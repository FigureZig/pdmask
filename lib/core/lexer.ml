(* lexer.ml — pass 1: bytes to tokens.

   Design (spec 4.3):
   - Parallel int arrays (no boxing, no GC pressure).
   - The structure is reused between requests: it grows but is not recreated.
   - Yield control every 64 KiB.
   - Word: hash computed while reading, dictionary lookup, flags.
   - Digit group: count.
   - '@': expand left and right into an EMAIL token.
   - Everything else: by the class table.

   Token kinds:
   - WORD_CYR  Cyrillic word
   - WORD_LAT  Latin word
   - DIGITS    digit group
   - EMAIL     email address
   - SEP       separator (- / . ,)
   - PUNCT     other punctuation
   - SPACE     whitespace *)

type kind =
  | WORD_CYR
  | WORD_LAT
  | DIGITS
  | EMAIL
  | SEP
  | PUNCT
  | SPACE

type toks =
  { mutable n : int;
    mutable start : int array;
    mutable len : int array;
    mutable kind : kind array;
    mutable flags : int array; (* dictionary flags for words *)
    mutable aux : int array; (* for DIGITS: number of digits *)
    (* Грубый индекс "байт -> токен": в блоке idx.(b) лежит номер последнего
       токена, начинающегося не правее байта b * 2^blk_shift. Поиск токена по
       смещению превращается в чтение по индексу плюс несколько шагов вперёд
       подряд вместо семнадцати случайных прыжков двоичного поиска по массиву
       на сто тридцать тысяч элементов. Доказательства спрашивают об этом
       дважды на каждого кандидата. *)
    mutable idx : int array;
    mutable nidx : int;
    (* Номера токенов, у которых есть хоть один словарный флаг. Правила,
       которые цепляются за словарь — адрес, место рождения, гражданство,
       орган выдачи, — интересуются только ими, а их в живом тексте около
       тринадцати процентов от всех токенов. Перебирать ради них весь массив
       значит делать семь восьмых работы впустую. *)
    mutable flagged : int array;
    mutable nflagged : int;
    (* Позиции концов предложений, по возрастанию. Лексер и так читает каждый
       байт тела; отдельный проход ради этих позиций — это второе чтение тех
       же 400 КБ, и стоило оно 0.8 мс на запрос. *)
    mutable sent : int array;
    mutable nsent : int;
    (* Позиции кавычек, по возрастанию: для « и » это позиция второго байта,
       чтобы совпадало с тем, как их узнаёт проверка «спан в кавычках». *)
    mutable quotes : int array;
    mutable nquotes : int
  }

let blk_shift = 5

let create () : toks =
  { n = 0;
    start = Array.make 256 0;
    len = Array.make 256 0;
    kind = Array.make 256 WORD_CYR;
    flags = Array.make 256 0;
    aux = Array.make 256 0;
    idx = Array.make 256 (-1);
    nidx = 0;
    flagged = Array.make 256 0;
    nflagged = 0;
    sent = Array.make 256 0;
    nsent = 0;
    quotes = Array.make 64 0;
    nquotes = 0
  }

let reset (t : toks) : unit =
  t.n <- 0;
  t.nsent <- 0;
  t.nquotes <- 0

(* Рост массивов через Array.blit, а не Array.init: init зовёт замыкание на
   каждый элемент, а элементов тут сотни тысяч. *)
let ensure (t : toks) (need : int) : unit =
  if need > Array.length t.start then (
    let cap = max (Array.length t.start * 2) need in
    let gi (old : int array) =
      let a = Array.make cap 0 in
      Array.blit old 0 a 0 t.n;
      a
    in
    t.start <- gi t.start;
    t.len <- gi t.len;
    t.flags <- gi t.flags;
    t.aux <- gi t.aux;
    let k = Array.make cap WORD_CYR in
    Array.blit t.kind 0 k 0 t.n;
    t.kind <- k
  )

let mark_quote (t : toks) (pos : int) : unit =
  if t.nquotes = Array.length t.quotes then (
    let bigger = Array.make (2 * t.nquotes) 0 in
    Array.blit t.quotes 0 bigger 0 t.nquotes;
    t.quotes <- bigger
  );
  Array.unsafe_set t.quotes t.nquotes pos;
  t.nquotes <- t.nquotes + 1

let mark_sentence (t : toks) (pos : int) : unit =
  if t.nsent = Array.length t.sent then (
    let bigger = Array.make (2 * t.nsent) 0 in
    Array.blit t.sent 0 bigger 0 t.nsent;
    t.sent <- bigger
  );
  Array.unsafe_set t.sent t.nsent pos;
  t.nsent <- t.nsent + 1

let push (t : toks) (start : int) (len : int) (kind : kind) (flags : int) (aux : int) : unit =
  ensure t (t.n + 1);
  t.start.(t.n) <- start;
  t.len.(t.n) <- len;
  t.kind.(t.n) <- kind;
  t.flags.(t.n) <- flags;
  t.aux.(t.n) <- aux;
  t.n <- t.n + 1

(* Является ли символ в позиции i буквой? Проверяется именно символ, а не
   байт: продолжающие байты 0x80..0xBF помечены в таблице как CYR_LO, но точно
   такие же байты стоят внутри тире и кавычек-ёлочек. Слово начинается только
   с латинской буквы или с ведущего байта кириллицы. *)
let is_letter_at (buf : string) (i : int) : bool =
  let b = buf.[i] in
  Classes.class_of b = Classes.LAT || Classes.is_cyr_lead b

(* Начинается ли в позиции i кириллическая буква? *)
let is_cyr_at (buf : string) (i : int) : bool = Classes.is_cyr_lead buf.[i]

(* Читает слово, начиная с off, и сразу кладёт токен. Возвращает новую позицию.

   Хеш словаря считается тем же проходом, что ищет конец слова. Раньше байты
   слова обходились трижды — сканирование, хеш, побайтовое сравнение с
   ключом, — и хеш был самой дорогой частью лексера: 18.6% стадии. Тройка
   (конец, кириллица ли, флаги) на выходе стоила блока на каждое слово, потому
   токен кладётся прямо здесь.

   Слово состоит только из латиницы (один байт на символ) и ведущих байтов
   кириллицы 0xD0/0xD1 (два байта) — других символов is_letter_at не
   пропускает, поэтому свёртка парами здесь та же, что в hash_folded. *)
let scan_word (t : toks) (dict : Dict.t) (buf : string) (off : int) (len : int) : int =
  let i = ref off in
  let is_cyr = ref false in
  let h = ref Dict.fnv_offset in
  (* Свёртка развёрнута прямо здесь. fold_byte и fold_pair — настоящие вызовы
     на каждый байт каждого слова, а слов в теле на 400 КБ двадцать шесть
     тысяч: без flambda это самая дорогая функция всего конвейера.

     Шагаем символами, а не байтами: иначе слово «съест» половину тире. *)
  let go = ref true in
  while !go && !i < len do
    let c = Char.code (String.unsafe_get buf !i) in
    if c = 0xD0 || c = 0xD1 then (
      is_cyr := true;
      if !i + 1 < len then (
        let c2 = Char.code (String.unsafe_get buf (!i + 1)) in
        let lead = ref c
        and cont = ref c2 in
        if c = 0xD0 then
          if c2 >= 0x90 && c2 <= 0x9F then
            cont := c2 + 0x20 (* А-П *)
          else if c2 >= 0xA0 && c2 <= 0xAF then (
            lead := 0xD1;
            cont := c2 - 0x20 (* Р-Я *)
          ) else if c2 = 0x81 then
            cont := 0xB5 (* Ё -> е, см. Classes.fold_pair *)
          else
            ()
        else if c = 0xD1 && c2 = 0x91 then (
          lead := 0xD0;
          cont := 0xB5 (* ё -> е *)
        );
        h := !h lxor !lead * Dict.fnv_prime;
        h := !h lxor !cont * Dict.fnv_prime;
        i := !i + 2
      ) else (
        (* оборванная на ведущем байте кириллица в самом конце тела: символа
           нет, и токен не имеет права вылезать за границу буфера *)
        h := !h lxor c * Dict.fnv_prime;
        incr i
      )
    ) else if Array.unsafe_get Classes.table c == Classes.LAT then (
      let fc =
        if c >= 0x41 && c <= 0x5A then
          c lor 0x20
        else
          c
      in
      h := !h lxor fc * Dict.fnv_prime;
      incr i
    ) else
      go := false
  done;
  let wlen = !i - off in
  let flags = Dict.find_hashed dict buf off wlen !h in
  push t off wlen
    ( if !is_cyr then
        WORD_CYR
      else
        WORD_LAT
    )
    flags 0;
  !i

(* Читает группу цифр и кладёт токен. Возвращает новую позицию: кортеж
   (конец, количество) стоил блока на каждый цифровой токен. *)
let scan_digits (t : toks) (buf : string) (off : int) (len : int) : int =
  let i = ref off in
  while
    !i < len
    && Array.unsafe_get Classes.table (Char.code (String.unsafe_get buf !i)) == Classes.DIGIT
  do
    incr i
  done;
  push t off (!i - off) DIGITS 0 (!i - off);
  !i

(* Scan an email: expand '@' left and right over word chars and separators.
   Returns (start, end) of the email token, or None. *)
(* Начало символа, которому принадлежит байт i: отступаем назад по
   продолжающим байтам. Нужно, чтобы границы email-токена совпадали с
   границами символов. *)
let char_start (buf : string) (i : int) : int =
  let j = ref i in
  while !j > 0 && not (Classes.is_codepoint_start buf.[!j]) do
    decr j
  done;
  !j

let scan_email (buf : string) (at : int) (len : int) : (int * int) option =
  (* expand left over word chars, digits, dots, dashes, plus *)
  let left = ref at in
  let continue_left () =
    if !left = 0 then
      false
    else
      let p = char_start buf (!left - 1) in
      is_letter_at buf p
      || Classes.class_of buf.[p] = Classes.DIGIT
      || buf.[p] = '.'
      || buf.[p] = '-'
      || buf.[p] = '_'
      || buf.[p] = '+'
  in
  (* шагаем символами: иначе граница токена встаёт посреди кириллической буквы
     и маска рвёт её пополам, а ответ перестаёт быть корректным UTF-8 *)
  while continue_left () do
    left := char_start buf (!left - 1)
  done;
  (* expand right over word chars, digits, dots, dashes, plus *)
  let right = ref (at + 1) in
  while
    !right < len
    && (is_letter_at buf !right
       || Classes.class_of buf.[!right] = Classes.DIGIT
       || buf.[!right] = '.'
       || buf.[!right] = '-'
       || buf.[!right] = '_'
       || buf.[!right] = '+'
       )
  do
    right := !right + Classes.char_len buf.[!right]
  done;
  if !right > len then right := len;
  (* require at least one char on each side of '@' *)
  if !left < at && !right > at + 1 then
    Some (!left, !right)
  else
    None

(* Lex buf into tokens. The token array is reused. *)
let build_index (t : toks) (buflen : int) : unit =
  if t.n > Array.length t.flagged then t.flagged <- Array.make (max 256 t.n) 0;
  let f = ref 0 in
  for i = 0 to t.n - 1 do
    if Array.unsafe_get t.flags i <> 0 then (
      Array.unsafe_set t.flagged !f i;
      incr f
    )
  done;
  t.nflagged <- !f;
  let nb = (buflen lsr blk_shift) + 2 in
  if nb > Array.length t.idx then t.idx <- Array.make (max (2 * Array.length t.idx) nb) (-1);
  t.nidx <- nb;
  let j = ref (-1) in
  for b = 0 to nb - 1 do
    let target = b lsl blk_shift in
    while !j + 1 < t.n && Array.unsafe_get t.start (!j + 1) <= target do
      incr j
    done;
    Array.unsafe_set t.idx b !j
  done

let lex (t : toks) (dict : Dict.t) (buf : string) : unit =
  reset t;
  let len = String.length buf in
  let i = ref 0 in
  let last_yield = ref 0 in
  while !i < len do
    let b = String.unsafe_get buf !i in
    (* класс читается прямо из таблицы: вызов class_of — это вызов на каждый
       байт тела запроса, а без flambda он не встраивается *)
    match Array.unsafe_get Classes.table (Char.code b) with
    | Classes.CYR_HI when not (Classes.is_cyr_lead b) ->
        (* ведущий байт какого-то другого многобайтового символа *)
        let w = min (Classes.char_len b) (len - !i) in
        push t !i w PUNCT 0 0;
        (* кавычки отмечаются по дороге: их единицы на всё тело, а проверка
           «спан в кавычках» иначе прочёсывает по сто шестьдесят байт в каждую
           сторону на каждого кандидата *)
        ( if b = '"' then
            mark_quote t !i
          else if b = '\xc2' && !i + 1 < len then
            let c2 = String.unsafe_get buf (!i + 1) in
            if c2 = '\xab' || c2 = '\xbb' then mark_quote t (!i + 1)
        );
        i := !i + w
    | Classes.CYR_LO ->
        (* одинокий продолжающий байт: вход битый, проглатываем по одному *)
        push t !i 1 PUNCT 0 0;
        incr i
    | Classes.LAT | Classes.CYR_HI -> i := scan_word t dict buf !i len
    | Classes.DIGIT -> i := scan_digits t buf !i len
    | Classes.AT -> (
        match scan_email buf !i len with
        | Some (s, e) ->
            push t s (e - s) EMAIL 0 0;
            i := e
        | None ->
            push t !i 1 PUNCT 0 0;
            incr i
      )
    | Classes.SEP ->
        push t !i 1 SEP 0 0;
        (* конец предложения отмечается здесь, по дороге: точек, восклицаний и
           переводов строки на порядки меньше, чем байтов *)
        if b = '.' && Classes.sentence_dot buf !i then mark_sentence t !i;
        incr i
    | Classes.PUNCT ->
        push t !i 1 PUNCT 0 0;
        if b = '!' || b = '?' then mark_sentence t !i;
        incr i
    | Classes.SPACE ->
        (* group consecutive spaces into one token *)
        let j = ref !i in
        while
          !j < len
          && Array.unsafe_get Classes.table (Char.code (String.unsafe_get buf !j)) == Classes.SPACE
        do
          if String.unsafe_get buf !j = '\n' then mark_sentence t !j;
          incr j
        done;
        push t !i (!j - !i) SPACE 0 0;
        i := !j
    | Classes.OTHER ->
        (* символ целиком: тире, кавычки-ёлочки, эмодзи. Токен обязан совпадать
           с границей символа, иначе спан разрежет его пополам *)
        let w = min (Classes.char_len b) (len - !i) in
        push t !i w PUNCT 0 0;
        (* кавычки отмечаются по дороге: их единицы на всё тело, а проверка
           «спан в кавычках» иначе прочёсывает по сто шестьдесят байт в каждую
           сторону на каждого кандидата *)
        ( if b = '"' then
            mark_quote t !i
          else if b = '\xc2' && !i + 1 < len then
            let c2 = String.unsafe_get buf (!i + 1) in
            if c2 = '\xab' || c2 = '\xbb' then mark_quote t (!i + 1)
        );
        i := !i + w;
        (* yield every 64 KiB *)
        if !i - !last_yield >= 65536 then (
          Eio.Fiber.yield ();
          last_yield := !i
        )
  done;
  build_index t len
