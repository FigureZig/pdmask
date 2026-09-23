(* evidence.ml — evidence for and against PII.

   For each candidate span we collect signals (evidence) that argue for or
   against it being personal data. Each evidence has a code and a weight.
   decision.ml sums the weights and compares against a threshold.

   Evidence codes and default weights (spec 5.3, plus the eponym/possessive
   split of the note in docs/req_from_alfa):
   For:
     E_CHECKSUM  +45   checksum matched (Luhn, INN)
     E_KW_NEAR   +40   keyword *of this type* within 5 content tokens
     E_COOCCUR   +35   another confirmed PII type in the same sentence
     E_WHOLE     +35   span covers >=90% of a short payload (<64 code points)
     E_POSSESS   +35   a word of ownership before the name: паспорт Пушкина
     E_ROLE      +30   role word nearby (client, applicant, holder)
     E_FORM      +20   characteristic form (3-part FIO, +7 phone, flat number)
     E_DOCCTX    +15   document context (form, application, contract)
     E_CAPS      +5    word starts with a capital
   Against:
     E_ORGADDR   -70   address matches a bank office
     E_PUBLIC_FULL -60 a full name of a public person matched
     E_EPONYM    -55   the name names a thing, not an owner: улица Пушкина
     E_STOPCTX   -45   stop context nearby (poet, writer, monument)
     E_TITLE     -30   span inside quotes
     E_PUBLIC_SURN -20 only the surname of a public person matched

   Why E_PUBLIC is split in two (note, addition to M2/M4): a list of public
   persons does not scale, and the same surname is both "поэт Александр
   Пушкин" and "клиент Алексей Пушкин". A full-name match is strong evidence
   against; a bare surname match is weak, because the surname belongs to tens
   of thousands of ordinary people too.

   Why E_EPONYM and E_POSSESS exist: what decides is the role the name plays
   in the sentence — is it the owner of the thing, or its name?
     улица Пушкина    the name names the street   -> not PII
     паспорт Пушкина  the name owns the passport  -> PII
   The head word before the name tells which, and the two dictionaries
   heads_eponym.txt and heads_possess.txt hold those head words. This is an
   approximation of the real signal, which is the grammatical case; storing
   grammemes in the dictionary is the proper fix and is not done yet. *)

type code =
  | E_CHECKSUM
  | E_KW_NEAR
  | E_COOCCUR
  | E_WHOLE
  | E_POSSESS
  | E_ROLE
  | E_FORM
  | E_DOCCTX
  | E_CAPS
  | E_ORGADDR
  | E_PUBLIC_FULL
  | E_EPONYM
  | E_STOPCTX
  | E_TITLE
  | E_PUBLIC_SURN

let code_name (c : code) : string =
  match c with
  | E_CHECKSUM -> "E_CHECKSUM"
  | E_KW_NEAR -> "E_KW_NEAR"
  | E_COOCCUR -> "E_COOCCUR"
  | E_WHOLE -> "E_WHOLE"
  | E_POSSESS -> "E_POSSESS"
  | E_ROLE -> "E_ROLE"
  | E_FORM -> "E_FORM"
  | E_DOCCTX -> "E_DOCCTX"
  | E_CAPS -> "E_CAPS"
  | E_ORGADDR -> "E_ORGADDR"
  | E_PUBLIC_FULL -> "E_PUBLIC_FULL"
  | E_EPONYM -> "E_EPONYM"
  | E_STOPCTX -> "E_STOPCTX"
  | E_TITLE -> "E_TITLE"
  | E_PUBLIC_SURN -> "E_PUBLIC_SURN"

let weight (c : code) : int =
  match c with
  | E_CHECKSUM -> 45
  | E_KW_NEAR -> 40
  | E_COOCCUR -> 35
  | E_WHOLE -> 35
  | E_POSSESS -> 35
  | E_ROLE -> 30
  | E_FORM -> 20
  | E_DOCCTX -> 15
  | E_CAPS -> 5
  | E_ORGADDR -> -70
  | E_PUBLIC_FULL -> -60
  | E_EPONYM -> -55
  | E_STOPCTX -> -45
  | E_TITLE -> -30
  | E_PUBLIC_SURN -> -20

(* A piece of evidence attached to a span. *)
type evidence =
  { code : code;
    at : int (* token index where the evidence was found *)
  }

(* Context passed to the evidence collector. *)
type ctx =
  { bank_index : Textindex.t;
    public_forms : Dict.t;
    payload : string;
    payload_cp : int; (* length in code points, for E_WHOLE *)
    toks : Lexer.toks
  }

(* --- token helpers --- *)

(* Index of the token containing byte offset off. The token starts ascend and
   the tokens tile the input, so this is a binary search; a linear scan per
   candidate would make evidence collection quadratic on long texts. *)
let token_at (t : Lexer.toks) (off : int) : int =
  if off < 0 || t.Lexer.n = 0 || t.Lexer.nidx = 0 then
    -1
  else
    let b = off lsr Lexer.blk_shift in
    let b =
      if b >= t.Lexer.nidx then
        t.Lexer.nidx - 1
      else
        b
    in
    let i = ref (Array.unsafe_get t.Lexer.idx b) in
    while !i + 1 < t.Lexer.n && Array.unsafe_get t.Lexer.start (!i + 1) <= off do
      incr i
    done;
    !i

(* Token index range [lo, hi] covered by the span. *)
let span_tokens (ctx : ctx) (s : Spans.span) : int * int =
  let lo = token_at ctx.toks s.Spans.start in
  let hi = token_at ctx.toks (Spans.end_ s - 1) in
  (lo, hi)

(* Диапазон токенов спана считается ОДИН раз в collect и передаётся дальше.
   Раньше каждый помощник звал span_tokens сам — то есть два бинарных поиска по
   массиву на семьдесят тысяч токенов, и так по пять-восемь раз на одного
   кандидата, для одного и того же спана. Поиск сам по себе логарифмический, но
   каждый шаг — промах кэша по t.start, и это была самая дорогая «проходка» в
   сборе доказательств. *)

(* Does any token of the span carry the flag? *)
let span_has_flag (ctx : ctx) (lo : int) (hi : int) (flag : int) : bool =
  let rec go i = i <= hi && (ctx.toks.flags.(i) land flag <> 0 || go (i + 1)) in
  lo >= 0 && go lo

(* Есть ли в спане цифры? *)
let span_has_digits (ctx : ctx) (lo : int) (hi : int) : bool =
  let rec go i = i <= hi && (Rules.is_digits ctx.toks i || go (i + 1)) in
  lo >= 0 && go lo

(* Number of word tokens in the span. *)
let span_words (ctx : ctx) (lo : int) (hi : int) : int =
  let n = ref 0 in
  if lo >= 0 then
    for i = lo to hi do
      if Rules.is_word ctx.toks i then incr n
    done;
  !n

(* Is there a token carrying the flag within `window` content tokens of the
   span, outside the span itself? A keyword inside the span is part of the
   value, not context around it: "адрес отделения банка" must not collect the
   address keyword's own weight, and a role word swallowed by a FIO span must
   not vouch for that span. *)
let near_span (ctx : ctx) (lo : int) (hi : int) (flag : int) (window : int) : bool =
  flag <> 0
  && lo >= 0
  && (Rules.find_kw_dir ctx.toks (lo - 1) (-1) window flag >= 0
     || Rules.find_kw_dir ctx.toks (hi + 1) 1 window flag >= 0
     )

(* ИЛИ флагов токенов вокруг спана — сразу для двух окон, за один проход.

   Раньше near_span звался по разу на флаг: роль, стоп-контекст, контекст
   документа, ключевое слово типа — и каждый раз заново обходил то же самое
   окно вокруг того же спана. Окна при этом почти всегда 5 и 8, то есть один
   обход до восьми содержательных токенов покрывает все четыре вопроса.
   Проверка превращается в проверку бита.

   Два результата возвращаются одним числом: флаги занимают биты 0..30, а int
   в OCaml 63-битный. Кортеж здесь стоил бы блока на каждый вызов — flambda в
   сборке выключена, и межфункционального анбоксинга ждать неоткуда. Локальные
   ссылки при этом свободны: их ocamlopt разворачивает в переменные сам. *)
let env_bits = 31

let scan_env (t : Lexer.toks) (from : int) (step : int) (w1 : int) (w2 : int) : int =
  let a1 = ref 0
  and a2 = ref 0 in
  let seen = ref 0
  and j = ref from
  and go = ref true in
  while !go do
    if !j < 0 || !j >= t.n then
      go := false
    else (
      (* is_content развёрнут на месте: это три невстроенных вызова на каждый
         прочитанный токен, а читаются они десятками на кандидата. *)
      ( match Array.unsafe_get t.Lexer.kind !j with
      | Lexer.WORD_CYR | Lexer.WORD_LAT | Lexer.DIGITS | Lexer.EMAIL -> incr seen
      | _ -> ()
      );
      if !seen > w2 then
        go := false
      else
        let f = t.flags.(!j) in
        if !seen <= w1 then a1 := !a1 lor f;
        a2 := !a2 lor f;
        j := !j + step
    )
  done;
  !a1 lor (!a2 lsl env_bits)

(* Find a head word (eponym or ownership) in the two content tokens before the
   span. "паспорт гражданина Пушкина" still reaches "паспорт". *)
let find_head_before (ctx : ctx) (tok_idx : int) (flag : int) : int =
  let rec walk j seen =
    if j < 0 then
      -1
    else
      let seen =
        if Rules.is_content ctx.toks j then
          seen + 1
        else
          seen
      in
      if seen > 2 then
        -1
      else if ctx.toks.flags.(j) land flag <> 0 then
        j
      else
        walk (j - 1) seen
  in
  walk (tok_idx - 1) 0

(* --- text helpers --- *)

(* Свёрнутый текст спана — один проход и одна строка. Прежний вариант резал
   подстроку и сворачивал её отдельно: два прохода и две строки на вызов. *)
let span_text (ctx : ctx) (s : Spans.span) : string =
  let buf = ctx.payload
  and off = s.Spans.start
  and len = s.Spans.len in
  let out = Bytes.create len in
  let i = ref 0 in
  while !i < len do
    let b = String.unsafe_get buf (off + !i) in
    let c = Char.code b in
    if (c = 0xD0 || c = 0xD1) && !i + 1 < len then (
      let p = Classes.fold_pair b (String.unsafe_get buf (off + !i + 1)) in
      Bytes.unsafe_set out !i (Char.unsafe_chr (p lsr 8));
      Bytes.unsafe_set out (!i + 1) (Char.unsafe_chr (p land 0xFF));
      i := !i + 2
    ) else (
      Bytes.unsafe_set out !i (Classes.fold_byte b);
      incr i
    )
  done;
  Bytes.unsafe_to_string out

(* Number of code points in a byte range. *)
let code_points (buf : string) (off : int) (len : int) : int =
  let n = ref 0 in
  for i = off to off + len - 1 do
    if Classes.is_codepoint_start buf.[i] then incr n
  done;
  !n

(* То же, но счёт обрывается, как только стало ясно, что точки больше cap.

   Длина payload в кодовых точках нужна ровно для одного вопроса: короткий ли
   payload целиком (E_WHOLE, порог 64). Считать её полным проходом по телу
   запроса — это лишний проход по 400 КБ на каждый запрос ради сравнения с
   числом 64. Точное значение нужно только когда точек меньше порога, а там
   счёт и так доходит до конца. *)
let code_points_capped (buf : string) (cap : int) : int =
  let n = ref 0
  and i = ref 0 in
  let len = String.length buf in
  while !i < len && !n <= cap do
    if Classes.is_codepoint_start buf.[!i] then incr n;
    incr i
  done;
  !n

(* Входит ли needle в haystack как подстрока?

   Сравнение идёт по байтам на месте. Прежний вариант резал String.sub на
   КАЖДОЙ позиции — то есть аллоцировал новую строку на каждый сдвиг окна.
   На справочнике из тридцати отделений это давало около пятнадцати тысяч слов
   на один адресный кандидат, и сбор доказательств съедал 68% времени всего
   конвейера, не делая почти никакой полезной работы. *)
let contains (haystack : string) (needle : string) : bool =
  let lh = String.length haystack
  and ln = String.length needle in
  if ln = 0 then
    true
  else if ln > lh then
    false
  else
    let first = needle.[0] in
    let last = lh - ln in
    let i = ref 0
    and found = ref false in
    while (not !found) && !i <= last do
      if haystack.[!i] = first then (
        let k = ref 1 in
        while !k < ln && haystack.[!i + !k] = needle.[!k] do
          incr k
        done;
        if !k = ln then found := true
      );
      incr i
    done;
    !found

(* Does the span cover a bank office address? The span rarely lines up with
   the reference entry exactly — the address rule anchors on the city name and
   the reference starts at "г." — so either one containing the other counts.

   Справочник проиндексирован один раз при загрузке (см. textindex.ml):
   Ахо–Корасик отвечает на "офис внутри спана", суффиксный автомат — на "спан
   внутри офиса". Запрос линеен по длине спана и не зависит от размера
   справочника, а наивная сверка была O(K · |спан| · |офис|) и съедала почти
   половину всего сбора доказательств. *)
let matches_bank_office (ctx : ctx) (s : Spans.span) : bool =
  Textindex.matches ctx.bank_index (Dictload.address_key_of ctx.payload s.Spans.start s.Spans.len)

(* Does the span carry a flat or office number? A bank office does not have
   one, which is the void rule of spec 5.4; the same marker is what makes a
   residential address recognisable, so it is also E_FORM. *)
let has_flat_number (folded : string) : bool =
  contains folded "кв." || contains folded "кварт." || contains folded "оф."

(* Does the span text match a public person's full form? Поиск идёт по
   байтам спана на месте: Dict сворачивает вход в хеширующем цикле, поэтому
   ни подстроки, ни свёрнутой копии не возникает. *)
let match_public_full (ctx : ctx) (s : Spans.span) : bool =
  Dict.find ctx.public_forms ctx.payload s.Spans.start s.Spans.len <> 0

(* Does the span carry a public person's surname? The surnames are in the
   dictionary under Flag.public_person, declined forms included. *)
let match_public_surn (ctx : ctx) (lo : int) (hi : int) : bool =
  span_has_flag ctx lo hi Dict.Flag.public_person

(* Начинается ли спан с начала предложения?

   Заглавная буква в начале предложения не значит ничего: там с большой буквы
   стоит любое слово. Когда словарь имён расширили до склоняемых форм, ровно
   на этом посыпались негативные кейсы: «Машина готова?», «Какой график
   работы» — «машина» и «какой» есть в словаре как формы имён, и одинокое
   словарное слово с заглавной набирало 45 + 5 = ровно порог.

   Границы предложений лексер уже собрал. Спан начинает предложение, если
   между ближайшей границей слева и его первым токеном нет ни одного
   содержательного токена. *)
let starts_sentence (ctx : ctx) (lo : int) (start : int) : bool =
  if lo < 0 then
    false
  else
    let t = ctx.toks in
    (* ближайшая граница предложения строго левее начала спана *)
    let b = t.Lexer.sent in
    let a = ref 0
    and z = ref t.Lexer.nsent in
    while !a < !z do
      let m = (!a + !z) lsr 1 in
      if Array.unsafe_get b m < start then
        a := m + 1
      else
        z := m
    done;
    let prev =
      if !a = 0 then
        -1
      else
        Array.unsafe_get b (!a - 1)
    in
    (* нет содержательных токенов между границей и спаном *)
    let j = ref (lo - 1)
    and clean = ref true in
    while !clean && !j >= 0 && t.Lexer.start.(!j) > prev do
      ( match Array.unsafe_get t.Lexer.kind !j with
      | Lexer.WORD_CYR | Lexer.WORD_LAT | Lexer.DIGITS | Lexer.EMAIL -> clean := false
      | _ -> ()
      );
      decr j
    done;
    !clean

(* Does the span start with a capital letter? Only ever evidence, never a
   condition — invariant 10. *)
let starts_capital (payload : string) (s : Spans.span) : bool =
  if s.Spans.len = 0 then
    false
  else
    let c = Char.code payload.[s.Spans.start] in
    (c >= 0x41 && c <= 0x5A) (* A-Z *)
    || c = 0xD0
       && s.Spans.len >= 2
       &&
       let c2 = Char.code payload.[s.Spans.start + 1] in
       (c2 >= 0x90 && c2 <= 0x9F) || (c2 >= 0xA0 && c2 <= 0xAF) || c2 = 0x81

(* Is the span inside quotes? A quoted span is a title — роман «Евгений
   Онегин», кафе "Пушкин" — and a title is not personal data. Looks for an
   opening quote to the left and a closing one to the right, on the same line.

   The search is bounded: a title is a handful of words, and scanning to the
   start of the text for a quote that is not there costs a full pass per
   candidate, which is a quadratic over a long payload. *)
let quote_window = 160

(* Четыре внутренних замыкания — is_open, is_close, left, right — стоили по
   блоку каждое на каждого кандидата: двадцать слов на кандидата и косвенный
   вызов на каждый прочитанный байт. Оба поиска развёрнуты в циклы. *)
(* Есть ли хоть одна кавычка в [lo, hi]? Двоичный поиск по позициям, которые
   лексер собрал своим проходом. Кавычек в обычном тексте единицы, поэтому у
   подавляющего большинства кандидатов ответ «нет» — и побайтовый поиск
   открывающей кавычки, сто шестьдесят байт в каждую сторону, не запускается
   вовсе. *)
let quote_in (t : Lexer.toks) (lo : int) (hi : int) : bool =
  let q = t.Lexer.quotes in
  let a = ref 0
  and b = ref t.Lexer.nquotes in
  while !a < !b do
    let m = (!a + !b) lsr 1 in
    if Array.unsafe_get q m < lo then
      a := m + 1
    else
      b := m
  done;
  !a < t.Lexer.nquotes && Array.unsafe_get q !a <= hi

let inside_quotes (ctx : ctx) (s : Spans.span) : bool =
  let buf = ctx.payload in
  let n = String.length buf in
  (* Открывающая кавычка должна стоять вплотную слева, а закрывающая вплотную
     справа — между ними и спаном допустимы только пробелы.

     Раньше обе искались в пределах ста шестидесяти байт через любой текст.
     В обычной прозе это работало, но на теле-транскрипте чата, где ВСЁ лежит
     внутри строк JSON, кавычки находились всегда: каждое значение ПДН
     получало E_TITLE со штрафом -30 и уходило под порог. Email при базе 55
     давал 25, телефон 20. Это и был самый крупный провал на pii-bench:
     шестьдесят два кейса домена с нулевым recall.

     Заголовок — это когда закавычен сам спан: «Евгений Онегин», кафе
     "Пушкин". Кусок посреди длинной закавыченной строки заголовком не
     является. *)
  let i = ref (s.Spans.start - 1) in
  while !i >= 0 && (String.unsafe_get buf !i = ' ' || String.unsafe_get buf !i = '\t') do
    decr i
  done;
  let opened =
    !i >= 0
    &&
    let c = String.unsafe_get buf !i in
    c = '"' || (c = '\xab' && !i > 0 && String.unsafe_get buf (!i - 1) = '\xc2')
  in
  opened
  &&
  let j = ref (Spans.end_ s) in
  while !j < n && (String.unsafe_get buf !j = ' ' || String.unsafe_get buf !j = '\t') do
    incr j
  done;
  !j < n
  &&
  let c = String.unsafe_get buf !j in
  (* Закрывающая «ёлочка» — это ДВА байта, 0xc2 0xbb, и слева от спана мы
     упираемся в первый из них. Проверка только второго байта означала, что
     «Пушкин» в кавычках не опознавался как название: скан останавливался на
     0xc2 и решал, что кавычки нет. Открывающая сторона работала случайно —
     там мы приходим на второй байт. *)
  c = '"'
  || (c = '\xc2' && !j + 1 < n && String.unsafe_get buf (!j + 1) = '\xbb')
  || (c = '\xbb' && !j > 0 && String.unsafe_get buf (!j - 1) = '\xc2')

(* Is the span immediately before an opening quote? "Роман «Евгений Онегин»"
   — the word "Роман" (a genre, not a name) sits right before the quote. *)
let before_quote (ctx : ctx) (s : Spans.span) : bool =
  let buf = ctx.payload in
  let n = String.length buf in
  let e = Spans.end_ s in
  let rec skip i =
    if i >= n then
      false
    else
      match buf.[i] with
      | ' ' | '\t' -> skip (i + 1)
      | '"' -> true
      | c when c = '\xc2' && i + 1 < n && buf.[i + 1] = '\xab' -> true
      | _ -> false
  in
  skip e

(* --- per-type signals --- *)

(* The keyword flag that confirms this type. E_KW_NEAR means the keyword *of
   the type*, not any keyword at all: without that, a FIO next to the word
   "паспорт" would collect the passport's evidence. Types with no keyword of
   their own (FIO, email, dates are covered by their own rules) get none. *)
(* Типы, которые описывают человека словами, а не жёсткой формой. Только им
   имеет смысл стоп-контекст публичной персоны. *)
let person_like (ty : Spans.ty) : bool =
  match ty with
  | Spans.Fio | Spans.Birth_place | Spans.Birth_date | Spans.Citizenship | Spans.Card_holder -> true
  | _ -> false

let kw_flag_of_ty (ty : Spans.ty) : int =
  match ty with
  | Spans.Fio | Spans.Email -> 0
  | Spans.Birth_date | Spans.Birth_place -> Dict.Flag.kw_birth
  | Spans.Issue_date -> Dict.Flag.kw_issue
  | Spans.Passport -> Dict.Flag.kw_passport
  | Spans.Driver_license -> Dict.Flag.kw_dl
  | Spans.Dept_code -> Dict.Flag.kw_dept
  | Spans.Address -> Dict.Flag.kw_addr lor Dict.Flag.addr_marker
  | Spans.Phone -> Dict.Flag.kw_phone
  | Spans.Inn -> Dict.Flag.kw_inn
  | Spans.Card -> Dict.Flag.kw_card
  | Spans.Cvv -> Dict.Flag.kw_cvv lor Dict.Flag.kw_cvv_weak
  | Spans.Pin -> Dict.Flag.kw_pin
  | Spans.Card_holder -> Dict.Flag.kw_holder
  | Spans.Citizenship -> Dict.Flag.kw_citizen
  (* Орган выдачи подтверждается не словом "отдел", а контекстом выдачи
     документа. Иначе "адрес отделения банка" — канонический пример ТЗ того,
     что маскировать нельзя — сам себе доказательство: "отделения" это
     kw_org. Признак органа — "выдан" или "паспорт" рядом. *)
  | Spans.Issuer -> Dict.Flag.kw_issue lor Dict.Flag.kw_passport
  | Spans.Snils | Spans.Oms | Spans.Foreign_passport -> Dict.Flag.kw_doc lor Dict.Flag.kw_issue

(* Is the form of the span characteristic of its type?
   - FIO: three parts, or a patronymic among them.
   - Phone: eleven digits opening with +7, 7 or 8 (ITU-T E.164).
   - Address: a flat or office number.
   Other types are recognised by shape already, so their rule is the form. *)
(* Слова, флаги и наличие цифр в спане — за один обход. По отдельности это
   были три прохода по одним и тем же токенам одного и того же спана.
   Упаковано в int: флаги занимают биты 0..30, дальше счётчик слов, потом бит
   цифр. *)
let span_scan (ctx : ctx) (lo : int) (hi : int) : int =
  if lo < 0 then
    0
  else
    let fl = ref 0
    and words = ref 0
    and digits = ref 0 in
    let t = ctx.toks in
    for i = lo to hi do
      fl := !fl lor Array.unsafe_get t.Lexer.flags i;
      match Array.unsafe_get t.Lexer.kind i with
      | Lexer.WORD_CYR | Lexer.WORD_LAT -> incr words
      | Lexer.DIGITS -> digits := 1
      | _ -> ()
    done;
    !fl lor (!words lsl 31) lor (!digits lsl 55)

let scan_flags (v : int) : int = v land 0x7FFFFFFF

let scan_words (v : int) : int = (v lsr 31) land 0xFFFFFF

let scan_digits (v : int) : bool = (v lsr 55) land 1 <> 0

(* Есть ли в спане и личное имя, и фамилия (или отчество)?

   Характерная форма ФИО — это имя плюс фамилия, а не два слова из словаря
   подряд. Со склоняемыми формами OpenCorpora словарь имён стал большим, и
   пары обычных слов начали в него попадать целиком: «Масло лили», «Баланс
   какой-то». Требование разных ролей их отсекает, а «Виталию Крылову»
   (имя + фамилия) оставляет. *)
let has_name_and_surname (ctx : ctx) (lo : int) (hi : int) : bool =
  if lo < 0 then
    false
  else
    let t = ctx.toks in
    let acc = ref 0 in
    for i = lo to hi do
      acc := !acc lor Array.unsafe_get t.Lexer.flags i
    done;
    !acc land Dict.Flag.name <> 0 && !acc land (Dict.Flag.surn lor Dict.Flag.patr) <> 0

let has_form (ctx : ctx) (lo : int) (hi : int) (s : Spans.span) (folded : string) : bool =
  match s.Spans.ty with
  | Spans.Fio ->
      let v = span_scan ctx lo hi in
      scan_words v >= 3
      || scan_flags v land Dict.Flag.patr <> 0
      (* Имя плюс фамилия — характерная форма сама по себе. Раньше её не
         отличали от одинокого словарного слова: и «Виталию Крылову», и
         «Дону» из «Ростов-на-Дону» набирали ровно 45 + 5 = порог. Два
         словарных слова подряд — это уже форма, одно — ещё нет. *)
      || has_name_and_surname ctx lo hi
  | Spans.Phone ->
      let d = Digits.digits_of ctx.payload s.Spans.start s.Spans.len in
      (Array.length d = 11 && (d.(0) = 7 || d.(0) = 8))
      || (s.Spans.start > 0 && ctx.payload.[s.Spans.start - 1] = '+')
  | Spans.Address ->
      (* Характерная форма адреса — это не только номер квартиры, но и сама
         связка "город, улица, дом": населённый пункт плюс число плюс хотя бы
         ещё одно слово между ними. Без этого доказательства адрес в живой
         переписке ("Калуга, Гагарина 78") набирает 45 при пороге 50 и
         отбрасывается — а ключевого слова там нет, люди пишут "адрс" или
         вообще ничего. *)
      has_flat_number folded
      ||
      let v = span_scan ctx lo hi in
      scan_flags v land Dict.Flag.geo <> 0 && scan_words v >= 3 && scan_digits v
  | _ -> false

(* Does the checksum of the span hold? Only card and INN carry one. *)
let checksum_ok (ctx : ctx) (s : Spans.span) : bool =
  let d () = Digits.digits_of ctx.payload s.Spans.start s.Spans.len in
  match s.Spans.ty with
  | Spans.Card -> Digits.luhn_valid (d ())
  | Spans.Inn -> Digits.inn_valid (d ())
  | _ -> false

(* --- evidence collection --- *)

(* Collect the evidence for a candidate span. E_COOCCUR is not collected here:
   it needs the outcome for the other spans and is added by router.ml on a
   second pass. *)
(* Keyword window for E_KW_NEAR. Most types look within 5 content tokens; CVV
   needs more because the card code is often far from the word "CVC" ("CVC с
   обратной стороны карты для подтверждения платежа, это 641"). *)
let kw_window (ty : Spans.ty) : int =
  match ty with
  | Spans.Cvv -> 12
  (* Паспорт называют не вплотную к цифрам: «потерял паспорт, капец! Такие
     были числа красивые! 7823 782372» — слово отстоит на семь
     содержательных токенов. Форма 4-6 при этом достаточно жёсткая, чтобы
     позволить окну пошире. *)
  | Spans.Passport | Spans.Driver_license -> 10
  | _ -> 5

(* Накопитель доказательств — обычная функция, а не замыкание внутри collect:
   замыкание заводилось на каждого кандидата, а кандидатов на теле в 400 КБ
   шесть с половиной тысяч. *)
let push_ev (ev : evidence list ref) (c : code) (at : int) : unit = ev := {code = c; at} :: !ev

let collect (ctx : ctx) (s : Spans.span) : evidence list =
  let ev = ref [] in
  let add c at = push_ev ev c at in
  (* Один бинарный поиск на границу спана — и всё, дальше только индексы. *)
  let i = token_at ctx.toks s.Spans.start in
  let lo = i in
  let hi = token_at ctx.toks (Spans.end_ s - 1) in
  (* Для фразовых типов ключевое слово — это якорь самой фразы, и оно лежит
     ВНУТРИ спана: "выдан ОУФМС ...", "место рождения г. Казань",
     "гражданство Российская Федерация". Искать его только снаружи бессмысленно
     — такой спан никогда не наберёт E_KW_NEAR и не перейдёт порог. Для
     значимых типов (карта, паспорт, телефон) наоборот: ключевое слово это
     контекст вокруг значения, и слово внутри спана не должно оплачивать само
     себя, иначе "адрес отделения банка" сам себе доказательство. *)
  let anchored_phrase =
    match s.Spans.ty with
    | Spans.Issuer | Spans.Citizenship | Spans.Birth_place -> true
    | _ -> false
  in
  (* Окружение спана снимается один раз на кандидата; near становится
     проверкой бита. Окно 12 (CVV) остаётся на старом пути — тип редкий, а
     фразовые типы ищут ключевое слово внутри спана и окружения не смотрят. *)
  let env =
    if anchored_phrase || lo < 0 then
      0
    else
      scan_env ctx.toks (lo - 1) (-1) 5 8 lor scan_env ctx.toks (hi + 1) 1 5 8
  in
  let env5 = env land ((1 lsl env_bits) - 1)
  and env8 = env lsr env_bits in
  let near flag window =
    if anchored_phrase then
      flag <> 0 && Rules.find_kw ctx.toks i window flag >= 0
    else if window = 5 then
      env5 land flag <> 0
    else if window = 8 then
      env8 land flag <> 0
    else
      near_span ctx lo hi flag window
  in
  (* Лениво: полное имя публичной персоны нужно только для ФИО и для E_WHOLE
     на коротком payload. Для карты, телефона и адреса это была пара аллокаций
     плюс сто с лишним сравнений строк впустую — на каждого кандидата. *)
  (* Свёрнутый текст спана нужен только адресу — и нужен там трижды: форме,
     сверке со справочником отделений и номеру квартиры. Раньше каждая из трёх
     считала его заново, то есть резала подстроку и сворачивала её в новую
     строку. Считается один раз и только для адреса. *)
  let folded =
    if s.Spans.ty = Spans.Address then
      span_text ctx s
    else
      ""
  in
  (* Полное имя публичной персоны нужно ровно в двух местах: для ФИО и для
     E_WHOLE на коротком payload. Раньше это была lazy-ячейка, то есть блок на
     каждого кандидата ради двух возможных обращений; то же условие считается
     заранее и даёт тот же ответ без ячейки. *)
  let public_full =
    ( match s.Spans.ty with
      | Spans.Fio -> true
      | _ -> ctx.payload_cp < 64
      )
    && match_public_full ctx s
  in
  if i >= 0 then (
    (* Заглавная не засчитывается только однословному спану в начале
       предложения: там с большой буквы стоит любое слово, а настоящее ФИО
       почти всегда длиннее одного токена. «Машина готова?» отсекается,
       «Иванов Иван Иванович, паспорт...» — нет. *)
    if starts_capital ctx.payload s && scan_words (span_scan ctx lo hi) >= 2 then add E_CAPS i;
    if near (kw_flag_of_ty s.Spans.ty) (kw_window s.Spans.ty) then add E_KW_NEAR i;
    if near Dict.Flag.role 5 then add E_ROLE i;
    (* Стоп-контекст («поэт», «писатель», «написал») подавляет ЧЕЛОВЕКА, а не
       идентификатор. Он был безусловным, и «написал им на support@...»
       гасило email штрафом -45: при базе 55 оставалось 10. У email, телефона,
       карты, паспорта форма жёсткая, и литературный контекст к ним
       отношения не имеет. *)
    if person_like s.Spans.ty && near Dict.Flag.stop_ctx 5 then add E_STOPCTX i;
    (* A birth place next to a stop context is a public person's birthplace,
       not personal data: "Поэт Пушкин родился в Москве". The stop word can
       be far — across the whole name — so the window is wider. *)
    if s.Spans.ty = Spans.Birth_place && near Dict.Flag.stop_ctx 20 then add E_STOPCTX i;
    if near Dict.Flag.doc_ctx 8 then add E_DOCCTX i;
    if has_form ctx lo hi s folded then add E_FORM i;
    (* Заголовок — это слова: «Евгений Онегин», кафе "Пушкин". Номер телефона,
       карта или email в кавычках заголовком не становятся, а в JSON-теле
       значение закавычено всегда: "content": "89167788990" — и телефон при
       базе 30 получал -30 и уходил под порог. Штраф выдаётся только типам,
       которые описывают человека словами. *)
    if person_like s.Spans.ty then (
      if inside_quotes ctx s then add E_TITLE i;
      if before_quote ctx s then add E_TITLE i
    );
    (* Who the name belongs to: a public person, the thing it names, or the
       owner of the document next to it. Only names carry these. *)
    if s.Spans.ty = Spans.Fio then (
      if public_full then
        add E_PUBLIC_FULL i
      else if match_public_surn ctx lo hi then
        add E_PUBLIC_SURN i;
      let eponym = find_head_before ctx i Dict.Flag.eponym_head in
      if eponym >= 0 then add E_EPONYM eponym;
      let possess = find_head_before ctx i Dict.Flag.possess_head in
      if possess >= 0 && eponym < 0 then add E_POSSESS possess
    );
    (* An address matching a bank office is not a client's address — unless it
       carries a flat number, which a bank office never has (spec 5.4). *)
    if s.Spans.ty = Spans.Address && matches_bank_office ctx s && not (has_flat_number folded) then
      add E_ORGADDR i
  );
  (* The payload can be a single value with no context at all; the dataset
     contains such elements. Length is counted in code points: in bytes every
     Cyrillic character counts twice and no Russian text is ever "short". The
     payload's own length is measured once per request, not once per
     candidate — a long text has thousands of them. *)
  ( if ctx.payload_cp < 64 then
      let slen = code_points ctx.payload s.Spans.start s.Spans.len in
      if slen * 10 >= ctx.payload_cp * 9 && not public_full then add E_WHOLE 0
  );
  if checksum_ok ctx s then add E_CHECKSUM 0;
  List.rev !ev
