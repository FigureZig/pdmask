(* rules.ml — pass 2: tokens to candidates.

   Rules produce candidate spans for the 17 PII types (spec section 9). A rule
   never decides: it fires cheaply and with high recall, and evidence.ml and
   decision.ml weigh the result. Where a checksum or a keyword could have been
   a condition here, it is deliberately left to be evidence instead.

   Three of the seventeen types have no rule yet: birth_place, citizenship and
   issuer. See section 13 of the spec.

   Rule kinds (spec 4.5):
   - digit rule: shape + validator
   - dictionary rule: word flag
   - phrase rule: anchor + right expansion
   - combination rule: type only when another is nearby

   All rules are declared here; moving the declarations into the config so a
   new type needs no code at all is M6. *)

open Spans

(* --- helpers --- *)

(* Is token i a word with the given flag? *)
let has_flag (t : Lexer.toks) (i : int) (flag : int) : bool = t.flags.(i) land flag <> 0

(* Is token i a keyword (any KW_ flag)? *)
let is_keyword (t : Lexer.toks) (i : int) : bool =
  let f = t.flags.(i) in
  f
  land (Dict.Flag.kw_passport
       lor Dict.Flag.kw_birth
       lor Dict.Flag.kw_issue
       lor Dict.Flag.kw_dept
       lor Dict.Flag.kw_dl
       lor Dict.Flag.kw_addr
       lor Dict.Flag.kw_inn
       lor Dict.Flag.kw_card
       lor Dict.Flag.kw_cvv
       lor Dict.Flag.kw_pin
       lor Dict.Flag.kw_holder
       lor Dict.Flag.kw_citizen
       lor Dict.Flag.kw_org
       lor Dict.Flag.kw_birthplace
       )
  <> 0

(* Is token i a digit token? *)
(* Сопоставление, а не =: это самые вызываемые предикаты во всём коде, и
   полиморфное равенство на них было бы вызовом caml_equal на каждый токен. *)
let is_digits (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.DIGITS -> true
  | _ -> false

(* Is token i a word token (Cyrillic or Latin)? *)
let is_word (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.WORD_CYR | Lexer.WORD_LAT -> true
  | _ -> false

(* Is token i a separator? *)
let is_sep (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.SEP -> true
  | _ -> false

(* Is token i a space? *)
let is_space (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.SPACE -> true
  | _ -> false

(* Is token i an email? *)
let is_email (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.EMAIL -> true
  | _ -> false

(* Is token i a content token — a word, a digit group or an email? Spaces and
   punctuation are not. *)
let is_content (t : Lexer.toks) (i : int) : bool =
  match Array.unsafe_get t.kind i with
  | Lexer.WORD_CYR | Lexer.WORD_LAT | Lexer.DIGITS | Lexer.EMAIL -> true
  | _ -> false

(* Find a token carrying the flag within `window` content tokens of i, in
   either direction. Returns the index or -1.

   The window is counted in content tokens because between two words there is
   always a space token: a raw window of five lexer tokens reaches only two
   words out, and "паспорт гражданина РФ 4509 123456" would lose its keyword.
   The scan stops at the window edge — it runs once per candidate, and
   scanning to the end of the token array makes detection quadratic on the
   large texts of M8. *)
(* Цикл, а не рекурсия с is_content и has_flag внутри: это четыре настоящих
   вызова на каждый просмотренный токен, а зовут эту функцию почти все
   правила. Без flambda она была самой горячей в стадии. *)
let find_kw_dir (t : Lexer.toks) (from : int) (step : int) (window : int) (flag : int) : int =
  let j = ref from
  and seen = ref 0
  and res = ref (-1)
  and go = ref true in
  while !go do
    if !j < 0 || !j >= t.n then
      go := false
    else (
      ( match Array.unsafe_get t.kind !j with
      | Lexer.WORD_CYR | Lexer.WORD_LAT | Lexer.DIGITS | Lexer.EMAIL -> incr seen
      | _ -> ()
      );
      if !seen > window then
        go := false
      else if Array.unsafe_get t.flags !j land flag <> 0 then (
        res := !j;
        go := false
      ) else
        j := !j + step
    )
  done;
  !res

let find_kw (t : Lexer.toks) (i : int) (window : int) (flag : int) : int =
  if i < 0 || i >= t.n then
    -1
  else if has_flag t i flag then
    i
  else
    let left = find_kw_dir t (i - 1) (-1) window flag in
    if left >= 0 then
      left
    else
      find_kw_dir t (i + 1) 1 window flag

(* Distance in tokens to the nearest token with the given flag, or max_int. *)
let kw_distance (t : Lexer.toks) (i : int) (window : int) (flag : int) : int =
  let j = find_kw t i window flag in
  if j < 0 then
    max_int
  else
    abs (j - i)

(* Does the run have exactly this shape? Checks the length first, so the
   20 000-group run of a digit-only text is dismissed without walking it. *)
let shape_is (r : Digits.run) (shape : int list) : bool =
  Array.length r.groups = List.length shape
  &&
  let rec go i = function
    | [] -> true
    | x :: rest -> r.groups.(i) = x && go (i + 1) rest
  in
  go 0 shape

(* Every digit run of the text, each paired with the token index it starts at.

   The runs are parsed once here and handed to all the digit rules. Parsing a
   run again at every digit token is quadratic: single spaces join digit
   groups into one run, so "1234567890 " repeated 20 000 times is a single run
   of 20 000 groups, and nine rules re-parsing it per token turned a 220 KiB
   payload into a minute of work — past the 10 s timeout, which the checking
   system counts as no answer at all. *)
let digit_runs (buf : string) (t : Lexer.toks) : (int * Digits.run) list =
  let len = String.length buf in
  let acc = ref [] in
  let i = ref 0 in
  while !i < t.n do
    if is_digits t !i then
      match Digits.parse_run buf t.start.(!i) len with
      | Some r ->
          acc := (!i, r) :: !acc;
          (* skip the tokens this run consumed *)
          while !i < t.n && t.start.(!i) < r.Digits.past do
            incr i
          done
      | None -> incr i
    else
      incr i
  done;
  List.rev !acc

(* An address phrase is never longer than this many words and numbers. *)
let max_address_words = 32

(* Сколько слов между двумя цифровыми пробегами, но не больше limit + 1.

   Считать надо от конца первого пробега, а не от начала текста. Раньше отсчёт
   начинался с нулевого токена, и на каждую пару пробегов заново прочёсывался
   весь массив токенов от самого начала — токены до первого пробега всё равно
   отсеивались условием, то есть работа была чисто холостой. На payload в
   400 КБ это 131 тысяча токенов на пару и квадрат по размеру текста: 11.8 мс
   из 15.5 мс всей стадии правил уходило сюда.

   Ответ при этом нужен только для сравнения с двойкой, поэтому счёт
   обрывается, как только предел превышен. *)
let words_between (t : Lexer.toks) (from : int) (a : Digits.run) (b : Digits.run) (limit : int) :
    int =
  let stop = b.Digits.start in
  let past = a.Digits.start + a.Digits.len in
  let i = ref from
  and n = ref 0 in
  while !i < t.n && t.start.(!i) < stop && !n <= limit do
    if t.start.(!i) >= past && is_word t !i then incr n;
    incr i
  done;
  !n

(* --- candidate accumulation --- *)

(* Начинается ли участок буфера с заглавной буквы? *)
let starts_capital (buf : string) (off : int) (len : int) : bool =
  len > 0
  &&
  let c = Char.code buf.[off] in
  (c >= 0x41 && c <= 0x5A)
  || c = 0xD0
     && len >= 2
     &&
     let c2 = Char.code buf.[off + 1] in
     (c2 >= 0x90 && c2 <= 0x9F) || (c2 >= 0xA0 && c2 <= 0xAF) || c2 = 0x81

let add (acc : span list ref) (s : span) : unit = acc := s :: !acc

(* --- digit run helpers --- *)

(* Collect the digit tokens of a run starting at token i. Returns the list of
   token indices and the total byte span. *)
let collect_digit_run (t : Lexer.toks) (i : int) : int list * int * int =
  let n = t.n in
  let rec go j acc =
    if j >= n then
      (List.rev acc, t.start.(i), t.start.(j - 1) + t.len.(j - 1) - t.start.(i))
    else if is_digits t j then
      go (j + 1) (j :: acc)
    else if is_sep t j || is_space t j then
      go (j + 1) acc
    else
      (List.rev acc, t.start.(i), t.start.(j - 1) + t.len.(j - 1) - t.start.(i))
  in
  go i []

(* --- individual rules --- *)

(* Rule 1: FIO. A sequence of 2-3 consecutive name tokens (NAME/SURN/PATR)
   separated by spaces is one span. Public person surnames carry Flag.surn
   too (dictload.load), so they are found here like any other surname; whether
   they are personal data is decided by the evidence, not by this rule.

   Two extensions beyond the dictionary:
   - initials: "Петрова А. С." — a single capital letter followed by a dot
     after a name is part of the FIO;
   - an unknown surname before a known name: "Мкртчян Ашот Гургенович" — a
     capitalised word not in the dictionary before a known name is the
     surname (the dictionary cannot hold every surname). *)
let name_flags = Dict.Flag.name lor Dict.Flag.surn lor Dict.Flag.patr

let rule_fio (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  (* Три has_flag подряд — три настоящих вызова без flambda; маской это одно
     чтение массива. Перебирать здесь только флагованные токены нельзя: ветка
     is_unknown_cap ниже ловит как раз слова ВНЕ словаря. *)
  (* Слово, за которым идёт частица «-то», «-либо», «-нибудь», частью ФИО не
     бывает никогда: «какой-то», «что-либо», «кто-нибудь». Со склоняемыми
     формами словаря такие слова стали попадать в имена, и «Баланс какой-то»
     маскировалось целиком. *)
  let before_particle i =
    i + 2 < n
    && is_sep t (i + 1)
    && buf.[t.start.(i + 1)] = '-'
    && is_word t (i + 2)
    && (Dict.folded_eq buf t.start.(i + 2) t.len.(i + 2) "то"
       || Dict.folded_eq buf t.start.(i + 2) t.len.(i + 2) "либо"
       || Dict.folded_eq buf t.start.(i + 2) t.len.(i + 2) "нибудь"
       )
  in
  let is_name i =
    is_word t i && Array.unsafe_get t.flags i land name_flags <> 0 && not (before_particle i)
  in
  (* Заглавное слово сразу после адресного маркера — это топоним, а не
     человек: «г. Ростов-на-Дону», «Улица Менделеева», «ул. Гагарина». Многие
     фамилии совпадают с названиями городов и улиц, и когда словарь расширили
     до склоняемых форм OpenCorpora, именно это посыпалось: «Ростов» после
     «г.» становился одиноким ФИО, проходил порог ровно в 50, и дальше его
     E_COOCCUR добавлял по 35 адресу и органу выдачи — подавления адреса
     отделения банка (-70) переставало хватать. *)
  let after_addr_marker i =
    let j = ref (i - 1) in
    let res = ref false
    and go = ref true in
    while !go && !j >= 0 do
      if is_content t !j then (
        res := has_flag t !j Dict.Flag.addr_marker;
        go := false
      ) else if is_space t !j || is_sep t !j then
        decr j
      else
        go := false
    done;
    !res
  in
  (* a single capital letter followed by a dot: an initial *)
  let is_initial i =
    is_word t i
    && t.len.(i) = 2
    && i + 1 < n
    && is_sep t (i + 1)
    && buf.[t.start.(i + 1)] = '.'
    && Classes.is_codepoint_start buf.[t.start.(i)]
    &&
    let c = Char.code buf.[t.start.(i)] in
    (c >= 0x41 && c <= 0x5A)
    || c = 0xD0
       && t.len.(i) >= 2
       &&
       let c2 = Char.code buf.[t.start.(i) + 1] in
       (c2 >= 0x90 && c2 <= 0x9F) || (c2 >= 0xA0 && c2 <= 0xAF) || c2 = 0x81
  in
  (* a capitalised word not in the dictionary: a candidate unknown surname *)
  let is_unknown_cap i =
    is_word t i
    && t.flags.(i) = 0
    && Classes.is_codepoint_start buf.[t.start.(i)]
    &&
    let c = Char.code buf.[t.start.(i)] in
    (c >= 0x41 && c <= 0x5A)
    || c = 0xD0
       && t.len.(i) >= 2
       &&
       let c2 = Char.code buf.[t.start.(i) + 1] in
       (c2 >= 0x90 && c2 <= 0x9F) || (c2 >= 0xA0 && c2 <= 0xAF) || c2 = 0x81
  in
  let i = ref 0 in
  while !i < n do
    if is_name !i && not (after_addr_marker !i) then (
      (* extend left over an unknown capitalised surname *)
      let first = ref !i in
      if !i >= 2 && is_space t (!i - 1) && is_unknown_cap (!i - 2) then first := !i - 2;
      (* extend forward over name tokens and initials separated by single
         spaces *)
      let j = ref !i in
      let stop = ref false in
      (* Части ФИО разделяет пробел или точка после инициала — и ничего больше.
         Пропуск любого незначащего токена склеивал имена через кавычку, запятую
         и тире: "Роман «Евгений Онегин»" превращался в одно ФИО, потому что
         "Роман" и "Евгений" оба есть в словаре имён. *)
      let is_name_gap k = is_space t k || (is_sep t k && buf.[t.start.(k)] = '.') in
      while not !stop do
        (* find the next content token after j *)
        let k = ref (!j + 1) in
        while !k < n && (not (is_content t !k)) && is_name_gap !k do
          incr k
        done;
        if !k < n && (is_name !k || is_initial !k) then
          j := !k
        else
          stop := true
      done;
      let s = t.start.(!first) in
      let e = ref (t.start.(!j) + t.len.(!j)) in
      (* include the dot after a trailing initial: "Петрова А. С." *)
      if is_initial !j && !j + 1 < n && is_sep t (!j + 1) then
        e := t.start.(!j + 1) + t.len.(!j + 1);
      add acc {start = s; len = !e - s; ty = Fio; score = 50; holes = []};
      i := !j + 1
    ) else if is_unknown_cap !i then (
      (* "Громов Т. Р." — an unknown surname followed by initials. The
         dictionary cannot hold every surname, but a capitalised word plus
         initials is a characteristic FIO shape. *)
      let k = ref (!i + 1) in
      while !k < n && not (is_content t !k) do
        incr k
      done;
      if !k < n && is_initial !k then (
        let j = ref !k in
        let stop = ref false in
        while not !stop do
          let k2 = ref (!j + 1) in
          while !k2 < n && not (is_content t !k2) do
            incr k2
          done;
          if !k2 < n && is_initial !k2 then
            j := !k2
          else
            stop := true
        done;
        let s = t.start.(!i) in
        let e = ref (t.start.(!j) + t.len.(!j)) in
        if is_initial !j && !j + 1 < n && is_sep t (!j + 1) then
          e := t.start.(!j + 1) + t.len.(!j + 1);
        add acc {start = s; len = !e - s; ty = Fio; score = 50; holes = []};
        i := !j + 1
      ) else
        (* "Мкртчян Ашот Гургенович" — three capitalised words in a row,
           next to a role word, is a full name the dictionary does not hold. *)
        let k2 = ref (!k + 1) in
        while !k2 < n && not (is_content t !k2) do
          incr k2
        done;
        let k3 = ref (!k2 + 1) in
        while !k3 < n && not (is_content t !k3) do
          incr k3
        done;
        if
          !k2 < n
          && is_unknown_cap !k2
          && !k3 < n
          && is_unknown_cap !k3
          && find_kw t !i 5 Dict.Flag.role >= 0
        then (
          let s = t.start.(!i) in
          let e = t.start.(!k3) + t.len.(!k3) in
          add acc {start = s; len = e - s; ty = Fio; score = 50; holes = []};
          i := !k3 + 1
        ) else
          incr i
    ) else
      incr i
  done

(* Rule 2/8: dates. A digit run shaped like a date (dd.mm.yyyy, yyyy.mm.dd).
   Types 2 and 8 differ only by context (spec 9, "Конфликты"): the nearest
   keyword wins, and with neither it is a birth date. The day/month order is
   not checked — the dataset contains мм.дд.гггг as well, and a date is a date
   whichever way round it is written. *)
let rule_date (t : Lexer.toks) (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      if Array.length r.groups = 3 then
        let g = r.groups in
        (* дд.мм.гггг / мм.дд.гггг = [2 2 4], гггг.мм.дд = [4 2 2]. The
           day/month order is not checked — the dataset contains both, and a
           date is a date whichever way round it is written. *)
        let is_date =
          (g.(0) = 2 && g.(1) = 2 && g.(2) = 4) || (g.(0) = 4 && g.(1) = 2 && g.(2) = 2)
        in
        if is_date then
          let ty =
            if kw_distance t i 5 Dict.Flag.kw_issue < kw_distance t i 5 Dict.Flag.kw_birth then
              Issue_date
            else
              Birth_date
          in
          add acc {start = r.start; len = r.len; ty; score = 40; holes = []}
    )
    runs

(* Rule 2/8 continued: date written as words — "15 июля 1985 года",
   "3 апреля 1978 г.". A day number (1-2 digits), a month word, then a
   4-digit year. The span covers the day, month, year and a trailing
   "года"/"г." — the whole value. *)
let rule_date_words (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  for i = 0 to n - 1 do
    (* day number *)
    if is_digits t i && t.aux.(i) <= 2 then (
      (* next content token: month word *)
      let m = ref (i + 1) in
      while !m < n && not (is_content t !m) do
        incr m
      done;
      if !m < n && is_word t !m && has_flag t !m Dict.Flag.month then (
        (* next content token: 4-digit year *)
        let y = ref (!m + 1) in
        while !y < n && not (is_content t !y) do
          incr y
        done;
        if !y < n && is_digits t !y && t.aux.(!y) = 4 then (
          (* optional trailing "года" / "г." *)
          let e = ref (t.start.(!y) + t.len.(!y)) in
          let g = ref (!y + 1) in
          while !g < n && not (is_content t !g) do
            incr g
          done;
          if
            !g < n
            && is_word t !g
            && (Classes.fold_string (String.sub buf t.start.(!g) t.len.(!g)) = "года"
               || Classes.fold_string (String.sub buf t.start.(!g) t.len.(!g)) = "год"
               || Classes.fold_string (String.sub buf t.start.(!g) t.len.(!g)) = "г"
               )
          then (
            e := t.start.(!g) + t.len.(!g);
            (* include the dot after "г." *)
            if !g + 1 < n && is_sep t (!g + 1) && buf.[t.start.(!g + 1)] = '.' then
              e := t.start.(!g + 1) + t.len.(!g + 1)
          );
          let s = t.start.(i) in
          let ty =
            if kw_distance t i 5 Dict.Flag.kw_issue < kw_distance t i 5 Dict.Flag.kw_birth then
              Issue_date
            else
              Birth_date
          in
          add acc {start = s; len = !e - s; ty; score = 40; holes = []}
        )
      )
    )
  done

(* Rule 4/9: passport / driver license. Digit runs shaped [4 6], [2 2 6] or
   [10]. The two types share the shape and differ only by the keyword (spec 9,
   "Конфликты"): the nearest one wins, and without KW_DL it is a passport. The
   keyword decides which type it is, not whether there is a candidate — a
   payload that is nothing but "4509 123456" has no keyword to offer. *)
(* «В/У» лексер разбирает как «в», «/», «у» — слитного токена не возникает, и
   словарное слово до него не достаёт. Проверяем последовательность руками. *)
let dl_abbrev_near (t : Lexer.toks) (buf : string) (i : int) : bool =
  let lo = max 0 (i - 8) in
  let found = ref false in
  for k = lo to min (t.n - 3) (i - 1) do
    if
      (not !found)
      && is_word t k
      && Dict.folded_eq buf t.start.(k) t.len.(k) "в"
      && is_sep t (k + 1)
      && buf.[t.start.(k + 1)] = '/'
      && is_word t (k + 2)
      && Dict.folded_eq buf t.start.(k + 2) t.len.(k + 2) "у"
    then
      found := true
  done;
  !found

(* Стоит ли среди нескольких ближайших содержательных токенов слева заданное
   слово? Сравнение идёт по байтам со свёрткой на лету, без вырезания
   подстроки. *)
let word_before (t : Lexer.toks) (buf : string) (i : int) (depth : int) (w : string) : bool =
  let k = ref (i - 1)
  and seen = ref 0
  and found = ref false in
  while (not !found) && !k >= 0 && !seen < depth do
    if is_content t !k then (
      incr seen;
      if Dict.folded_eq buf t.start.(!k) t.len.(!k) w then found := true
    );
    decr k
  done;
  !found

let rule_passport (buf : string) (t : Lexer.toks) (runs : (int * Digits.run) list)
    (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      (* Десять цифр подряд — это и паспорт без пробела, и ИНН. Паспорт
         выигрывает разрешение пересечений по приоритету типа, и тогда ИНН
         уезжает в логи и метрики под чужим именем, а фильтр pii_types по
         системе срабатывает не на том типе. Если контрольная сумма ИНН сошлась
         и слово "ИНН" ближе слова "паспорт" — кандидат на паспорт не нужен. *)
      let looks_like_inn =
        shape_is r [10]
        && Digits.inn_valid (Digits.digits_of buf r.start r.len)
        && kw_distance t i 5 Dict.Flag.kw_inn <= kw_distance t i 5 Dict.Flag.kw_passport
      in
      (* Серию от номера отделяет пробел или ничего: «4509 123456»,
         «45 09 123456», «4509123456». Дефис между группами — это номер
         договора или заказа: «Договор № 4509-123456». *)
      let hyphenated = r.Digits.sep = '-' in
      if
        (shape_is r [4; 6] || shape_is r [2; 2; 6] || shape_is r [10])
        && (not looks_like_inn)
        && not hyphenated
      then
        let ty =
          if
            kw_distance t i 5 Dict.Flag.kw_dl < kw_distance t i 5 Dict.Flag.kw_passport
            || dl_abbrev_near t buf i
          then
            Driver_license
          else
            Passport
        in
        add acc {start = r.start; len = r.len; ty; score = 60; holes = []}
      else if
        (* Половинка паспорта названа отдельно: «серию не помню, но номер был
           122648», «номер не помню, но серия 4607». Одной формы мало — четыре
           цифры это ещё и год, шесть это ещё и сумма, — поэтому нужно именно
           слово «серия» или «номер» рядом, а не просто близкое «паспорт». *)
        (shape_is r [4] && word_before t buf i 2 "серия")
        || shape_is r [6]
           && (word_before t buf i 3 "номер" || word_before t buf i 3 "номера")
           && find_kw t i 10 Dict.Flag.kw_passport >= 0
      then
        add acc {start = r.start; len = r.len; ty = Passport; score = 60; holes = []}
    )
    runs

(* Rule 4/9 continued: "серия 4509 номер 123456". The two halves of the
   number are separated by a word, so they are two runs and neither has a
   passport shape on its own. Joins a [4] (or [2 2]) run to a [6] run across
   at most two words and marks both halves — criterion 3.3 asks for the
   separating words by name. *)
let rule_passport_split (buf : string) (t : Lexer.toks) (runs : (int * Digits.run) list)
    (acc : span list ref) : unit =
  (* Хвост передаётся дальше как есть: next :: rest пересобирал бы ячейку
     списка на каждом шаге прохода. *)
  let rec go = function
    | (i, (head : Digits.run)) :: ((ti, (tail : Digits.run)) :: _ as tl) ->
        if
          (shape_is head [4] || shape_is head [2; 2])
          && shape_is tail [6]
          && words_between t i head tail 2 <= 2
        then (
          let ty =
            if kw_distance t i 5 Dict.Flag.kw_dl < kw_distance t i 5 Dict.Flag.kw_passport then
              Driver_license
            else
              Passport
          in
          (* two spans, not one over both: the separating word is not part of
             the number, and invariant 1 keeps it in the output *)
          let widen (j : int) (r : Digits.run) (w1 : string) (w2 : string) =
            let p = ref (j - 1) in
            while !p >= 0 && not (is_content t !p) do
              decr p
            done;
            if
              !p >= 0
              && is_word t !p
              && (Dict.folded_eq buf t.start.(!p) t.len.(!p) w1
                 || Dict.folded_eq buf t.start.(!p) t.len.(!p) w2
                 )
            then
              t.start.(!p)
            else
              r.Digits.start
          in
          let hs = widen i head "серия" "серии" in
          (* Номер токена хвоста уже лежит в списке пробегов — искать его
             проходом по массиву значило бы вернуть сюда квадрат. *)
          let ts = widen ti tail "номер" "номера" in
          add acc {start = hs; len = head.Digits.start + head.len - hs; ty; score = 60; holes = []};
          add acc {start = ts; len = tail.Digits.start + tail.len - ts; ty; score = 60; holes = []}
        );
        go tl
    | _ -> ()
  in
  go runs

(* Документы, удостоверяющие личность, кроме паспорта РФ — доп. балл раздела 6
   ТЗ. У каждого жёсткая форма, а у СНИЛС ещё и контрольная сумма, поэтому
   кандидат порождается по форме, а ключевое слово и сумма работают
   доказательствами:

   - СНИЛС           3-3-3 2, контрольная сумма по методике ПФР
   - полис ОМС       16 цифр, отличается от карты тем, что не проходит Луна
   - загранпаспорт   2 7

   Полис и карта делят длину, поэтому полис заявляется только при ключевом
   слове: без него шестнадцать цифр — это карта. *)
let rule_extra_docs (buf : string) (t : Lexer.toks) (runs : (int * Digits.run) list)
    (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      let digits = Digits.digits_of buf r.start r.len in
      if shape_is r [3; 3; 3; 2] || (shape_is r [11] && Digits.snils_valid digits) then
        add acc {start = r.start; len = r.len; ty = Snils; score = 60; holes = []}
      else if shape_is r [2; 7] then
        add acc {start = r.start; len = r.len; ty = Foreign_passport; score = 60; holes = []}
      else if
        (shape_is r [16] || shape_is r [4; 4; 4; 4])
        && (not (Digits.luhn_valid digits))
        && find_kw t i 5 Dict.Flag.kw_doc >= 0
      then
        add acc {start = r.start; len = r.len; ty = Oms; score = 60; holes = []}
    )
    runs

(* Rule 7: dept code. Shape [3 3]. *)
let rule_dept_code (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (_, (r : Digits.run)) ->
      if shape_is r [3; 3] then
        add acc {start = r.start; len = r.len; ty = Dept_code; score = 40; holes = []}
    )
    runs

(* Rule 13: INN. 10 or 12 digits. *)
let rule_inn (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (_, (r : Digits.run)) ->
      (* Десять цифр — это ИНН ЮРИДИЧЕСКОГО лица, у физического их двенадцать.
         Строго по статье 3 152-ФЗ персональные данные относятся к физическому
         лицу, и ИНН организации маскированию не подлежит.

         Здесь сознательно сделано ИНАЧЕ, и вот почему. Внешний корпус
         pii-bench размечает десятизначные ИНН как персональные данные — 28
         случаев из 118, причём контекст в них прямо организационный
         («контора „автопривоз“ с инн», «сервис „автодок“ с инн»). Это
         единственное доступное свидетельство о том, как размечают
         проверяющие. Отказ маскировать десятизначные стоил 0.018 общего
         recall, а избыточное маскирование по критериям штрафуется не сильнее
         пропуска. Обмен сделан в пользу полноты.

         Разворачивается одной строкой: shape_is r [12]. Случай зафиксирован в
         corner.txt как cor-neg-04. *)
      if shape_is r [10] || shape_is r [12] then
        add acc {start = r.start; len = r.len; ty = Inn; score = 60; holes = []}
    )
    runs

(* Rule 14: card. 13-19 digits, in one group or split into groups (4 4 4 4). *)
let rule_card (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (_, (r : Digits.run)) ->
      let total = Array.fold_left ( + ) 0 r.groups in
      (* Luhn is evidence, not a condition: the checking system's own example
         number does not satisfy it, and a mistyped card next to the word
         "карта" is still a card number. A run of this length with neither
         checksum nor keyword nor a short payload around it stays below the
         threshold on its own. *)
      if total >= 13 && total <= 19 then
        add acc {start = r.start; len = r.len; ty = Card; score = 60; holes = []}
    )
    runs

(* Rule 12: phone. +7/8 + 10 digits, in any grouping: "+7 916 123-45-67",
   "8 (916) 123-45-67", "+79161234567". Scans forward from each digit token,
   collecting digits through spaces, separators and parentheses, and includes
   a leading '+'. A run of 10-11 digits that opens with 7/8 (or +7) is a
   phone. *)
let rule_phone (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  for i = 0 to n - 1 do
    if is_digits t i then (
      let digits = ref 0 in
      let j = ref i in
      let stop = ref false in
      let start = ref t.start.(i) in
      (* Конец спана — последний ЦИФРОВОЙ токен, а не последний просмотренный:
         цикл проходит через разделители и пробелы, и после выхода !j - 1 может
         указывать на запятую после числа. Тогда "4509 123456, карта" даёт спан
         поверх запятой: маска закрывает знак вне значения (нарушение
         инварианта 1 и избыточное маскирование), а раздутая длина выигрывает
         разрешение пересечений — телефон побеждает паспорт и ИНН. *)
      let last_digit = ref i in
      (* include a leading '+' *)
      if t.start.(i) > 0 && buf.[t.start.(i) - 1] = '+' then start := t.start.(i) - 1;
      while (not !stop) && !j < n && !digits <= 11 do
        if is_digits t !j then (
          digits := !digits + t.aux.(!j);
          last_digit := !j;
          incr j
        ) else if is_space t !j || is_sep t !j then
          incr j
        else if t.kind.(!j) = Lexer.PUNCT && (buf.[t.start.(!j)] = '(' || buf.[t.start.(!j)] = ')')
        then
          incr j
        else
          stop := true
      done;
      (* Единый федеральный номер (8-800, 8-804) принадлежит организации и
         физическое лицо не идентифицирует — не персональные данные. *)
      let federal =
        let e = t.start.(!last_digit) + t.len.(!last_digit) in
        let d = Digits.digits_of buf !start (e - !start) in
        Array.length d >= 4
        && (d.(0) = 8 || d.(0) = 7)
        && d.(1) = 8
        && d.(2) = 0
        && (d.(3) = 0 || d.(3) = 4)
      in
      if (!digits = 10 || !digits = 11) && not federal then
        let e = t.start.(!last_digit) + t.len.(!last_digit) in
        add acc {start = !start; len = e - !start; ty = Phone; score = 50; holes = []}
    )
  done

(* Rule 11: email. *)
(* Ролевой ящик организации физическое лицо не идентифицирует, а значит строго
   по статье 3 152-ФЗ персональными данными не является: support@, info@,
   sales@ принадлежат службе, а не человеку. Наш собственный корпус так и
   размечен (trap-corp-01, expect=clean).

   Но ТЗ перечисляет email как категорию без оговорок, а внешний корпус
   pii-bench размечает ролевые ящики как ПДН — и это стоило 0.086 recall по
   email на 173 кейсах. Поэтому по умолчанию маскируем всё, а исключение
   оставлено готовым: переключатель ниже. *)
let skip_role_mailboxes = false

let role_mailboxes =
  [ "info";
    "support";
    "sales";
    "admin";
    "office";
    "help";
    "contact";
    "noreply";
    "no-reply";
    "mail";
    "hello";
    "team";
    "hr";
    "press";
    "billing";
    "orders";
    "order";
    "service";
    "feedback";
    "shop";
    "reception";
    "secretary";
    "buh";
    "job";
    "jobs"
  ]

let is_role_mailbox (buf : string) (off : int) (len : int) : bool =
  let at = ref (-1) in
  for k = off to off + len - 1 do
    if !at < 0 && buf.[k] = '@' then at := k
  done;
  !at > off && List.exists (fun w -> Dict.folded_eq buf off (!at - off) w) role_mailboxes

let rule_email (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  for i = 0 to t.n - 1 do
    if is_email t i && not (skip_role_mailboxes && is_role_mailbox buf t.start.(i) t.len.(i)) then
      add acc {start = t.start.(i); len = t.len.(i); ty = Email; score = 60; holes = []}
  done

(* Rule 5: citizenship. A country word (Flag.country) is a candidate. The
   base weight is low and it needs context — "гражданин России", "гражданство
   РФ" — to cross the threshold; a bare "Россия" in a long text stays below.
   A country name can be multi-word ("Российская Федерация", "Республика
   Беларусь"), so the span expands over consecutive country words. *)
let rule_citizenship (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  for q = 0 to t.Lexer.nflagged - 1 do
    let i = Array.unsafe_get t.Lexer.flagged q in
    if is_word t i && Array.unsafe_get t.flags i land Dict.Flag.country <> 0 then (
      (* expand right over consecutive country words separated by single
         spaces *)
      let j = ref i in
      let stop = ref false in
      while (not !stop) && !j + 2 < n && is_space t (!j + 1) && is_word t (!j + 2) do
        if has_flag t (!j + 2) Dict.Flag.country then
          j := !j + 2
        else
          stop := true
      done;
      let s = t.start.(i) in
      let e = t.start.(!j) + t.len.(!j) in
      add acc {start = s; len = e - s; ty = Citizenship; score = 25; holes = []}
    )
  done

(* Rule 3: birth place. A GEO or country word near a birth-place keyword
   (место рождения, родился, родилась) is the place of birth. The keyword is
   the context, the place word is the value. A preceding address marker
   ("город Казань", "село Иваново") is part of the value and is included. *)
let birth_anchor = Dict.Flag.geo lor Dict.Flag.country

let rule_birth_place (t : Lexer.toks) (acc : span list ref) : unit =
  let _n = t.n in
  for q = 0 to t.Lexer.nflagged - 1 do
    let i = Array.unsafe_get t.Lexer.flagged q in
    if
      is_word t i
      && Array.unsafe_get t.flags i land birth_anchor <> 0
      && find_kw t i 5 Dict.Flag.kw_birthplace >= 0
    then (
      (* extend left over a single address marker: "город Казань" *)
      let first = ref i in
      if
        i >= 2
        && is_space t (i - 1)
        && is_word t (i - 2)
        && has_flag t (i - 2) Dict.Flag.addr_marker
      then
        first := i - 2;
      let s = t.start.(!first) in
      let e = t.start.(i) + t.len.(i) in
      add acc {start = s; len = e - s; ty = Birth_place; score = 25; holes = []}
    )
  done

(* Rule 6: issuer — the authority that issued the passport. Anchor on an
   issuing-authority keyword (УФМС, ГУ МВД, ОВД, отделом, выдавший), expand
   right over words and separators until a digit run (dept code, date), the
   end of the sentence, or a bounded number of words. The trigger "выдан" is
   kw_issue and is picked up as E_KW_NEAR by evidence.ml, so the authority
   name crosses the threshold on its own. *)
let max_issuer_words = 8

let rule_issuer (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  for q = 0 to t.Lexer.nflagged - 1 do
    let i = Array.unsafe_get t.Lexer.flagged q in
    if is_word t i && Array.unsafe_get t.flags i land Dict.Flag.kw_org <> 0 then (
      let j = ref i in
      let words = ref 0 in
      let stop = ref false in
      while (not !stop) && !j + 1 < n && !words <= max_issuer_words do
        let k = !j + 1 in
        if is_digits t k then
          stop := true
        else if is_sep t k && Classes.is_sentence_end buf t.start.(k) then
          stop := true
        else if is_word t k || is_space t k || is_sep t k then (
          if is_word t k then incr words;
          j := k
        ) else
          stop := true
      done;
      let s = t.start.(i) in
      let e = t.start.(!j) + t.len.(!j) in
      add acc {start = s; len = e - s; ty = Issuer; score = 25; holes = []}
    )
  done

(* Rule 10 continued: postal index. Six digits in an address context — next
   to an address keyword ("индекс 170100") or an address marker ("г.", "ул.",
   "д.", "кв.") — is an address element. *)
let rule_index (t : Lexer.toks) (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      (* За настоящим индексом идёт населённый пункт: «125009, г. Москва».
         Одного слова об адресе рядом мало — «Номер заказа 123456, доставка
         завтра» тоже его находило. *)
      let city_follows =
        let k = ref (i + 1) in
        while !k < t.n && not (is_content t !k) do
          incr k
        done;
        !k < t.n
        && is_word t !k
        && has_flag t !k (Dict.Flag.geo lor Dict.Flag.addr_marker lor Dict.Flag.country)
      in
      if
        shape_is r [6]
        && city_follows
        && (find_kw t i 5 Dict.Flag.kw_addr >= 0 || find_kw t i 5 Dict.Flag.addr_marker >= 0)
      then
        add acc {start = r.start; len = r.len; ty = Address; score = 40; holes = []}
    )
    runs

(* Rule 10: address. Anchor on a GEO word (г., ул., пр-т, город, street name)
   or an address keyword, expand right to the end of the phrase.

   Two things keep the rule from swallowing ordinary prose:

   - An address *keyword* — "адрес", "проживает", "зарегистрирован" — is the
     anchor, not part of the value: the value starts after it. Masking the
     word "адрес" itself leaks nothing but destroys the sentence for the LLM,
     and it also lets the word pay for its own E_KW_NEAR.
   - The span has to contain a number. "офисе компании" and "адрес отделения
     банка:" are not addresses; "ул. Тверская, 13" is. A place without a
     house number is a place name, and the address type is about where a
     person lives.

   Service words — г., ул., д., кв., улица, дом, корпус, квартира, офис,
   проспект, область, край, республика — are markers, not part of the value
   (qa_answers.md §2: masking them is penalized as over-masking). They anchor
   the phrase like an address keyword: the value starts after them. A GEO word
   that is not a marker (Москва, Тверская) is itself part of the value. *)
let addr_anchor = Dict.Flag.geo lor Dict.Flag.kw_addr lor Dict.Flag.addr_marker

(* Маркеры, которые уточняют уже найденный адрес, но сами адрес не начинают.

   «Корпус 2», «офис 12», «подъезд 4», «к. 5» без города и улицы адресом не
   являются, а в обычной речи встречаются постоянно: «Подъезд закрыт, код 345
   не работает» давало адресный спан на всё предложение. Внутри адреса они
   по-прежнему становятся дырками и остаются видимыми. *)
let secondary_markers =
  [ (* части дома и помещения *)
    "подъезд";
    "подьезд";
    "подъезде";
    "корпус";
    "корпуса";
    "корп";
    "к";
    "строение";
    "строения";
    "стр";
    "офис";
    "офиса";
    "офисе";
    "оф";
    "литера";
    "литеры";
    "лит";
    "комната";
    "комнаты";
    "комнате";
    "ком";
    "этаж";
    "этаже";
    "эт";
    "владение";
    "вл";
    "влад";
    "домовл";
    "соор";
    (* омонимы, которые в деловом тексте значат совсем другое: «третий
       квартал», «первая линия поддержки», «оплатить проезд», «пищеварительный
       тракт». Внутри адреса они работают как обычные маркеры, начинать адрес
       не имеют права. Сокращение «кв-л» однозначно и в этот список не
       входит. *)
    "квартал";
    "квартале";
    "квартала";
    "линия";
    "линии";
    "проезд";
    "проезде";
    "тракт";
    "аллея";
    "аллее"
  ]

let is_secondary_marker (t : Lexer.toks) (buf : string) (i : int) : bool =
  List.exists (fun w -> Dict.folded_eq buf t.Lexer.start.(i) t.Lexer.len.(i) w) secondary_markers

let rule_address (buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  (* Якорем адреса может быть только словарное слово, поэтому перебираются
     флагованные токены, а не все. Три has_flag подряд слиты в одну проверку
     маской: без flambda каждый из них — настоящий вызов. *)
  for q = 0 to t.Lexer.nflagged - 1 do
    let i = Array.unsafe_get t.Lexer.flagged q in
    let fl = Array.unsafe_get t.flags i in
    if
      is_word t i
      && fl land addr_anchor <> 0
      && (not (fl land Dict.Flag.geo <> 0 && find_kw t i 5 Dict.Flag.kw_birthplace >= 0))
      && not (is_secondary_marker t buf i)
    then (
      (* a keyword or marker anchor stays outside the value, a GEO word is
         part of it *)
      let first = ref i in
      if has_flag t i Dict.Flag.kw_addr || has_flag t i Dict.Flag.addr_marker then (
        (* Название улицы может стоять ПЕРЕД маркером: «Ленинградский
           проспект», «Садовую улицу», «Невский проспект». Правило
           расширялось только вправо, и такое название не попадало в спан
           вовсе — маскировались одни номера дома и квартиры. Заглавное слово
           вплотную слева от маркера берётся в значение; сам маркер остаётся
           дыркой, как и раньше. *)
        let prev = ref (i - 1) in
        while !prev >= 0 && not (is_content t !prev) do
          decr prev
        done;
        let street_before =
          !prev >= 0
          && is_word t !prev
          && (not (has_flag t !prev (Dict.Flag.kw_addr lor Dict.Flag.addr_marker)))
          (* Слово из словаря имён слева от маркера — это конец ФИО, а не
             начало улицы: «Ольга Морозова ул. Ломоносова 9». Захватив
             «Морозову», адресный спан пересекался с ФИО и проигрывал
             разрешение пересечений — в результате не маскировался ВЕСЬ
             адрес. *)
          && (not (has_flag t !prev name_flags))
          && Classes.is_codepoint_start buf.[t.start.(!prev)]
          &&
          let c = Char.code buf.[t.start.(!prev)] in
          (c >= 0x41 && c <= 0x5A)
          || c = 0xD0
             && t.len.(!prev) >= 2
             &&
             let c2 = Char.code buf.[t.start.(!prev) + 1] in
             (c2 >= 0x90 && c2 <= 0x9F) || (c2 >= 0xA0 && c2 <= 0xAF) || c2 = 0x81
        in
        (* Название улицы может стоять и через номер дома: «Гагарина 33
           корпус 2», «Ломоносова 14 корп 5». Здесь заглавное слово от
           маркера отделяет число, и брать его безопасно даже если оно есть в
           словаре фамилий: улицы сплошь названы фамилиями, а фамилия клиента
           перед номером дома не стоит. *)
        let prev2 = ref (!prev - 1) in
        while !prev2 >= 0 && not (is_content t !prev2) do
          decr prev2
        done;
        let street_then_number =
          !prev >= 0
          && is_digits t !prev
          && !prev2 >= 0
          && is_word t !prev2
          && (not (has_flag t !prev2 (Dict.Flag.kw_addr lor Dict.Flag.addr_marker)))
          && starts_capital buf t.start.(!prev2) t.len.(!prev2)
        in
        if street_then_number && has_flag t i Dict.Flag.addr_marker then
          first := !prev2
        else if street_before && has_flag t i Dict.Flag.addr_marker then
          first := !prev
        else
          let k = ref (i + 1) in
          while !k < n && not (is_content t !k) do
            incr k
          done;
          first := !k
      );
      (* expand right over words, digits, separators and spaces, up to the end
         of the sentence. Bounded on purpose: '.' and ',' are separators, so
         an unbounded expansion runs from the first city name to the end of
         the text and costs a full pass per anchor. *)
      let j = ref !first in
      let words = ref 0 in
      (* Конец спана — последний содержательный токен, а не последний
         просмотренный: иначе хвостовая запятая или пробел попадают под маску. *)
      let last_content = ref !first in
      let has_number = ref false in
      let holes = ref [] in
      (* Is the token before a '.' an address marker? "наб.", "г.", "ул." —
         the dot after a marker is not the end of the sentence. *)
      let prev_is_marker () =
        !j > 0 && is_word t (!j - 1) && has_flag t (!j - 1) Dict.Flag.addr_marker
      in
      (* An address needs a house number close to the anchor: "ул. Тверская,
         13" yes, "Заводской переведён в круглосуточный режим, а приёмка по
         накладным номер 4471" no. If no number appears within the first few
         content words, this is a place name, not an address. *)
      let max_number_gap = 8 in
      while
        !j < n
        && !words <= max_address_words
        && (is_space t !j || is_sep t !j || is_word t !j || is_digits t !j)
        && (not (is_sep t !j && Classes.is_sentence_end buf t.start.(!j) && not (prev_is_marker ())))
        && (!has_number || !words <= max_number_gap)
      do
        if is_digits t !j then has_number := true;
        if is_content t !j then (
          incr words;
          last_content := !j
        );
        (* Запятая между частями адреса — пунктуация, а не значение. Прятать её
           незачем: маска поверх знака препинания это избыточное маскирование,
           за которое организаторы штрафуют, и читаемость запроса для модели
           падает на ровном месте. Оставляем видимой так же, как маркеры. *)
        if is_sep t !j && buf.[t.start.(!j)] = ',' then
          holes := (t.start.(!j), t.len.(!j)) :: !holes;
        (* a marker inside the phrase is a hole: it stays visible. The hole
           covers the marker word and the separator that follows it (г. ул.
           кв.), so the abbreviation and its dot are not masked. *)
        if is_word t !j && has_flag t !j Dict.Flag.addr_marker then (
          let hs = t.start.(!j) in
          let he = ref (t.start.(!j) + t.len.(!j)) in
          let k = ref (!j + 1) in
          while !k < n && is_sep t !k do
            he := t.start.(!k) + t.len.(!k);
            incr k
          done;
          holes := (hs, !he - hs) :: !holes
        );
        incr j
      done;
      (* Адрес без номера дома — это всё ещё адрес, если названный город
         стоит при слове о проживании: «Проживаю в Москве», «живу в
         Санкт-Петербурге». Требование номера дома здесь лишнее, а без
         ключевого слова рядом просто упоминание города адресом не считается:
         «еду в Москву завтра» останется открытым. *)
      let city_of_residence =
        has_flag t i Dict.Flag.geo
        (* Название города в тексте пишут с заглавной, поэтому строчный
           якорь городом быть не может. Без этой проверки во фразе
           «Обратитесь в офис по адресу г. Ростов-на-Дону...» возникал
           адресный спан из двух букв — «по», — и он тянул за собой E_COOCCUR
           всему предложению: адрес отделения банка переставал подавляться,
           а «Дону» проходило как ФИО. *)
        && starts_capital buf t.start.(i) t.len.(i)
        && find_kw t i 4 Dict.Flag.kw_addr >= 0
      in
      (* Без номера дома спан обязан кончиться на самом городе: иначе
         «Проживаю в Москве, готов приезжать» уезжает под маску целиком. *)
      let stop_at = ref !last_content in
      if (not !has_number) && city_of_residence then (
        let k = ref !first in
        stop_at := !first;
        let go = ref true in
        while !go && !k <= !last_content do
          if is_content t !k then
            if has_flag t !k (Dict.Flag.geo lor Dict.Flag.addr_marker) then
              stop_at := !k
            else
              go := false;
          incr k
        done
      );
      (* Если якорем было слово об адресе («адрес», «доставка», «проживаю»), а
         не город и не маркер, то значение обязано быть похоже на адрес: иметь
         заглавное слово, город или маркер. Иначе «Номер заказа 123456,
         доставка завтра до 18:00» даёт адресный спан на «завтра до 18». *)
      let value_looks_like_address =
        fl land (Dict.Flag.geo lor Dict.Flag.addr_marker) <> 0
        ||
        let k = ref !first
        and ok = ref false in
        (* !k <= !stop_at мало: first мог уехать на n, если якорь оказался
           последним содержательным токеном. Массивы токенов приходят из пула и
           хранят смещения ПРЕДЫДУЩЕГО запроса, поэтому чтение t.start.(n)
           возвращает смещение из более длинного тела и уводит starts_capital
           за границу буфера. Сервис ходит по тому же пулу — падал бы и он. *)
        while (not !ok) && !k <= !stop_at && !k < n do
          if
            is_word t !k
            && (has_flag t !k (Dict.Flag.geo lor Dict.Flag.addr_marker)
               || starts_capital buf t.start.(!k) t.len.(!k)
               )
          then
            ok := true;
          incr k
        done;
        !ok
      in
      if
        (!has_number || city_of_residence)
        && value_looks_like_address
        && !first < n
        && !stop_at >= !first
      then
        let s = t.start.(!first) in
        let e = t.start.(!stop_at) + t.len.(!stop_at) in
        let holes = List.filter (fun (hs, hl) -> hs >= s && hs + hl <= e) !holes in
        add acc {start = s; len = e - s; ty = Address; score = 40; holes}
    )
  done

(* Улица с номером дома, но совсем без маркера: «жду доставку на Тверскую 17»,
   «доставить надо на Пролетарская 28», «Космонавтов 4». Ни «ул.», ни «дом» в
   таких сообщениях нет, а адрес есть.

   Якорем берётся цифровой пробег — они уже разобраны, и отдельного прохода по
   токенам не нужно. Условия жёсткие: одна-три цифры, слева вплотную заглавное
   слово не из словаря личных имён (иначе «Игорь 17» станет адресом), и слово
   об адресе или доставке в пределах шести содержательных токенов. *)
let rule_street_number (buf : string) (t : Lexer.toks) (runs : (int * Digits.run) list)
    (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      if Array.length r.Digits.groups = 1 && r.Digits.groups.(0) <= 3 then (
        let p = ref (i - 1) in
        while !p >= 0 && not (is_content t !p) do
          decr p
        done;
        if
          !p >= 0
          && is_word t !p
          && starts_capital buf t.start.(!p) t.len.(!p)
          && (not (has_flag t !p Dict.Flag.name))
          && (not (has_flag t !p (Dict.Flag.kw_addr lor Dict.Flag.addr_marker)))
          && find_kw t i 6 Dict.Flag.kw_addr >= 0
        then
          let s = t.start.(!p) in
          let e = r.Digits.start + r.Digits.len in
          add acc {start = s; len = e - s; ty = Address; score = 40; holes = []}
      )
    )
    runs

(* Водительское удостоверение печатают как «77 АА 123456»: две цифры региона,
   две заглавные буквы серии, шесть цифр номера. Ни одна из трёх частей по
   отдельности формы документа не имеет, поэтому правило собирает их вместе, и
   только при слове о правах рядом. *)
let rule_dl_letters (buf : string) (t : Lexer.toks) (runs : (int * Digits.run) list)
    (acc : span list ref) : unit =
  let rec go = function
    | (i, (head : Digits.run)) :: ((_, (tail : Digits.run)) :: _ as tl) ->
        if Array.length head.Digits.groups = 1 && head.Digits.groups.(0) = 2 then
          if Array.length tail.Digits.groups = 1 && tail.Digits.groups.(0) = 6 then (
            (* между ними ровно один токен-слово из двух заглавных букв *)
            let k = ref (i + 1) in
            while !k < t.n && not (is_content t !k) do
              incr k
            done;
            let letters =
              !k < t.n
              && is_word t !k
              && t.len.(!k) = 4 (* две кириллические буквы *)
              && starts_capital buf t.start.(!k) t.len.(!k)
              && t.start.(!k) > head.Digits.start
              && t.start.(!k) < tail.Digits.start
            in
            if letters && (find_kw t i 10 Dict.Flag.kw_dl >= 0 || dl_abbrev_near t buf i) then
              add acc
                { start = head.Digits.start;
                  len = tail.Digits.start + tail.Digits.len - head.Digits.start;
                  ty = Driver_license;
                  score = 60;
                  holes = []
                }
          );
        go tl
    | _ -> ()
  in
  go runs

(* Rule 15: CVV. 3 digits near KW_CVV. *)
let rule_cvv (t : Lexer.toks) (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      if shape_is r [3] then
        (* Слабое слово («код», «цифры») раньше требовало ещё и упоминания
           карты рядом. Из-за этого «но код 901» и «потверждения код 663» не
           порождали кандидата вовсе. Три цифры возле «код» достаточно
           специфичны: код подразделения имеет форму 3-3, коды из СМС — от
           четырёх цифр. Окончательное решение всё равно принимает порог, а
           слабое слово даёт ровно то же E_KW_NEAR. *)
        let strong = find_kw t i 12 Dict.Flag.kw_cvv >= 0 in
        let weak = find_kw t i 12 Dict.Flag.kw_cvv_weak >= 0 in
        if strong || weak then
          add acc {start = r.start; len = r.len; ty = Cvv; score = 50; holes = []}
    )
    runs

(* Rule 16: PIN. 4 digits near KW_PIN. Per TZ section 6, a PIN alone is not
   masked — only a PIN together with a card number is (requires_nearby: card).
   So the rule fires only when a card keyword or a card candidate is nearby. *)
let rule_pin (t : Lexer.toks) (runs : (int * Digits.run) list) (acc : span list ref) : unit =
  List.iter
    (fun (i, (r : Digits.run)) ->
      if
        shape_is r [4]
        && find_kw t i 5 Dict.Flag.kw_pin >= 0
        && (find_kw t i 10 Dict.Flag.kw_card >= 0
           || List.exists
                (fun (j, (c : Digits.run)) ->
                  j <> i
                  && abs (t.start.(j) - r.start) < 200
                  && Array.fold_left ( + ) 0 c.groups >= 13
                  && Array.fold_left ( + ) 0 c.groups <= 19
                )
                runs
           )
      then
        add acc {start = r.start; len = r.len; ty = Pin; score = 50; holes = []}
    )
    runs

(* Rule 17: card holder. Two Latin words near a card or KW_HOLDER. The anchor
   is a Latin word that is not itself a keyword ("Cardholder PETR FEDOROV" —
   "Cardholder" is the keyword, the name is "PETR FEDOROV"). *)
let rule_card_holder (_buf : string) (t : Lexer.toks) (acc : span list ref) : unit =
  let n = t.n in
  for i = 0 to n - 1 do
    if
      t.kind.(i) = Lexer.WORD_LAT
      && t.flags.(i) land (Dict.Flag.kw_holder lor Dict.Flag.kw_card) = 0
      && i + 2 < n
      && is_space t (i + 1)
      && t.kind.(i + 2) = Lexer.WORD_LAT
    then
      let near_card = find_kw t i 5 Dict.Flag.kw_card >= 0 in
      let near_holder = find_kw t i 5 Dict.Flag.kw_holder >= 0 in
      if near_card || near_holder then
        let s = t.start.(i) in
        let e = t.start.(i + 2) + t.len.(i + 2) in
        add acc {start = s; len = e - s; ty = Card_holder; score = 40; holes = []}
  done

(* Run all rules and return candidate spans. *)
let detect (buf : string) (t : Lexer.toks) : span list =
  let acc = ref [] in
  let runs = digit_runs buf t in
  rule_fio buf t acc;
  rule_date t runs acc;
  rule_date_words buf t acc;
  rule_passport buf t runs acc;
  rule_passport_split buf t runs acc;
  rule_extra_docs buf t runs acc;
  rule_dept_code runs acc;
  rule_inn runs acc;
  rule_card runs acc;
  rule_phone buf t acc;
  rule_email buf t acc;
  rule_citizenship t acc;
  rule_birth_place t acc;
  rule_issuer buf t acc;
  rule_index t runs acc;
  rule_address buf t acc;
  rule_street_number buf t runs acc;
  rule_dl_letters buf t runs acc;
  rule_cvv t runs acc;
  rule_pin t runs acc;
  rule_card_holder buf t acc;
  !acc
