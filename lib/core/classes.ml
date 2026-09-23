(* classes.ml — 256-byte class table and Cyrillic case folding.

   Each byte of the input maps to a class (spec 4.1):
   - DIGIT    0-9
   - LAT      ASCII letters (folded with |0x20)
   - CYR_HI   first byte of a Cyrillic character (0xD0, 0xD1)
   - CYR_LO   second byte of a Cyrillic character (0x80..0xBF)
   - SEP      - / . ,
   - AT       @
   - PUNCT    other punctuation
   - SPACE    whitespace
   - OTHER    anything else

   Cyrillic case folding preserves byte length (three rules):
     A-P   D0 90..9F  ->  D0 B0..BF     second byte +0x20
     R-Ya  D0 A0..AF  ->  D1 80..8F     first byte -> D1, second -0x20
     Yo    D0 81      ->  D1 91
   Latin folding is |0x20 for A-Z.

   Folding is applied inside the hashing loop; no second buffer is created. *)

type cls =
  | DIGIT
  | LAT
  | CYR_HI
  | CYR_LO
  | SEP
  | AT
  | PUNCT
  | SPACE
  | OTHER

let table : cls array =
  let t = Array.make 256 OTHER in
  (* digits *)
  for c = Char.code '0' to Char.code '9' do
    t.(c) <- DIGIT
  done;
  (* latin letters *)
  for c = Char.code 'A' to Char.code 'Z' do
    t.(c) <- LAT
  done;
  for c = Char.code 'a' to Char.code 'z' do
    t.(c) <- LAT
  done;
  (* Cyrillic lead bytes *)
  t.(0xD0) <- CYR_HI;
  t.(0xD1) <- CYR_HI;
  (* Cyrillic continuation bytes *)
  for c = 0x80 to 0xBF do
    t.(c) <- CYR_LO
  done;
  (* separators *)
  t.(Char.code '-') <- SEP;
  t.(Char.code '/') <- SEP;
  t.(Char.code '.') <- SEP;
  t.(Char.code ',') <- SEP;
  (* at *)
  t.(Char.code '@') <- AT;
  (* whitespace *)
  t.(Char.code ' ') <- SPACE;
  t.(Char.code '\t') <- SPACE;
  t.(Char.code '\n') <- SPACE;
  t.(Char.code '\r') <- SPACE;
  t.(0x0B) <- SPACE;
  t.(0x0C) <- SPACE;
  t

let class_of (b : char) : cls = table.(Char.code b)

(* Fold a single byte to lowercase, preserving byte length.
   Returns the folded byte. For a Cyrillic lead byte (0xD0/0xD1) the caller
   must also fold the following continuation byte; see fold_pair. *)
let fold_byte (b : char) : char =
  let c = Char.code b in
  match c with
  | 0xD0 -> b (* lead byte, handled by fold_pair *)
  | 0xD1 -> b (* lead byte, handled by fold_pair *)
  | c when c >= 0x41 && c <= 0x5A -> Char.chr (c lor 0x20) (* A-Z *)
  | _ -> b

(* Свёртка кириллической пары (ведущий, продолжающий) в нижний регистр.
   Длина в байтах сохраняется; сворачиваются только заглавные, строчная
   кириллика (ведущий 0xD1) возвращается как есть.

   Пара возвращается упакованной в int — ведущий в старшем байте, — а не
   кортежем. Кортеж здесь это блок на каждый кириллический символ входа:
   функция зовётся и из свёртки строки, и из хеширования словаря, то есть на
   каждом слове каждого запроса. Распаковка — lsr и land, обе бесплатные. *)
let fold_pair (lead : char) (cont : char) : int =
  let l = Char.code lead in
  let c = Char.code cont in
  match l with
  | 0xD0 ->
      if c >= 0x90 && c <= 0x9F then
        (l lsl 8) lor (c + 0x20)
      (* А-П *)
      else if c >= 0xA0 && c <= 0xAF then
        (0xD1 lsl 8) lor (c - 0x20)
      (* Р-Я *)
      else if c = 0x81 then
        (* Ё сводится к «е», а не к «ё». В живом русском тексте точки над ё
           почти не ставят, а словари OpenCorpora их сохраняют: «Ковалёва» в
           словаре против «Ковалева» в переписке — это промах на ровном месте,
           и промах систематический, на каждой фамилии с ё. Длина в байтах
           сохраняется: и «е», и «ё» — двухбайтовые. *)
        (0xD0 lsl 8) lor 0xB5 (* Ё -> е *)
      else
        (l lsl 8) lor c
  | 0xD1 ->
      if c = 0x91 then
        (0xD0 lsl 8) lor 0xB5 (* ё -> е *)
      else
        (l lsl 8) lor c
  | _ -> (l lsl 8) lor c

let fold_lead (p : int) : char = Char.unsafe_chr (p lsr 8)

let fold_cont (p : int) : char = Char.unsafe_chr (p land 0xFF)

(* Длина символа UTF-8 по ведущему байту.

   Нужна потому, что байты 0x80..0xBF в таблице классов помечены как CYR_LO:
   это верно для кириллицы, но такие же байты стоят внутри тире, кавычек-ёлочек
   и вообще любого многобайтового символа. Без учёта длины лексер начинает
   токен с середины символа, спан режет символ пополам, и в ответ уходит битый
   UTF-8 — потому что маска выбрасывает продолжающие байты, а ведущий остаётся.

   Одинокий продолжающий байт считаем за один: вход может быть битым, и
   зацикливаться на нём нельзя. *)
let char_len (b : char) : int =
  let c = Char.code b in
  if c < 0x80 then
    1
  else if c land 0xE0 = 0xC0 then
    2
  else if c land 0xF0 = 0xE0 then
    3
  else if c land 0xF8 = 0xF0 then
    4
  else
    1

(* Начинает ли байт кириллическую букву? Только D0 и D1 — остальные ведущие
   байты это что угодно другое, и словом их считать нельзя. *)
let is_cyr_lead (b : char) : bool =
  let c = Char.code b in
  c = 0xD0 || c = 0xD1

(* Is this byte the start of a UTF-8 code point? *)
let is_codepoint_start (b : char) : bool = Char.code b land 0xC0 <> 0x80

(* Is the '.' at i the end of a sentence rather than an abbreviation? A full
   stop closes a sentence when it follows a word of at least three letters:
   "г.", "ул.", "кв.", "им." and the initials "И." are abbreviations, and
   the length is counted in letters. Treating
   those as boundaries would cut "Иванов И.И., адрес: г. Москва" into five
   sentences and lose every E_COOCCUR in it. *)
let sentence_dot (buf : string) (i : int) : bool =
  let rec letters j n =
    if j < 0 || n >= 3 then
      n
    else
      match class_of buf.[j] with
      (* count code points, not bytes: a Cyrillic letter is two bytes, and
         counting bytes makes the two-letter "ул." look like a whole word *)
      | LAT | CYR_HI | CYR_LO ->
          letters (j - 1)
            ( if is_codepoint_start buf.[j] then
                n + 1
              else
                n
            )
      | _ -> n
  in
  letters (i - 1) 0 >= 3

(* Is the byte at i a sentence boundary? *)
let is_sentence_end (buf : string) (i : int) : bool =
  match buf.[i] with
  | '!' | '?' | '\n' -> true
  | '.' -> sentence_dot buf i
  | _ -> false

(* Fold a whole string to lowercase, preserving byte length. Used where a
   substring has to be compared against a folded dictionary entry as a string
   (bank offices, public person forms). The hot path does not go through here:
   Dict.find folds inside the hashing loop and allocates nothing.

   String.lowercase_ascii must not be used for this: it leaves Cyrillic
   untouched, so "Пушкин" would never match the folded key "пушкин". *)
let fold_string (s : string) : string =
  let n = String.length s in
  let out = Bytes.create n in
  let i = ref 0 in
  while !i < n do
    let b = s.[!i] in
    let c = Char.code b in
    if (c = 0xD0 || c = 0xD1) && !i + 1 < n then (
      let p = fold_pair b s.[!i + 1] in
      Bytes.set out !i (fold_lead p);
      Bytes.set out (!i + 1) (fold_cont p);
      i := !i + 2
    ) else (
      Bytes.set out !i (fold_byte b);
      incr i
    )
  done;
  Bytes.unsafe_to_string out
