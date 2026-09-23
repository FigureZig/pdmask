(* dictload.ml — load dictionary files into a Dict.

   Reads the trimmed dictionary files from dicts/ and populates a Dict with
   the appropriate flags. Each file maps to a flag:
   - names.txt         -> Flag.name
   - surnames.txt      -> Flag.surn
   - patronymics.txt   -> Flag.patr
   - geox.txt          -> Flag.geo
   - address_markers.txt -> Flag.addr_marker
   - countries.txt      -> Flag.country
   - months.txt         -> Flag.month
   - stop_context.txt  -> Flag.stop_ctx
   - doc_context.txt   -> Flag.doc_ctx
   - roles.txt         -> Flag.role
   - heads_eponym.txt  -> Flag.eponym_head
   - heads_possess.txt -> Flag.possess_head
   - keywords.txt      -> per-word flags (word flag)

   Words are stored folded (lowercase) so lookup is case-insensitive.

   The files hold one form per line (risk 2 of the spec: the dictionaries are
   trimmed to keep the archive small), but the eponym and possessive evidence
   of section 5 reads names in oblique cases — "паспорт Пушкина", "улица
   Пушкина" — so the missing forms are generated at load time by
   name_forms. *)

let fold = Classes.fold_string

(* Does the folded word end with the folded suffix, leaving a stem of at
   least two Cyrillic characters? *)
let ends_with (w : string) (suf : string) : bool =
  let lw = String.length w
  and ls = String.length suf in
  lw >= ls + 4 && String.sub w (lw - ls) ls = suf

(* Drop the suffix from the word. *)
let stem (w : string) (suf : string) : string = String.sub w 0 (String.length w - String.length suf)

(* Is the last consonant of the stem a hushing one (ж ш ч щ ц)? After those
   the instrumental ending is -ем, not -ом: Александрович -> Александровичем. *)
let hushing (w : string) : bool =
  let l = String.length w in
  l >= 2
  &&
  let tail = String.sub w (l - 2) 2 in
  tail = "ж" || tail = "ш" || tail = "ч" || tail = "щ" || tail = "ц"

(* Declined forms of a Russian personal name, generated from the nominative.
   Five productive classes cover nearly every name, surname and patronymic in
   the dictionaries:

   - possessive surname  -ов -ев -ёв -ин -ын   Пушкин   -> Пушкина, Пушкиным
   - possessive feminine -ова -ева -ёва -ина   Ахматова -> Ахматовой
   - adjectival          -ий -ый -ой           Толстой  -> Толстого
   - feminine noun       -а -я                 Анна     -> Анны, Анне
   - masculine noun      consonant or -ь       Гоголь   -> Гоголя, Гоголем

   Anything that does not fall into a class (Мкртчян, Шевченко, Дюма) is left
   alone: it is either indeclinable or too irregular to generate, and a wrong
   form in the dictionary costs more than a missing one — it can only produce
   a false positive, never a catch. *)
let name_forms (w : string) : string list =
  let add s tails = List.map (fun t -> s ^ t) tails in
  if
    ends_with w "ова"
    || ends_with w "ева"
    || ends_with w "ёва"
    || ends_with w "ина"
    || ends_with w "ына"
  then
    add (stem w "а") ["ой"; "у"; "ы"; "ых"]
  else if
    ends_with w "ов" || ends_with w "ев" || ends_with w "ёв" || ends_with w "ин" || ends_with w "ын"
  then
    add w ["а"; "у"; "ым"; "е"; "ой"; "ы"; "ых"; "ыми"]
  else if ends_with w "ий" then
    add (stem w "ий") ["ого"; "ому"; "им"; "ом"; "ая"; "ой"; "ую"; "ие"; "их"; "ими"]
  else if ends_with w "ый" then
    add (stem w "ый") ["ого"; "ому"; "ым"; "ом"; "ая"; "ой"; "ую"; "ые"; "ых"; "ыми"]
  else if ends_with w "ой" then
    add (stem w "ой") ["ого"; "ому"; "ым"; "ом"; "ая"; "ой"; "ую"; "ые"; "ых"; "ыми"]
  else if ends_with w "ия" then
    add (stem w "я") ["и"; "ю"; "ей"]
  else if ends_with w "я" then
    add (stem w "я") ["и"; "е"; "ю"; "ей"]
  else if ends_with w "а" then
    add (stem w "а") ["ы"; "е"; "у"; "ой"]
  else if ends_with w "ь" then
    add (stem w "ь") ["я"; "ю"; "ем"; "е"]
  else if ends_with w "й" then
    add (stem w "й") ["я"; "ю"; "ем"; "е"]
  else
    add w
      [ "а";
        "у";
        ( if hushing w then
            "ем"
          else
            "ом"
        );
        "е"
      ]

(* Read a dictionary file, one entry per line. Blank lines and lines starting
   with '#' are comments. Entries are folded before insertion. *)
let read_lines (path : string) : string list =
  match In_channel.with_open_bin path (fun ic -> In_channel.input_all ic) with
  | exception _ -> []
  | content ->
      String.split_on_char '\n' content
      |> List.filter_map (fun line ->
          let line = String.trim line in
          if line = "" || line.[0] = '#' then
            None
          else
            Some line
      )

let load_file (dict : Dict.t) (path : string) (flag : int) : unit =
  List.iter (fun line -> Dict.add dict (fold line) flag) (read_lines path)

(* Same, but also insert the declined forms of every entry. *)
let load_file_declined (dict : Dict.t) (path : string) (flag : int) : unit =
  List.iter
    (fun line ->
      let w = fold line in
      Dict.add dict w flag;
      List.iter (fun f -> Dict.add dict f flag) (name_forms w)
    )
    (read_lines path)

(* Load the keywords file: each line is "word flag". *)
let load_keywords (dict : Dict.t) (path : string) : unit =
  List.iter
    (fun line ->
      match String.split_on_char ' ' line with
      | word :: flag :: _ ->
          let f =
            match flag with
            | "passport" -> Dict.Flag.kw_passport
            | "birth" -> Dict.Flag.kw_birth
            | "issue" -> Dict.Flag.kw_issue
            | "dept" -> Dict.Flag.kw_dept
            | "dl" -> Dict.Flag.kw_dl
            | "addr" -> Dict.Flag.kw_addr
            | "inn" -> Dict.Flag.kw_inn
            | "card" -> Dict.Flag.kw_card
            | "cvv" -> Dict.Flag.kw_cvv
            (* Слабое слово CVV: «код», «цифры». Без этой строки флаг не
               проставлялся НИКОМУ, и весь слабый путь правила CVV был мёртвым
               кодом — «но код 901» не порождало кандидата вовсе. *)
            | "cvv_weak" -> Dict.Flag.kw_cvv_weak
            | "pin" -> Dict.Flag.kw_pin
            | "phone" -> Dict.Flag.kw_phone
            | "doc" -> Dict.Flag.kw_doc
            | "holder" -> Dict.Flag.kw_holder
            | "citizen" -> Dict.Flag.kw_citizen
            | "org" -> Dict.Flag.kw_org
            | "birthplace" -> Dict.Flag.kw_birthplace
            | unknown ->
                (* Молча выбрасывать строку словаря нельзя: именно так флаг
                   cvv_weak четыре слова подряд уходил в никуда, а правило
                   продолжало на него ссылаться. *)
                Printf.eprintf "dictload: неизвестный флаг %S у слова %S в %s\n%!" unknown word path;
                0
          in
          if f <> 0 then Dict.add dict (fold word) f
      | _ -> ()
    )
    (read_lines path)

(* A public person: a surname and the full-name forms it appears in. *)
type person =
  { surname : string; (* folded surname, e.g. "пушкин" *)
    forms : string list (* folded full-name forms, e.g. "александр пушкин" *)
  }

(* Все полные формы публичных персон одним открытым хешем.

   Раньше сверка шла List.exists по персонам, внутри List.exists по формам, со
   сравнением строк — то есть сотни caml_string_equal на каждого кандидата в
   ФИО. В профиле всего конвейера это было 17%. Формы уже свёрнуты, а Dict
   сворачивает вход на лету, так что поиск идёт прямо по байтам спана, без
   String.sub и без свёртки в новую строку. *)
let public_forms (persons : person list) : Dict.t =
  let d = Dict.create ~capacity:1024 () in
  List.iter (fun p -> List.iter (fun f -> Dict.add d f 1) p.forms) persons;
  d

(* Load the public persons file. Each line is one person; forms are separated
   by tabs. The surname is the last word of the first form. *)
let load_public_persons (dir : string) : person list =
  read_lines (Filename.concat dir "public_persons.txt")
  |> List.filter_map (fun line ->
      let forms =
        String.split_on_char '\t' line
        |> List.map (fun f -> fold (String.trim f))
        |> List.filter (fun f -> f <> "")
      in
      match forms with
      | [] -> None
      | first :: _ ->
          let words = String.split_on_char ' ' first in
          let surname = List.nth words (List.length words - 1) in
          Some {surname; forms}
  )

(* Load the bank offices file: a list of full address phrases, folded. *)
(* Буквы и цифры свёрнутой строки, остальное отброшено. Адреса
   "г. Ростов-на-Дону, ул. Большая Садовая, 1" и
   "Ростов-на-Дону ул Большая Садовая 1" дают один ключ, поэтому сверка со
   справочником отделений не зависит от того, где начался спан и как
   расставлены сокращения. *)
(* Ключ адреса прямо из тела запроса: свёртка и отбор букв с цифрами за один
   проход. Раньше на каждого адресного кандидата приходилось три прохода и три
   строки — вырезать подстроку, свернуть её, отфильтровать свёрнутую. *)
let keep_in_key (c : char) : bool =
  match Array.unsafe_get Classes.table (Char.code c) with
  | Classes.DIGIT | Classes.LAT | Classes.CYR_HI | Classes.CYR_LO -> true
  | _ -> false

let address_key_of (buf : string) (off : int) (len : int) : string =
  let out = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    let b = String.unsafe_get buf (off + !i) in
    let c = Char.code b in
    if (c = 0xD0 || c = 0xD1) && !i + 1 < len then (
      let p = Classes.fold_pair b (String.unsafe_get buf (off + !i + 1)) in
      let lead = Char.unsafe_chr (p lsr 8)
      and cont = Char.unsafe_chr (p land 0xFF) in
      if keep_in_key lead then Buffer.add_char out lead;
      if keep_in_key cont then Buffer.add_char out cont;
      i := !i + 2
    ) else
      let f = Classes.fold_byte b in
      if keep_in_key f then Buffer.add_char out f;
      incr i
  done;
  Buffer.contents out

let address_key (folded : string) : string =
  let out = Buffer.create (String.length folded) in
  String.iter
    (fun c ->
      match Classes.class_of c with
      | Classes.DIGIT | Classes.LAT | Classes.CYR_HI | Classes.CYR_LO -> Buffer.add_char out c
      | _ -> ()
    )
    folded;
  Buffer.contents out

(* Справочник отделений возвращается уже в виде ключей. Нормализовать их на
   каждого кандидата — а кандидатов-адресов в длинном тексте полторы тысячи —
   значит пересобирать один и тот же Buffer тридцать раз на запрос. *)
let load_bank_offices (dir : string) : string list =
  read_lines (Filename.concat dir "bank_offices.txt")
  |> List.map (fun l -> address_key (fold l))
  |> List.filter (fun k -> k <> "")

(* Load every dictionary. The public persons are passed in rather than read
   here: evidence.ml needs the full-name forms, and their surnames go into the
   dictionary as ordinary surnames carrying Flag.public_person, so that
   rule_fio finds "Пушкина" in "паспорт Пушкина" the same way it finds any
   other surname. *)
let load (dict : Dict.t) (dir : string) (persons : person list) : unit =
  load_file_declined dict (Filename.concat dir "names.txt") Dict.Flag.name;
  load_file_declined dict (Filename.concat dir "surnames.txt") Dict.Flag.surn;
  load_file_declined dict (Filename.concat dir "patronymics.txt") Dict.Flag.patr;
  load_file dict (Filename.concat dir "geox.txt") Dict.Flag.geo;
  load_file dict (Filename.concat dir "address_markers.txt") Dict.Flag.addr_marker;
  load_file dict (Filename.concat dir "countries.txt") Dict.Flag.country;
  load_file dict (Filename.concat dir "months.txt") Dict.Flag.month;
  load_file dict (Filename.concat dir "stop_context.txt") Dict.Flag.stop_ctx;
  load_file dict (Filename.concat dir "doc_context.txt") Dict.Flag.doc_ctx;
  load_file dict (Filename.concat dir "roles.txt") Dict.Flag.role;
  load_file dict (Filename.concat dir "heads_eponym.txt") Dict.Flag.eponym_head;
  load_file dict (Filename.concat dir "heads_possess.txt") Dict.Flag.possess_head;
  load_keywords dict (Filename.concat dir "keywords.txt");
  let public = Dict.Flag.surn lor Dict.Flag.public_person in
  List.iter
    (fun p ->
      Dict.add dict p.surname public;
      List.iter (fun f -> Dict.add dict f public) (name_forms p.surname)
    )
    persons
