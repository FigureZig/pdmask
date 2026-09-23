(* spans.ml — span type and overlap resolution.

   A span is a byte range in the input with a detected PII type. Rules produce
   candidate spans; spans.ml resolves overlaps and glues adjacent spans.

   Overlap resolution (spec 4.7):
   - longer wins;
   - at equal length, higher type priority wins;
   - at equal priority, higher final weight wins.
   Adjacent spans of the same type through a single space are glued into one
   span (an address made of parts is one span). *)

type ty =
  | Fio
  | Birth_date
  | Birth_place
  | Passport
  | Citizenship
  | Issuer
  | Dept_code
  | Issue_date
  | Driver_license
  | Address
  | Email
  | Phone
  | Inn
  | Card
  | Cvv
  | Pin
  | Card_holder
  | Snils
  | Oms
  | Foreign_passport

let ty_name (t : ty) : string =
  match t with
  | Fio -> "fio"
  | Birth_date -> "birth_date"
  | Birth_place -> "birth_place"
  | Passport -> "passport"
  | Citizenship -> "citizenship"
  | Issuer -> "issuer"
  | Dept_code -> "dept_code"
  | Issue_date -> "issue_date"
  | Driver_license -> "driver_license"
  | Address -> "address"
  | Email -> "email"
  | Phone -> "phone"
  | Inn -> "inn"
  | Card -> "card"
  | Cvv -> "cvv"
  | Pin -> "pin"
  | Card_holder -> "card_holder"
  | Snils -> "snils"
  | Oms -> "oms"
  | Foreign_passport -> "foreign_passport"

(* Priority for overlap resolution: higher wins at equal length. *)
let priority (t : ty) : int =
  match t with
  | Passport -> 100
  | Driver_license -> 95
  | Card -> 90
  | Inn -> 85
  | Phone -> 80
  | Dept_code -> 75
  | Cvv -> 70
  | Pin -> 65
  | Fio -> 60
  | Address -> 55
  | Birth_date -> 50
  | Issue_date -> 50
  | Birth_place -> 45
  | Issuer -> 40
  | Citizenship -> 35
  | Email -> 30
  | Card_holder -> 25
  (* контрольная сумма и жёсткая форма делают их узнаваемее паспорта *)
  | Snils -> 105
  | Foreign_passport -> 98
  | Oms -> 92

type span =
  { start : int;
    len : int;
    ty : ty;
    score : int; (* rule confidence; breaks ties in overlap resolution *)
    holes : (int * int) list
        (* byte ranges within the span that are not part of the value and must not
           be masked — the address service words г., ул., д., кв. (qa_answers.md
           §2). Empty for every type except Address. *)
  }

let end_ (s : span) : int = s.start + s.len

(* Do two spans overlap? *)
let overlaps (a : span) (b : span) : bool = a.start < end_ b && b.start < end_ a

(* Compare two spans for overlap resolution. Returns true if a should win. *)
let better (a : span) (b : span) : bool =
  if a.len <> b.len then
    a.len > b.len
  else if priority a.ty <> priority b.ty then
    priority a.ty > priority b.ty
  else
    a.score > b.score

(* Bit for the type. E_COOCCUR needs the set of types confirmed in a
   sentence, and seventeen types fit in one int. *)
let ty_bit (t : ty) : int =
  let i =
    match t with
    | Fio -> 0
    | Birth_date -> 1
    | Birth_place -> 2
    | Passport -> 3
    | Citizenship -> 4
    | Issuer -> 5
    | Dept_code -> 6
    | Issue_date -> 7
    | Driver_license -> 8
    | Address -> 9
    | Email -> 10
    | Phone -> 11
    | Inn -> 12
    | Card -> 13
    | Cvv -> 14
    | Pin -> 15
    | Card_holder -> 16
    | Snils -> 17
    | Oms -> 18
    | Foreign_passport -> 19
  in
  1 lsl i

(* Resolve a list of candidate spans into non-overlapping spans.
   Greedy: sort by (start, then better), pick spans that don't overlap.

   resolve_by carries whatever is attached to each span through, so the
   caller does not have to look the evidence up again afterwards.

   The picked spans are scanned in ascending start order, so a candidate
   overlaps one of them exactly when it starts before the furthest end picked
   so far; keeping that one number makes the pass linear. Comparing each
   candidate against every span already picked is quadratic, and a long text
   produces thousands of them. *)
let resolve_by (key : 'a -> span) (items : 'a list) : 'a list =
  let sorted =
    List.sort
      (fun x y ->
        let a = key x
        and b = key y in
        if a.start <> b.start then
          Int.compare a.start b.start
        else if better a b then
          -1
        else
          1
      )
      items
  in
  let rec pick acc max_end = function
    | [] -> List.rev acc
    | x :: rest ->
        let s = key x in
        if s.start < max_end then
          pick acc max_end rest
        else
          pick (x :: acc) (max max_end (end_ s)) rest
  in
  pick [] min_int sorted

let resolve (spans : span list) : span list = resolve_by (fun s -> s) spans

(* Glue adjacent spans of the same type separated by a single space into one.
   Only Address spans are glued (an address made of parts is one span).
   Returns a new list. *)
(* Уже упорядочен по началу? Проверка линейная, а сортировка — n log n с
   аллокацией на каждом шаге слияния. На горячем пути список приходит из
   resolve_by, который отдаёт его уже отсортированным, так что сортировка там
   была чистой перекладкой. *)
let rec is_sorted = function
  | a :: (b :: _ as rest) -> a.start <= b.start && is_sorted rest
  | _ -> true

let glue (spans : span list) : span list =
  let sorted =
    if is_sorted spans then
      spans
    else
      List.sort (fun a b -> Int.compare a.start b.start) spans
  in
  let rec go acc = function
    | [] -> List.rev acc
    | s :: rest -> (
        match acc with
        | prev :: tail
          when ( match (prev.ty, s.ty) with
                 | Address, Address -> true
                 | _ -> false
                 )
               && end_ prev + 1 = s.start ->
            (* prev кончился, пробел, начался s — склеиваем.

               Дырки НЕ сдвигаются. Они хранятся в абсолютных смещениях в теле
               запроса: правило адреса кладёт туда t.start токена, и маска
               сравнивает их с абсолютной позицией чтения. Прежний код сдвигал
               их на расстояние между началами спанов, то есть уводил в
               произвольное место — в том числе в середину многобайтового
               символа. Тогда ведущий байт уходил под звёздочку, а
               продолжающий копировался как есть, и наружу отправлялся битый
               UTF-8. Поймал это слепой тест: один кейс из 65 620. *)
            let holes = prev.holes @ s.holes in
            let merged = {prev with len = s.start + s.len - prev.start; holes} in
            go (merged :: tail) rest
        | _ -> go (s :: acc) rest
      )
  in
  go [] sorted
