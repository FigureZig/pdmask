(* dict.ml — hash dictionary with open addressing, FNV-1a.

   Design (spec 4.2):
   - Open addressing, power-of-two capacity.
   - FNV-1a 64 hash over folded bytes.
   - Lookup takes (buf, off, len) and does not create a substring.
   - The value is a bitmask of flags (word categories and keywords).

   Folding is applied inside the hashing loop (see Classes.fold_byte /
   Classes.fold_pair), so "ИВАНОВ", "Иванов" and "иванов" hash to the same key
   without allocating a folded copy. *)

(* Word flags. Each bit marks a category or keyword the word belongs to. *)
module Flag = struct
  type t = int

  let none = 0

  let name = 1 lsl 0

  let surn = 1 lsl 1

  let patr = 1 lsl 2

  let geo = 1 lsl 3

  let country = 1 lsl 4

  let month = 1 lsl 5

  let kw_passport = 1 lsl 6

  let kw_birth = 1 lsl 7

  let kw_issue = 1 lsl 8

  let kw_dept = 1 lsl 9

  let kw_dl = 1 lsl 10

  let kw_addr = 1 lsl 11

  let kw_inn = 1 lsl 12

  let kw_card = 1 lsl 13

  let kw_cvv = 1 lsl 14

  let kw_cvv_weak = 1 lsl 30

  let kw_pin = 1 lsl 15

  let kw_holder = 1 lsl 16

  let kw_citizen = 1 lsl 17

  let kw_org = 1 lsl 18

  let kw_birthplace = 1 lsl 19

  let role = 1 lsl 20

  let stop_ctx = 1 lsl 21

  let public_person = 1 lsl 22

  let title_ctx = 1 lsl 23

  let doc_ctx = 1 lsl 24

  let eponym_head = 1 lsl 25

  let possess_head = 1 lsl 26

  let kw_phone = 1 lsl 27

  let addr_marker = 1 lsl 28

  let kw_doc = 1 lsl 29
end

type t =
  { mutable keys : string array; (* stored folded keys, "" = empty slot *)
    mutable vals : int array; (* flag bitmask per slot *)
    mutable size : int; (* number of occupied slots *)
    mutable capacity : int (* power of two *)
  }

(* Пустой ключ — один разделяемый объект: все ячейки таблицы инициализируются
   именно им, поэтому «ячейка свободна?» проверяется физическим равенством.
   Через = это был бы вызов caml_string_equal на каждый проб, то есть на
   каждое слово каждого запроса. *)
let empty_key = ""

(* FNV-1a 64 over folded bytes of buf[off..off+len). *)
(* FNV-1a на обычном int, а не на Int64. Int64 в OCaml боксированный: каждое
   Int64.mul и Int64.logxor — это новый блок в куче, то есть две аллокации на
   байт каждого слова каждого запроса. Хеш нигде не хранится и не передаётся
   наружу, он только выбирает слот в таблице, так что 63 бит с запасом хватает.
   Переполнение при умножении здесь штатное — на нём хеш и держится. *)
let fnv_prime = 0x100000001b3

let fnv_offset = 0x3bf29ce484222325

let hash_folded (buf : string) (off : int) (len : int) : int =
  let h = ref fnv_offset in
  let i = ref off in
  let stop = off + len in
  while !i < stop do
    let b = buf.[!i] in
    let c = Char.code b in
    (* fold a single byte; for Cyrillic lead bytes fold the pair *)
    if c = 0xD0 || c = 0xD1 then
      if !i + 1 < stop then (
        let p = Classes.fold_pair b buf.[!i + 1] in
        h := !h lxor (p lsr 8) * fnv_prime;
        h := !h lxor (p land 0xFF) * fnv_prime;
        i := !i + 2
      ) else (
        h := !h lxor c * fnv_prime;
        incr i
      )
    else (
      h := !h lxor Char.code (Classes.fold_byte b) * fnv_prime;
      incr i
    )
  done;
  !h

let create ?(capacity = 1 lsl 16) () : t =
  {keys = Array.make capacity empty_key; vals = Array.make capacity 0; size = 0; capacity}

(* capacity — степень двойки, поэтому маска положительна и отрицательный
   хеш даёт корректный слот. *)
let slot_of (t : t) (h : int) : int = h land (t.capacity - 1)

(* Grow the table to the next power of two and rehash. *)
let grow (t : t) =
  let new_cap = t.capacity * 2 in
  let old_keys = t.keys in
  let old_vals = t.vals in
  t.keys <- Array.make new_cap empty_key;
  t.vals <- Array.make new_cap 0;
  t.capacity <- new_cap;
  t.size <- 0;
  Array.iteri
    (fun i k ->
      if k != empty_key then
        let h = hash_folded k 0 (String.length k) in
        let rec insert pos =
          if t.keys.(pos) == empty_key then (
            t.keys.(pos) <- k;
            t.vals.(pos) <- old_vals.(i);
            t.size <- t.size + 1
          ) else
            insert ((pos + 1) land (t.capacity - 1))
        in
        insert (slot_of t h)
    )
    old_keys

(* Insert a folded key with its flags. *)
let add (t : t) (key : string) (flags : int) : unit =
  if t.size * 2 >= t.capacity then grow t;
  let h = hash_folded key 0 (String.length key) in
  let rec insert pos =
    if t.keys.(pos) == empty_key then (
      t.keys.(pos) <- key;
      t.vals.(pos) <- flags;
      t.size <- t.size + 1
    ) else if t.keys.(pos) = key then
      t.vals.(pos) <- t.vals.(pos) lor flags
    else
      insert ((pos + 1) land (t.capacity - 1))
  in
  insert (slot_of t h)

(* Does buf[off..off+len) fold to the stored key k? Compares byte by byte,
   folding the input on the fly, without creating a substring. *)
let folded_eq (buf : string) (off : int) (len : int) (k : string) : bool =
  if String.length k <> len then
    false
  else
    let i = ref off in
    let j = ref 0 in
    let ok = ref true in
    while !ok && !i < off + len do
      let b = buf.[!i] in
      let c = Char.code b in
      if c = 0xD0 || c = 0xD1 then
        if !i + 1 < off + len then (
          let p = Classes.fold_pair b buf.[!i + 1] in
          if p lsr 8 <> Char.code k.[!j] || p land 0xFF <> Char.code k.[!j + 1] then ok := false;
          i := !i + 2;
          j := !j + 2
        ) else (
          if Char.code (Classes.fold_byte b) <> Char.code k.[!j] then ok := false;
          incr i;
          incr j
        )
      else (
        if Char.code (Classes.fold_byte b) <> Char.code k.[!j] then ok := false;
        incr i;
        incr j
      )
    done;
    !ok

(* То же, но хеш уже посчитан вызывающей стороной.

   Лексер всё равно проходит по байтам слова, когда ищет его конец, и считает
   хеш там же: иначе байты слова обходятся трижды — сканирование, хеш,
   сравнение с ключом, — а хеш был самой дорогой частью лексера. *)
let find_hashed (t : t) (buf : string) (off : int) (len : int) (h : int) : int =
  if len = 0 then
    0
  else
    (* Цикл, а не рекурсивное замыкание: probe захватывал t, buf, off и len,
       то есть заводил блок на КАЖДОЕ слово каждого запроса. В лексере это
       были все двести тысяч слов его аллокаций. *)
    let pos = ref (slot_of t h)
    and res = ref 0
    and go = ref true in
    let mask = t.capacity - 1 in
    while !go do
      let k = Array.unsafe_get t.keys !pos in
      if k == empty_key then
        go := false
      else if folded_eq buf off len k then (
        res := Array.unsafe_get t.vals !pos;
        go := false
      ) else
        pos := (!pos + 1) land mask
    done;
    !res

(* Look up buf[off..off+len). Returns the flag bitmask or 0 if absent. *)
let find (t : t) (buf : string) (off : int) (len : int) : int =
  find_hashed t buf off len (hash_folded buf off len)

(* Number of entries. *)
let size (t : t) : int = t.size
