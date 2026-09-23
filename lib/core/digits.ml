(* digits.ml — digit run shapes, Luhn, INN checksum.

   Design (spec 4.4):
   - luhn: check digit per ISO/IEC 7812-1 Annex B.
   - inn_valid: 10 and 12 digit INN with FNS check digits.
   - shape: glue adjacent digit tokens through a single separator into a "run"
     with a shape like [4;6], [2;2;6], [4;4;4;4], [3;3].

   A "run" is a maximal sequence of digit groups separated by single
   separators (space, dash, dot). The shape is the list of group lengths. *)

(* Luhn check (ISO/IEC 7812-1 Annex B). digits is the digit sequence without
   the check digit. Returns the check digit. *)
let luhn_check (digits : int array) : int =
  let sum = ref 0 in
  let n = Array.length digits in
  (* double every second digit from the right *)
  for i = n - 1 downto 0 do
    let d = digits.(i) in
    if (n - i) mod 2 = 0 then
      let d2 = d * 2 in
      sum :=
        !sum
        +
        if d2 > 9 then
          d2 - 9
        else
          d2
    else
      sum := !sum + d
  done;
  (10 - (!sum mod 10)) mod 10

(* Validate a full number (including check digit) with Luhn. *)
let luhn_valid (digits : int array) : bool =
  let n = Array.length digits in
  if n < 2 then
    false
  else
    let sum = ref 0 in
    for i = n - 1 downto 0 do
      let d = digits.(i) in
      if (n - i) mod 2 = 0 then
        let d2 = d * 2 in
        sum :=
          !sum
          +
          if d2 > 9 then
            d2 - 9
          else
            d2
      else
        sum := !sum + d
    done;
    !sum mod 10 = 0

(* INN validation (FNS method).
   10-digit: n10 = (2n1+4n2+10n3+3n4+5n5+9n6+4n7+6n8+8n9) mod 11, if 10 then 0.
   12-digit: n11 = (7n1+2n2+4n3+10n4+3n5+5n6+9n7+4n8+6n9+8n10) mod 11, if 10 then 0;
             n12 = (3n1+7n2+2n3+4n4+10n5+3n6+5n7+9n8+4n9+6n10+8n11) mod 11, if 10 then 0. *)
let inn_valid (digits : int array) : bool =
  let n = Array.length digits in
  let check10 (d : int array) : int =
    let w = [|2; 4; 10; 3; 5; 9; 4; 6; 8|] in
    let s = ref 0 in
    for i = 0 to 8 do
      s := !s + (d.(i) * w.(i))
    done;
    let r = !s mod 11 in
    if r = 10 then
      0
    else
      r
  in
  let check11 (d : int array) : int =
    let w = [|7; 2; 4; 10; 3; 5; 9; 4; 6; 8|] in
    let s = ref 0 in
    for i = 0 to 9 do
      s := !s + (d.(i) * w.(i))
    done;
    let r = !s mod 11 in
    if r = 10 then
      0
    else
      r
  in
  let check12 (d : int array) : int =
    let w = [|3; 7; 2; 4; 10; 3; 5; 9; 4; 6; 8|] in
    let s = ref 0 in
    for i = 0 to 10 do
      s := !s + (d.(i) * w.(i))
    done;
    let r = !s mod 11 in
    if r = 10 then
      0
    else
      r
  in
  match n with
  | 10 -> check10 digits = digits.(9)
  | 12 -> check11 digits = digits.(10) && check12 digits = digits.(11)
  | _ -> false

(* Контрольная сумма СНИЛС по методике ПФР: сумма первых девяти цифр с весами
   9..1, затем остаток от 101. Значения 100 и 101 дают контрольное число 00. *)
let snils_valid (digits : int array) : bool =
  if Array.length digits <> 11 then
    false
  else
    let s = ref 0 in
    for i = 0 to 8 do
      s := !s + (digits.(i) * (9 - i))
    done;
    let cs =
      if !s < 100 then
        !s
      else if !s = 100 || !s = 101 then
        0
      else
        let r = !s mod 101 in
        if r = 100 || r = 101 then
          0
        else
          r
    in
    cs = (digits.(9) * 10) + digits.(10)

(* A digit run: a sequence of digit groups separated by single separators.
   shape is the list of group lengths. *)
type run =
  { start : int; (* byte offset of the first digit *)
    len : int; (* total byte length including separators *)
    groups : int array; (* length of each digit group *)
    sep : char; (* the separator character used (or '\000' if single group) *)
    past : int (* смещение сразу за пробегом *)
  }

(* Parse a digit run starting at buf[off]. Returns the run and the offset just
   past it, or None if buf[off] is not a digit. *)
let parse_run (buf : string) (off : int) (len : int) : run option =
  if off >= len || Classes.class_of buf.[off] <> Classes.DIGIT then
    None
  else
    let start = off in
    let groups = ref [] in
    let cur = ref 0 in
    let sep = ref '\000' in
    let i = ref off in
    let last_digit_end = ref off in
    let stop = ref false in
    while (not !stop) && !i < len do
      match Classes.class_of buf.[!i] with
      | Classes.DIGIT ->
          incr cur;
          incr i;
          last_digit_end := !i
      | Classes.SEP when !cur > 0 ->
          (* a separator between digit groups *)
          if !sep = '\000' then sep := buf.[!i];
          groups := !cur :: !groups;
          cur := 0;
          incr i
      | Classes.SPACE when !cur > 0 ->
          (* a single space between digit groups *)
          if !sep = '\000' then sep := ' ';
          groups := !cur :: !groups;
          cur := 0;
          incr i
      | _ -> stop := true
    done;
    if !cur > 0 then groups := !cur :: !groups;
    let groups = Array.of_list (List.rev !groups) in
    let total = !last_digit_end - start in
    Some {start; len = total; groups; sep = !sep; past = !last_digit_end}

(* The digits of buf[off..off+len), skipping the separators inside a run.
   "4276 3800 1234 5678" gives the 16 digits the Luhn check needs. *)
(* Один массив вместо двух: прежний вариант выделял буфер на всю длину
   участка вместе с разделителями, а потом делал из него Array.sub нужного
   размера — то есть две аллокации на каждый разбор. Цифры считаются первым
   проходом, он не аллоцирует вовсе. *)
let digits_of (buf : string) (off : int) (len : int) : int array =
  let n = ref 0 in
  for i = off to off + len - 1 do
    let c = String.unsafe_get buf i in
    if c >= '0' && c <= '9' then incr n
  done;
  let out = Array.make !n 0 in
  let k = ref 0 in
  for i = off to off + len - 1 do
    let c = String.unsafe_get buf i in
    if c >= '0' && c <= '9' then (
      Array.unsafe_set out !k (Char.code c - 48);
      incr k
    )
  done;
  out

(* Shape of a run as a string like "4 6" or "2 2 6". *)
let shape_of (r : run) : string =
  Array.to_list r.groups |> List.map string_of_int |> String.concat " "
