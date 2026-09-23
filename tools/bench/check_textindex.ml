(* Временная проверка: индекс против наивной сверки на случайных входах. *)
open Pdmask_core

let contains h n =
  let lh = String.length h
  and ln = String.length n in
  if ln = 0 then
    true
  else if ln > lh then
    false
  else
    let r = ref false in
    for i = 0 to lh - ln do
      if (not !r) && String.sub h i ln = n then r := true
    done;
    !r

let () =
  Eio_main.run @@ fun _ ->
  let keys = Dictload.load_bank_offices "dicts" in
  let idx = Textindex.of_keys keys in
  (* Эталон повторяет и отсечку по длине: слишком короткий ключ является
     подстрокой почти любого адреса отделения, и Textindex сознательно
     отвечает на такие «нет» — иначе спан из одной цифры получал бы E_ORGADDR,
     то есть запрет маскирования. *)
  let naive k =
    String.length k >= Textindex.min_query
    && List.exists (fun o -> contains o k || contains k o) keys
  in
  let arr = Array.of_list keys in
  Random.self_init ();
  let bad = ref 0
  and total = ref 0 in
  let check k =
    incr total;
    if Textindex.matches idx k <> naive k then (
      incr bad;
      if !bad <= 5 then Printf.printf "РАСХОЖДЕНИЕ на %S\n" k
    )
  in
  let alph = "абвгдеёжзиклмнопрстуфхцчшщыэюя0123456789 ,.-" in
  (* случайные строки *)
  for _ = 1 to 4000 do
    let n = 1 + Random.int 80 in
    check (String.init n (fun _ -> alph.[Random.int (String.length alph)]))
  done;
  (* случайные подстроки настоящих ключей *)
  for _ = 1 to 4000 do
    let k = arr.(Random.int (Array.length arr)) in
    let l = String.length k in
    if l > 0 then
      let a = Random.int l in
      let b = a + Random.int (l - a + 1) in
      check (String.sub k a (b - a))
  done;
  (* настоящие ключи с обвязкой с обеих сторон *)
  for _ = 1 to 2000 do
    let k = arr.(Random.int (Array.length arr)) in
    let pad n = String.init n (fun _ -> alph.[Random.int (String.length alph)]) in
    check (pad (Random.int 20) ^ k ^ pad (Random.int 20))
  done;
  List.iter check
    [""; String.make 200 (Char.chr 0xd0); String.concat "" (List.init 50 (fun _ -> "москва"))];
  List.iter check keys;
  Printf.printf "ключей %d, проверок %d, расхождений %d\n" (List.length keys) !total !bad
