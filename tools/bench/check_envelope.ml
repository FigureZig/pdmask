(* check_envelope.ml — круговой рейс конверта: запечатать и открыть.

   Написан после того, как /unmask начал отказывать примерно в половине
   случаев без всякой закономерности во времени. Причина была в nonce,
   собранном через Bytes.create: неинициализированные первые четыре байта
   совпадали у запечатывания и открытия далеко не всегда. Через HTTP такое
   не ловится — там мешают одноразовые коды и тридцатисекундные окна, —
   поэтому проверка живёт на уровне библиотеки.

     dune exec tools/bench/check_envelope.exe *)

open Pdmask_core

let () = Mirage_crypto_rng_unix.use_default ()

let k_master = "pdmask-test-master-key-0000000000000000"

let rounds = try int_of_string Sys.argv.(1) with _ -> 2000

(* Один рейс: своя случайная соль, свой набор записей. *)
let trip (i : int) : (unit, string) result =
  let system =
    if i mod 2 = 0 then
      "demo"
    else
      "crm"
  in
  let payload_id = Printf.sprintf "req-%d" i in
  let salt = Mirage_crypto_rng.generate 32 in
  let k_sys = Envelope.system_key k_master system in
  let k_req = Envelope.request_key k_sys salt in
  let exp = Int64.add (Int64.of_float (Unix.gettimeofday ())) 300L in
  let values =
    [ (Spans.Fio, "Иванов Иван Иванович");
      (Spans.Passport, Printf.sprintf "4509 %06d" (i mod 1000000));
      (Spans.Phone, "+7 916 123-45-67")
    ]
  in
  let records =
    List.mapi
      (fun k (ty, v) ->
        let label = Printf.sprintf "[%s_%d]" (Spans.ty_name ty) (k * 7) in
        Envelope.seal_record k_req payload_id ty k exp label v
      )
      values
  in
  let env = {Envelope.salt; exp; records} in
  (* через заголовок: строка — это то, что реально уезжает клиенту *)
  match Envelope.of_header (Envelope.to_header env) with
  | None -> Error "заголовок не разобрался"
  | Some back ->
      if back.Envelope.salt <> salt then
        Error "соль не пережила base64"
      else if back.Envelope.exp <> exp then
        Error "срок не пережил base64"
      else
        let k_req' =
          Envelope.request_key (Envelope.system_key k_master system) back.Envelope.salt
        in
        let rec go k = function
          | [] -> Ok ()
          | r :: rest -> (
              match Envelope.open_record back k_req' payload_id r with
              | None -> Error (Printf.sprintf "запись %s не открылась" r.Envelope.label)
              | Some v ->
                  let _, want = List.nth values k in
                  if v <> want then
                    Error (Printf.sprintf "запись %s открылась не тем" r.Envelope.label)
                  else
                    go (k + 1) rest
            )
        in
        go 0 back.Envelope.records

(* Чужая система не должна открывать конверт: ключ выводится из её имени. *)
let cross_system () : bool =
  let salt = Mirage_crypto_rng.generate 32 in
  let k_req = Envelope.request_key (Envelope.system_key k_master "demo") salt in
  let exp = Int64.add (Int64.of_float (Unix.gettimeofday ())) 300L in
  let r = Envelope.seal_record k_req "req" Spans.Fio 0 exp "[fio_0]" "Иванов Иван Иванович" in
  let env = {Envelope.salt; exp; records = [r]} in
  let k_other = Envelope.request_key (Envelope.system_key k_master "crm") salt in
  Envelope.open_record env k_other "req" r = None

(* Истёкший конверт не открывается. *)
let expired_rejected () : bool =
  let now = Int64.of_float (Unix.gettimeofday ()) in
  let env = {Envelope.salt = Mirage_crypto_rng.generate 32; exp = Int64.sub now 1L; records = []} in
  Envelope.expired env now

let () =
  let bad = ref 0 in
  let first = ref "" in
  for i = 1 to rounds do
    match trip i with
    | Ok () -> ()
    | Error why ->
        incr bad;
        if !first = "" then first := Printf.sprintf "рейс %d: %s" i why
  done;
  Printf.printf "круговых рейсов: %d, не открылось: %d\n" rounds !bad;
  if !bad > 0 then Printf.printf "первый отказ — %s\n" !first;
  Printf.printf "чужая система не открывает: %b\n" (cross_system ());
  Printf.printf "истёкший отвергается:      %b\n" (expired_rejected ());
  if !bad > 0 || (not (cross_system ())) || not (expired_rejected ()) then exit 1
