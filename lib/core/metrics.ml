(* metrics.ml — runtime counters for /metrics and the JSON access log.

   Thread-safe: every counter is an Atomic, so the multi-domain server can
   bump them from any domain without a lock. The counters are monotonic; the
   /metrics handler reads them and computes rates over a window.

   What is counted:
   - requests, by method+path and by status class;
   - masked PII, by type (how many spans of each type were masked);
   - evidence codes seen (how often each code fired);
   - latency: total nanoseconds and count для среднего, плюс гистограмма по
     логарифмическим корзинам для перцентилей. Организаторы меряют p50, p95,
     p99 и среднее, поэтому одного среднего мало. *)

type t =
  { mutable requests : int Atomic.t;
    mutable errors : int Atomic.t;
    mutable masked_total : int Atomic.t;
    mutable latency_ns : int64 Atomic.t;
    mutable latency_count : int Atomic.t;
    by_type : int Atomic.t array;
    by_evidence : int Atomic.t array;
    latency_hist : int Atomic.t array;
    start : float
  }

(* Гистограмма латентности: по две корзины на степень двойки микросекунд,
   то есть разрешение около полутора раз. Хранить отдельные замеры не нужно,
   сортировать нечего, и вся структура — массив атомарных счётчиков, который
   любой домен обновляет без блокировки. *)
let n_buckets = 64

let bucket_of (us : int) : int =
  if us <= 1 then
    0
  else
    let e = ref 0
    and v = ref us in
    while !v > 1 do
      v := !v lsr 1;
      incr e
    done;
    let half =
      if us land (1 lsl (!e - 1)) <> 0 then
        1
      else
        0
    in
    min (n_buckets - 1) ((!e * 2) + half)

(* Верхняя граница корзины в микросекундах — её и отдаём как значение
   перцентиля: завышать честнее, чем занижать. *)
let bucket_value (b : int) : float =
  let e = b / 2
  and half = b mod 2 in
  let base = Float.of_int (1 lsl min 62 e) in
  if half = 1 then
    base *. 2.0
  else
    base *. 1.5

let type_index (ty : Spans.ty) : int =
  match ty with
  | Spans.Fio -> 0
  | Spans.Birth_date -> 1
  | Spans.Birth_place -> 2
  | Spans.Passport -> 3
  | Spans.Citizenship -> 4
  | Spans.Issuer -> 5
  | Spans.Dept_code -> 6
  | Spans.Issue_date -> 7
  | Spans.Driver_license -> 8
  | Spans.Address -> 9
  | Spans.Email -> 10
  | Spans.Phone -> 11
  | Spans.Inn -> 12
  | Spans.Card -> 13
  | Spans.Cvv -> 14
  | Spans.Pin -> 15
  | Spans.Card_holder -> 16
  | Spans.Snils -> 17
  | Spans.Oms -> 18
  | Spans.Foreign_passport -> 19

let n_types = 20

let evidence_index (code : Evidence.code) : int =
  match code with
  | Evidence.E_CAPS -> 0
  | Evidence.E_KW_NEAR -> 1
  | Evidence.E_ROLE -> 2
  | Evidence.E_STOPCTX -> 3
  | Evidence.E_DOCCTX -> 4
  | Evidence.E_FORM -> 5
  | Evidence.E_TITLE -> 6
  | Evidence.E_PUBLIC_FULL -> 7
  | Evidence.E_PUBLIC_SURN -> 8
  | Evidence.E_EPONYM -> 9
  | Evidence.E_POSSESS -> 10
  | Evidence.E_ORGADDR -> 11
  | Evidence.E_COOCCUR -> 12
  | Evidence.E_WHOLE -> 13
  | Evidence.E_CHECKSUM -> 14

let n_evidence = 17

let create () : t =
  { requests = Atomic.make 0;
    errors = Atomic.make 0;
    masked_total = Atomic.make 0;
    latency_ns = Atomic.make 0L;
    latency_count = Atomic.make 0;
    by_type = Array.init n_types (fun _ -> Atomic.make 0);
    by_evidence = Array.init n_evidence (fun _ -> Atomic.make 0);
    latency_hist = Array.init n_buckets (fun _ -> Atomic.make 0);
    start = Unix.gettimeofday ()
  }

let incr_request (m : t) : unit = Atomic.incr m.requests

let incr_error (m : t) : unit = Atomic.incr m.errors

let add_latency (m : t) (ns : int64) : unit =
  Atomic.incr m.latency_count;
  Atomic.incr m.latency_hist.(bucket_of (Int64.to_int (Int64.div ns 1000L)));
  let rec add () =
    let cur = Atomic.get m.latency_ns in
    if Atomic.compare_and_set m.latency_ns cur (Int64.add cur ns) then
      ()
    else
      add ()
  in
  add ()

let incr_type (m : t) (ty : Spans.ty) : unit =
  Atomic.incr m.masked_total;
  Atomic.incr m.by_type.(type_index ty)

let incr_evidence (m : t) (code : Evidence.code) : unit =
  Atomic.incr m.by_evidence.(evidence_index code)

(* Счётчики за целый запрос, одной пачкой.

   Поштучный Atomic.incr на каждый спан и каждое доказательство — это около
   двенадцати тысяч атомарных операций на теле в 400 КБ, и все домены при этом
   бьют в один masked_total: кеш-линия ходит между ядрами туда-обратно тем
   чаще, чем больше ядер. Запрос считает у себя в обычных массивах и вносит
   итог один раз на тип. *)
let n_types_out = n_types

let n_evidence_out = n_evidence

let add_batch (m : t) (by_type : int array) (by_evidence : int array) : unit =
  let total = ref 0 in
  Array.iteri
    (fun i c ->
      if c > 0 then (
        total := !total + c;
        ignore (Atomic.fetch_and_add m.by_type.(i) c)
      )
    )
    by_type;
  Array.iteri
    (fun i c -> if c > 0 then ignore (Atomic.fetch_and_add m.by_evidence.(i) c))
    by_evidence;
  if !total > 0 then ignore (Atomic.fetch_and_add m.masked_total !total)

(* --- /metrics output (Prometheus text format) --- *)

let uptime (m : t) : float = Unix.gettimeofday () -. m.start

let render (m : t) : string =
  let buf = Buffer.create 512 in
  let b = Buffer.add_string buf in
  let uptime_s = uptime m in
  (* Перцентиль по гистограмме: идём по корзинам, пока не наберём нужную долю
     замеров. Возвращаем верхнюю границу корзины в миллисекундах. *)
  let percentile (p : float) : float =
    let total = Array.fold_left (fun a c -> a + Atomic.get c) 0 m.latency_hist in
    if total = 0 then
      0.
    else
      let target = int_of_float (p *. float_of_int total /. 100.) in
      let acc = ref 0
      and res = ref 0.
      and i = ref 0 in
      while !i < n_buckets && !res = 0. do
        acc := !acc + Atomic.get m.latency_hist.(!i);
        if !acc > target then res := bucket_value !i /. 1000.;
        incr i
      done;
      if !res = 0. then
        bucket_value (n_buckets - 1) /. 1000.
      else
        !res
  in
  let rps = float_of_int (Atomic.get m.requests) /. max uptime_s 1e-9 in
  let tps = float_of_int (Atomic.get m.masked_total) /. max uptime_s 1e-9 in
  let mean_latency_ms =
    let c = Atomic.get m.latency_count in
    if c = 0 then
      0.0
    else
      Int64.to_float (Atomic.get m.latency_ns) /. float_of_int c /. 1e6
  in
  b "# pdmask metrics\n";
  b (Printf.sprintf "pdmask_uptime_seconds %f\n" uptime_s);
  b (Printf.sprintf "pdmask_requests_total %d\n" (Atomic.get m.requests));
  b (Printf.sprintf "pdmask_errors_total %d\n" (Atomic.get m.errors));
  b (Printf.sprintf "pdmask_masked_total %d\n" (Atomic.get m.masked_total));
  b (Printf.sprintf "pdmask_rps %f\n" rps);
  b (Printf.sprintf "pdmask_tps %f\n" tps);
  b (Printf.sprintf "pdmask_latency_mean_ms %f\n" mean_latency_ms);
  b (Printf.sprintf "pdmask_latency_p50_ms %f\n" (percentile 50.));
  b (Printf.sprintf "pdmask_latency_p95_ms %f\n" (percentile 95.));
  b (Printf.sprintf "pdmask_latency_p99_ms %f\n" (percentile 99.));
  b "# per-type masked spans\n";
  Array.iteri
    (fun i c ->
      let name =
        match i with
        | 0 -> "fio"
        | 1 -> "birth_date"
        | 2 -> "birth_place"
        | 3 -> "passport"
        | 4 -> "citizenship"
        | 5 -> "issuer"
        | 6 -> "dept_code"
        | 7 -> "issue_date"
        | 8 -> "driver_license"
        | 9 -> "address"
        | 10 -> "email"
        | 11 -> "phone"
        | 12 -> "inn"
        | 13 -> "card"
        | 14 -> "cvv"
        | 15 -> "pin"
        | 16 -> "card_holder"
        | 17 -> "snils"
        | 18 -> "oms"
        | 19 -> "foreign_passport"
        | _ -> "unknown"
      in
      b (Printf.sprintf "pdmask_masked_%s %d\n" name (Atomic.get c))
    )
    m.by_type;
  Buffer.contents buf
