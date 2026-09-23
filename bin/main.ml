(* pdmask — main entry point.

   Subcommands (spec 3):
   - serve   run the HTTP server (default)
   - lex     run the lexer on a file
   - dict    dictionary stats
   - otp     print the current one-time code for /unmask and /admin/reload
   - eval    run the reference dataset (M5, not implemented)
   - explain explain spans for a payload; the HTTP route POST /explain is live,
             the subcommand is not *)

let version = "0.1.0-m4"

open Pdmask_core
open Pdmask_http

(* Load the dictionaries from dicts/. The public persons come back alongside
   the dictionary: evidence.ml matches full names against their forms, while
   their surnames go into the dictionary itself (see Dictload.load). *)
let load_dicts () : Dict.t * Dictload.person list =
  let dict = Dict.create () in
  let persons = Dictload.load_public_persons "dicts" in
  Dictload.load dict "dicts" persons;
  (dict, persons)

(* Минимальное число записей, ниже которого словарь считается незагруженным.
   Dictload намеренно глотает отсутствие файла и возвращает пустой список,
   чтобы частичный набор справочников не ронял сервис. Но если не загрузилось
   ничего, сервис будет отвечать 200 и возвращать payload как есть — то есть
   молча выпускать наружу все персональные данные. Такое состояние опаснее
   отказа: снаружи оно неотличимо от исправной работы. Поэтому отказ явный. *)
let min_dict_entries = 100

let check_dicts (dict : Dict.t) : unit =
  let n = Dict.size dict in
  if n < min_dict_entries then (
    Printf.eprintf
      "pdmask: словарь пуст (%d записей при минимуме %d).\nКаталог dicts/ не найден или не прочитан. Сервис в таком состоянии\nне маскирует ничего и отвечает 200 — это утечка, а не деградация.\nЗапускать из каталога, где лежит dicts/, либо смонтировать его в образ.\n%!"
      n min_dict_entries;
    exit 3
  )

let serve () =
  Mirage_crypto_rng_unix.use_default ();
  let config = Config.load "config/systems.yaml" in
  let store =
    Store.create ~ttl:config.limits.store_ttl_seconds ~max_bytes:config.limits.store_max_bytes ()
  in
  let dict, persons = load_dicts () in
  let public_forms = Dictload.public_forms persons in
  (* Последовательная модель необязательна: нет файла — сервис работает на
     одних правилах, только с меньшей полнотой. *)
  let seqmodel = Seqmodel.load "models/seqmodel.bin" in
  Printf.printf "pdmask seqmodel: %s\n%!"
    ( match seqmodel with
    | Some _ -> "models/seqmodel.bin загружена"
    | None -> "не найдена, работаем на правилах"
    );
  check_dicts dict;
  let bank_index = Textindex.of_keys (Dictload.load_bank_offices "dicts") in
  let k_master =
    Sys.getenv_opt "PDMASK_MASTER_KEY"
    |> Option.value ~default:"pdmask-dev-master-key-0000000000000000"
  in
  let otp_secret =
    Sys.getenv_opt "PDMASK_OTP_SECRET"
    |> Option.value ~default:"pdmask-dev-otp-secret-0000000000000000"
  in
  let admin_password =
    Sys.getenv_opt "PDMASK_ADMIN_PASSWORD" |> Option.value ~default:"pdmask-admin"
  in
  let router =
    { Router.store;
      dict;
      bank_index;
      public_forms;
      seqmodel;
      config = Atomic.make config;
      metrics = Metrics.create ();
      k_master;
      otp = Otp.create otp_secret;
      admin_password
    }
  in
  let httpd_config =
    { Httpd.max_body_bytes = config.limits.max_body_bytes;
      large_body_threshold = config.limits.large_body_threshold;
      max_inflight_large = config.limits.max_inflight_large;
      keepalive_idle_seconds = config.limits.keepalive_idle_seconds
    }
  in
  let httpd = Httpd.create httpd_config router in
  let port = int_of_string (Sys.getenv_opt "PORT" |> Option.value ~default:"8080") in
  Printf.printf "pdmask %s starting\n%!" version;
  Eio_main.run @@ fun env -> Httpd.serve httpd (Eio.Stdenv.net env) (Eio.Stdenv.domain_mgr env) port

(* --- lex subcommand --- *)

let kind_name (k : Lexer.kind) : string =
  match k with
  | Lexer.WORD_CYR -> "cyr"
  | Lexer.WORD_LAT -> "lat"
  | Lexer.DIGITS -> "digits"
  | Lexer.EMAIL -> "email"
  | Lexer.SEP -> "sep"
  | Lexer.PUNCT -> "punct"
  | Lexer.SPACE -> "space"

let lex_file (path : string) (stats : bool) : unit =
  let content =
    match In_channel.with_open_bin path (fun ic -> In_channel.input_all ic) with
    | exception _ ->
        Printf.eprintf "lex: cannot read %s\n%!" path;
        exit 1
    | c -> c
  in
  let dict, _ = load_dicts () in
  let toks = Lexer.create () in
  let t0 = Unix.gettimeofday () in
  Lexer.lex toks dict content;
  let t1 = Unix.gettimeofday () in
  let elapsed_ms = (t1 -. t0) *. 1000.0 in
  let bytes = String.length content in
  let throughput =
    if elapsed_ms > 0.0 then
      float_of_int bytes /. elapsed_ms /. 1000.0
    else
      0.0
  in
  if stats then (
    let count kind =
      let n = ref 0 in
      for i = 0 to toks.n - 1 do
        if toks.kind.(i) = kind then incr n
      done;
      !n
    in
    let cyr = count Lexer.WORD_CYR in
    let lat = count Lexer.WORD_LAT in
    let digits = count Lexer.DIGITS in
    let email = count Lexer.EMAIL in
    (* dict hits *)
    let hits flag =
      let n = ref 0 in
      for i = 0 to toks.n - 1 do
        if toks.flags.(i) land flag <> 0 then incr n
      done;
      !n
    in
    Printf.printf "bytes=%d  tokens=%d  cyr=%d lat=%d digits=%d email=%d\n" bytes toks.n cyr lat
      digits email;
    Printf.printf "dict hits: NAME=%d SURN=%d PATR=%d GEO=%d\n" (hits Dict.Flag.name)
      (hits Dict.Flag.surn) (hits Dict.Flag.patr) (hits Dict.Flag.geo);
    Printf.printf "elapsed=%.2f ms   throughput=%.1f MB/s\n" elapsed_ms throughput
  ) else
    for i = 0 to toks.n - 1 do
      Printf.printf "[%s] %s\n"
        (kind_name toks.kind.(i))
        (String.sub content toks.start.(i) toks.len.(i))
    done

(* --- dict subcommand --- *)

let dict_stats () : unit =
  let dict, _ = load_dicts () in
  Printf.printf "dictionary entries: %d\n" (Dict.size dict)

(* --- otp subcommand --- *)

(* Печатает текущий одноразовый код. Без этой подкоманды /unmask и
   /admin/reload невозможно проверить руками: код считается по RFC 6238 от
   секрета, который живёт в переменной окружения и в репозиторий не попадает.
   Секрет берётся тот же, что использует сервис, поэтому код подходит к
   запущенному рядом экземпляру. *)
let otp_code () : unit =
  let secret =
    Sys.getenv_opt "PDMASK_OTP_SECRET"
    |> Option.value ~default:"pdmask-dev-otp-secret-0000000000000000"
  in
  let t = Otp.create secret in
  let now = Int64.of_float (Unix.gettimeofday ()) in
  let step = Int64.div now 30L in
  let left = 30 - Int64.to_int (Int64.rem now 30L) in
  Printf.printf "%08d\n" (Otp.code_at t step);
  Printf.eprintf "действует ещё %d с (шаг 30 с, допуск +/-1 шаг)\n%!" left

let () =
  let args = Sys.argv in
  let cmd =
    if Array.length args > 1 then
      args.(1)
    else
      "serve"
  in
  match cmd with
  | "serve" -> serve ()
  | "lex" -> (
      let rec parse i file stats =
        if i >= Array.length args then
          (file, stats)
        else
          match args.(i) with
          | "--file" when i + 1 < Array.length args -> parse (i + 2) (Some args.(i + 1)) stats
          | "--stats" -> parse (i + 1) file true
          | _ -> parse (i + 1) file stats
      in
      let file, stats = parse 2 None false in
      match file with
      | Some f -> lex_file f stats
      | None ->
          Printf.eprintf "usage: pdmask lex --file <path> [--stats]\n%!";
          exit 2
    )
  | "dict" -> dict_stats ()
  | "otp" -> otp_code ()
  | "eval" | "explain" ->
      Printf.eprintf "%s: not implemented yet\n%!" cmd;
      exit 1
  | _ ->
      Printf.eprintf "usage: pdmask {serve|lex|dict|otp|eval|explain}\n%!";
      exit 2
