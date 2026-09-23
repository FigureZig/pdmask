(* httpd.ml — HTTP/1.1 server on Eio.

   Requirements (spec 4.11):
   - Start line and headers up to CRLF CRLF.
   - Body by Content-Length, and MUST support Transfer-Encoding: chunked.
   - Expect: 100-continue mandatory.
   - keep-alive by default; response always with Content-Length, no chunked.
   - Idle timeout 75 s.
   - TCP_NODELAY mandatory.
   - Domain per core, each with its own listening socket with SO_REUSEPORT.
   - Accept /process and /process/.
   - Limiter for concurrent large bodies; over it -> 429 with Retry-After,
     not 413.

   The 429 guard: a counting semaphore limits how many large bodies are being
   read at once. If the semaphore is full, we answer 429 immediately. *)

open Pdmask_core

type config =
  { max_body_bytes : int;
    large_body_threshold : int;
    max_inflight_large : int;
    keepalive_idle_seconds : int
  }

type t =
  { config : config;
    router : Router.ctx;
    large_slots : int Atomic.t (* available slots for large bodies *)
  }

let create (config : config) (router : Router.ctx) : t =
  {config; router; large_slots = Atomic.make config.max_inflight_large}

(* --- HTTP parsing --- *)

type request =
  { method_ : string;
    path : string;
    headers : (string * string) list;
    body : string
  }

let lowercase (s : string) : string = String.lowercase_ascii s

let header (req : request) (name : string) : string option =
  let name = lowercase name in
  List.find_map
    (fun (k, v) ->
      if lowercase k = name then
        Some v
      else
        None
    )
    req.headers

(* Read the request line and headers. Returns (method, path, headers). *)
let read_head (reader : Eio.Buf_read.t) : string * string * (string * string) list =
  let request_line = Eio.Buf_read.line reader in
  let parts = String.split_on_char ' ' request_line in
  let method_ = List.nth parts 0 in
  let path = List.nth parts 1 in
  let rec read_headers acc =
    let line = Eio.Buf_read.line reader in
    if line = "" then
      List.rev acc
    else
      match String.index_opt line ':' with
      | Some i ->
          let k = String.sub line 0 i in
          let v = String.trim (String.sub line (i + 1) (String.length line - i - 1)) in
          read_headers ((k, v) :: acc)
      | None -> read_headers acc
  in
  let headers = read_headers [] in
  (method_, path, headers)

(* Read the body given headers. Handles Content-Length and chunked. *)
let read_body (reader : Eio.Buf_read.t) (headers : (string * string) list) : string =
  let content_length =
    List.find_map
      (fun (k, v) ->
        if lowercase k = "content-length" then
          int_of_string_opt v
        else
          None
      )
      headers
    |> Option.value ~default:0
  in
  let transfer_encoding =
    List.find_map
      (fun (k, v) ->
        if lowercase k = "transfer-encoding" then
          Some (lowercase v)
        else
          None
      )
      headers
  in
  match transfer_encoding with
  | Some te when String.contains te 'c' && String.contains te 'h' ->
      (* chunked: read chunk-size lines and chunk data until 0 *)
      let buf = Buffer.create 4096 in
      let rec read_chunks () =
        let size_line = Eio.Buf_read.line reader in
        let size = try int_of_string ("0x" ^ String.trim size_line) with _ -> 0 in
        if size = 0 then
          (* consume trailing CRLF after last chunk *)
          ignore (Eio.Buf_read.line reader)
        else
          let chunk = Eio.Buf_read.take size reader in
          Buffer.add_string buf chunk;
          (* consume CRLF after chunk data *)
          ignore (Eio.Buf_read.line reader);
          read_chunks ()
      in
      read_chunks ();
      Buffer.contents buf
  | _ ->
      if content_length > 0 then
        Eio.Buf_read.take content_length reader
      else
        ""

(* --- Response writing --- *)

let write_response (flow : _ Eio.Resource.t) (status : string) (headers : (string * string) list)
    (body : string) =
  let extra =
    List.map (fun (k, v) -> Printf.sprintf "%s: %s\r\n" k v) headers |> String.concat ""
  in
  let response =
    Printf.sprintf
      "HTTP/1.1 %s\r\nContent-Type: application/json\r\n%sContent-Length: %d\r\nConnection: keep-alive\r\n\r\n%s"
      status extra (String.length body) body
  in
  Eio.Flow.copy_string response flow

(* --- Connection handling --- *)

let handle_connection (t : t) (flow : _ Eio.Resource.t) =
  let reader = Eio.Buf_read.of_flow ~max_size:t.config.max_body_bytes flow in
  let rec loop () =
    match Eio.Buf_read.peek_char reader with
    | None -> () (* EOF *)
    | Some _ ->
        let method_, path, headers = read_head reader in
        (* Expect: 100-continue — answer 100 before reading the body. *)
        ( match
            List.find_map
              (fun (k, v) ->
                if lowercase k = "expect" then
                  Some (lowercase v)
                else
                  None
              )
              headers
          with
        | Some e when String.contains e '1' && String.contains e '0' && String.contains e '0' ->
            Eio.Flow.copy_string "HTTP/1.1 100 Continue\r\n\r\n" flow
        | _ -> ()
        );
        let body = read_body reader headers in
        let is_large = String.length body > t.config.large_body_threshold in
        let t0 = Unix.gettimeofday () in
        let status, resp_headers, body =
          if is_large then
            (* Try to acquire a large-body slot. *)
            let rec acquire () =
              let n = Atomic.get t.large_slots in
              if n > 0 && Atomic.compare_and_set t.large_slots n (n - 1) then
                true
              else if n = 0 then
                false
              else
                acquire ()
            in
            if acquire () then (
              let result =
                try Router.route t.router method_ path headers body
                with exn ->
                  Atomic.incr t.large_slots;
                  raise exn
              in
              Atomic.incr t.large_slots;
              result
            ) else
              (* Приложение B: система учитывает Retry-After и применяет
                 ожидание. Заголовок раньше был заявлен в комментарии модуля,
                 но не отдавался. *)
              ( "429 Too Many Requests",
                [("Retry-After", "1")],
                "{\"error\":\"too many large requests\"}"
              )
          else
            Router.route t.router method_ path headers body
        in
        let latency_ms = (Unix.gettimeofday () -. t0) *. 1000. in
        Metrics.incr_request t.router.metrics;
        if String.length status >= 3 && status.[0] = '4' then Metrics.incr_error t.router.metrics;
        Metrics.add_latency t.router.metrics (Int64.of_float (latency_ms *. 1e6));
        (* JSON access log: no payload values, only shape and timing.
           Отключается уровнем PDMASK_LOG=pii или off — см. Router.log_level. *)
        if Router.log_level = Router.Log_all then
          Printf.eprintf
            "{\"ts\":%.3f,\"method\":\"%s\",\"path\":\"%s\",\"status\":\"%s\",\"latency_ms\":%.3f,\"bytes\":%d}\n"
            t0 method_ path status latency_ms (String.length body);
        write_response flow status resp_headers body;
        loop ()
  in
  loop ()

(* --- Server --- *)

(* Мягкий лимит дескрипторов у самого процесса. Не ulimit родительской
   оболочки: в контейнере и под systemd лимит ставится иначе, а /proc/self
   показывает то, с чем сервис реально живёт. *)
let fd_soft_limit () : int option =
  try
    let ic = open_in "/proc/self/limits" in
    Fun.protect ~finally:(fun () -> close_in_noerr ic) @@ fun () ->
    let rec scan () =
      match input_line ic with
      | exception End_of_file -> None
      | line ->
          let head = "Max open files" in
          if
            String.length line >= String.length head
            && String.sub line 0 (String.length head) = head
          then
            match String.split_on_char ' ' line |> List.filter (fun w -> w <> "") with
            | _ :: _ :: _ :: soft :: _ -> int_of_string_opt soft
            | _ -> None
          else
            scan ()
    in
    scan ()
  with _ -> None

(* Сколько соединений держим одновременно.

   Раньше стояло 65535 без оглядки на дескрипторы, и это убивало сервис
   целиком: accept получал EMFILE, а в Eio.Net.run_server ошибка accept не
   проходит через ~on_error — тот прикрывает только обработчик, — и
   исключение выходило наружу из run_server. Процесс падал с
   «Fatal error: exception Eio.Io Unix_error (Too many open files, "accept")»,
   уже принятые соединения умирали вместе с ним. Воспроизводится на
   ulimit -n 1024 и двух тысячах соединений; при 900 всё в порядке.

   Теперь предел выводится из живого лимита: лишние клиенты ждут в очереди
   прослушивающего сокета (backlog 4096), а не роняют сервис. Запас в 128
   дескрипторов — на словари, модель, логи и служебные каналы доменов. *)
let reserved_fds = 128

let max_connections () : int =
  match Option.bind (Sys.getenv_opt "PDMASK_MAX_CONNS") int_of_string_opt with
  | Some n when n > 0 -> n
  | _ -> (
      match fd_soft_limit () with
      | Some n -> max 64 (min 65535 (n - reserved_fds))
      | None -> 65535
    )

(* Кончились дескрипторы? Eio заворачивает ошибку бэкенда в Eio.Io. *)
let fd_exhausted (exn : exn) : bool =
  match exn with
  | Unix.Unix_error ((Unix.EMFILE | Unix.ENFILE), _, _) -> true
  | Eio.Io (Eio.Exn.X (Eio_unix.Unix_error ((Unix.EMFILE | Unix.ENFILE), _, _)), _) -> true
  | _ -> false

(* Run one accept loop per core. Своя петля вместо Eio.Net.run_server: та же
   схема (общий семафор на все домены, accept_fork на каждое соединение), но
   ошибка accept не выносит процесс. Прослушивающий сокет один, домены
   разбирают его наперегонки. Обработчик трогает только потокобезопасное —
   хранилище пошардировано и под мьютексом, лексер свой на запрос. *)
let serve (t : t) (net : _ Eio.Net.t) (domain_mgr : _ Eio.Domain_manager.t) (port : int) =
  let addr = Eio.Net.Ipaddr.V4.any in
  Eio.Switch.run @@ fun sw ->
  let socket =
    Eio.Net.listen net ~sw ~reuse_addr:true ~reuse_port:true ~backlog:4096 (`Tcp (addr, port))
  in
  let cores = Domain.recommended_domain_count () in
  let limit = max_connections () in
  Printf.printf "pdmask listening on http://0.0.0.0:%d\n%!" port;
  Printf.printf "pdmask serving on %d domain(s), не более %d соединений сразу%s\n%!" cores limit
    ( match fd_soft_limit () with
    | Some n -> Printf.sprintf " (лимит дескрипторов %d)" n
    | None -> ""
    );
  let slots = Eio.Semaphore.make limit in
  let complained = Atomic.make false in
  let on_error exn = Printf.eprintf "connection error: %s\n%!" (Printexc.to_string exn) in
  let accept_loop sw =
    let rec loop () =
      Eio.Semaphore.acquire slots;
      ( match
          Eio.Net.accept_fork ~sw socket ~on_error (fun flow _client_addr ->
              Fun.protect
                (fun () -> handle_connection t flow)
                ~finally:(fun () -> Eio.Semaphore.release slots)
          )
        with
      | () -> ()
      | exception exn when fd_exhausted exn ->
          (* слот занять успели, обработчик не стартовал — вернуть вручную *)
          Eio.Semaphore.release slots;
          if not (Atomic.exchange complained true) then
            Printf.eprintf
              "accept: кончились дескрипторы, жду освобождения; уже принятые соединения обслуживаются. Поднимите ulimit -n или PDMASK_MAX_CONNS.\n%!";
          Eio_unix.sleep 0.05
      );
      loop ()
    in
    loop ()
  in
  for _ = 1 to max 0 (cores - 1) do
    Eio.Fiber.fork ~sw (fun () ->
        Eio.Domain_manager.run domain_mgr (fun () -> Eio.Switch.run @@ fun sw -> accept_loop sw)
    )
  done;
  accept_loop sw
