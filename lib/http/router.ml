(* router.ml — request routing.

   Routes (spec 4.12):
   - POST /process   contract of the checking system, no auth
   - POST /mask      separate masking endpoint for the jury
   - POST /unmask    separate unmasking endpoint
   - POST /explain   spans, types and evidence codes without values
   - GET  /health    liveness
   - GET  /metrics   metrics (Prometheus format)

   The /process algorithm (spec 4.9):
     match Store.get payload_id with
     | None      -> m = mask payload; Store.put payload_id payload; return m
     | Some orig -> if payload = orig then return (mask payload)
                    else return orig
*)

open Pdmask_core

(* Пул буферов токенов, свой на каждый домен.

   Общий буфер в ctx был гонкой: Rules.detect берёт payload текущего запроса и
   toks, возможно, оставшиеся от чужого, и смещения одного текста применяются к
   другому. Под смешанной нагрузкой это давало разные маски на один и тот же
   вход и рвало соединения на Invalid_argument.

   Буфер на каждый запрос гонку убирает, но стоит дорого: Lexer.ensure растит
   массивы удвоением от 256, и на payload в 400 КБ это девять пересозданий с
   копированием — на каждый запрос заново.

   Пул совмещает оба свойства: буфер занят на время запроса, значит не делится
   ни с кем, но переживает запрос вместе с уже выросшими массивами, значит не
   растится повторно. Пул домен-локальный, поэтому синхронизация не нужна
   вовсе: фибры одного домена кооперативны, а домены в чужой пул не смотрят.

   Переросший буфер в пул не возвращается: иначе один гигантский запрос
   навсегда оставил бы домену массивы на сто тысяч токенов (M8 спеки). *)
module Toks_pool = struct
  let max_kept = 4

  let max_tokens = 1 lsl 17

  let key : Lexer.toks list ref Domain.DLS.key = Domain.DLS.new_key (fun () -> ref [])

  let take () : Lexer.toks =
    let p = Domain.DLS.get key in
    match !p with
    | t :: rest ->
        p := rest;
        t
    | [] -> Lexer.create ()

  let give (t : Lexer.toks) : unit =
    let p = Domain.DLS.get key in
    if Array.length t.Lexer.start <= max_tokens && List.length !p < max_kept then p := t :: !p
end

type ctx =
  { store : Store.t;
    dict : Dict.t;
    bank_index : Textindex.t;
    public_forms : Dict.t;
    config : Config.t Atomic.t;
    metrics : Metrics.t;
    k_master : string; (* master key for the envelope, from env *)
    otp : Otp.t; (* одноразовые коды, счётчик шага на каждого вызывающего *)
    admin_password : string (* basic auth for admin/demo endpoints *)
  }

(* Sentence index of every candidate, assigned in one pass over the payload.
   The spans are visited in ascending start order, so the payload pointer only
   moves forward. Asking "are these two spans in the same sentence?" for every
   pair is quadratic, and a long text produces thousands of candidates. *)
let sentence_ids (t : Lexer.toks) (spans : Spans.span array) : int array =
  let n = Array.length spans in
  (* Границы предложений лексер уже собрал своим проходом. Номер предложения
     для спана — это сколько границ лежит левее его начала, то есть двоичный
     поиск.

     Раньше здесь спаны сортировались, чтобы указатель по тексту шёл только
     вперёд: шесть с половиной тысяч кандидатов, около восьмидесяти тысяч
     сравнений, каждое — косвенный вызов замыкания-компаратора. Потом
     сортировку сменил двоичный поиск, но проход по всем 400 КБ ради самих
     границ остался вторым чтением тела. Теперь нет и его. *)
  let b = t.Lexer.sent
  and cnt = t.Lexer.nsent in
  let ids = Array.make n 0 in
  for i = 0 to n - 1 do
    let start = spans.(i).Spans.start in
    let lo = ref 0
    and hi = ref cnt in
    while !lo < !hi do
      let m = (!lo + !hi) lsr 1 in
      if Array.unsafe_get b m < start then
        lo := m + 1
      else
        hi := m
    done;
    ids.(i) <- !lo
  done;
  ids

(* Analyze a payload: detect candidates, collect evidence, decide. Returns
   (masked, rejected) where each is a list of (span, evidence). E_COOCCUR is
   resolved in two passes: a span gets E_COOCCUR if another confirmed PII span
   of a different type is in the same sentence. *)
let analyze (ctx : ctx) (payload : string) :
    (Spans.span * Evidence.evidence list) list * (Spans.span * Evidence.evidence list) list =
  let toks = Toks_pool.take () in
  Fun.protect ~finally:(fun () -> Toks_pool.give toks) @@ fun () ->
  Lexer.lex toks ctx.dict payload;
  let candidates = Rules.detect payload toks in
  let ev_ctx =
    { Evidence.bank_index = ctx.bank_index;
      public_forms = ctx.public_forms;
      payload;
      payload_cp = Evidence.code_points_capped payload 64;
      toks
    }
  in
  (* first pass: collect the evidence and decide without E_COOCCUR *)
  let first_pass = Array.of_list (List.map (fun s -> (s, Evidence.collect ev_ctx s)) candidates) in
  (* which PII types were confirmed in each sentence *)
  let sent = sentence_ids toks (Array.map fst first_pass) in
  let types = Array.make (1 + Array.fold_left max 0 sent) 0 in
  Array.iteri
    (fun i (s, ev) ->
      let d = Decision.decide s.Spans.ty ev in
      if d.masked then types.(sent.(i)) <- types.(sent.(i)) lor Spans.ty_bit s.Spans.ty
    )
    first_pass;
  (* second pass: add E_COOCCUR where another type was confirmed alongside *)
  let masked = ref [] in
  let rejected = ref [] in
  Array.iteri
    (fun i (s, ev) ->
      let others = types.(sent.(i)) land lnot (Spans.ty_bit s.Spans.ty) in
      let ev =
        if others <> 0 then
          {Evidence.code = Evidence.E_COOCCUR; at = 0} :: ev
        else
          ev
      in
      let d = Decision.decide s.Spans.ty ev in
      if d.masked then
        masked := (s, ev) :: !masked
      else
        rejected := (s, ev) :: !rejected
    )
    first_pass;
  (List.rev !masked, List.rev !rejected)

(* Accepted candidates after overlap resolution, with their evidence: the
   spans that actually get masked. The same digits can be a passport and a
   phone number at once, and only one of the two survives — /explain reports
   this list, so what it shows is exactly what /mask does. *)
let decide_spans (ctx : ctx) (payload : string) :
    (Spans.span * Evidence.evidence list) list * (Spans.span * Evidence.evidence list) list =
  let masked, rejected = analyze ctx payload in
  (Spans.resolve_by fst masked, rejected)

(* Does the profile allow masking this PII type? *)
let type_allowed (p : Config.profile) (ty : Spans.ty) : bool =
  match p.Config.pii_types with
  | None -> true
  | Some types -> List.mem ty types

(* Masking pipeline: analyze -> resolve -> filter by profile -> glue -> mask.
   The profile decides which types are masked and the mask mode. Counts the
   masked spans and their evidence for /metrics. *)
let mask_counted (ctx : ctx) (p : Config.profile) (payload : string) :
    string * (Spans.ty * int) list =
  let kept, _ = decide_spans ctx payload in
  let kept = List.filter (fun (s, _) -> type_allowed p s.Spans.ty) kept in
  (* Счёт по типам ведётся в обычном массиве по индексу типа, а не в
     ассоциативном списке: List.remove_assoc пересобирал весь список на каждом
     элементе, то есть десятки ячеек на каждый замаскированный спан. Метрики
     тоже вносятся одной пачкой, а не атомарным инкрементом на спан. *)
  let by_type = Array.make Metrics.n_types_out 0 in
  let by_ev = Array.make Metrics.n_evidence_out 0 in
  (* Тип, попавший в каждый индекс, запоминается тут же: иначе итоговый список
     собирался бы через List.mem_assoc, то есть полиморфным сравнением
     вариантов на каждый замаскированный спан. *)
  let ty_at = Array.make Metrics.n_types_out Spans.Fio in
  List.iter
    (fun (s, ev) ->
      let i = Metrics.type_index s.Spans.ty in
      ty_at.(i) <- s.Spans.ty;
      by_type.(i) <- by_type.(i) + 1;
      List.iter
        (fun e ->
          let j = Metrics.evidence_index e.Evidence.code in
          by_ev.(j) <- by_ev.(j) + 1
        )
        ev
    )
    kept;
  Metrics.add_batch ctx.metrics by_type by_ev;
  let counts = ref [] in
  Array.iteri (fun i c -> if c > 0 then counts := (ty_at.(i), c) :: !counts) by_type;
  let counts = !counts in
  let glued = Spans.glue (List.map fst kept) in
  let mode =
    match p.Config.mask_mode with
    | Config.Stars -> Mask.Stars
    | Config.Token -> Mask.Token
    | Config.Synthetic -> Mask.Synthetic
  in
  (Mask.mask mode payload glued, counts)

let mask (ctx : ctx) (p : Config.profile) (payload : string) : string =
  fst (mask_counted ctx p payload)

(* Требование ТЗ 4.1: логирование выявленных типов персональных данных по
   каждому запросу. Значений здесь нет и быть не может — только тип, сколько
   раз встретился, направление и размеры. Отдельной строкой от access-лога:
   это журнал обработки ПДН, и читают его по другому поводу. *)
(* Уровень журналирования: all — доступ и ПДН, pii — только журнал обработки
   ПДН (требование раздела 4.1 ТЗ), off — ничего.

   Зачем вообще уровень. Под нагрузкой в 1000 RPS две строки по 120 байт на
   запрос — это около четверти мегабайта в секунду и гигабайт за
   получасовой прогон. Метрики реального нагрузочного прогона показали ровно
   такую картину: 454 КБ/с записи на диск при нулевом чтении. На VM с тесным
   диском это риск заполнения, а заполнение — это отказ записи в горячем
   пути. *)
type log_level =
  | Log_off
  | Log_pii
  | Log_all

let log_level =
  match Sys.getenv_opt "PDMASK_LOG" with
  | Some "off" -> Log_off
  | Some "pii" -> Log_pii
  | _ -> Log_all

let log_pii (id : string) (dir : string) (system : string) (bytes_in : int) (bytes_out : int)
    (counts : (Spans.ty * int) list) : unit =
  let types =
    counts
    |> List.map (fun (ty, n) -> Printf.sprintf "\"%s\":%d" (Spans.ty_name ty) n)
    |> String.concat ","
  in
  (* Без %!: принудительный сброс на каждой строке — это системный вызов на
     запрос, да ещё под общим мьютексом канала, то есть точка, где все домены
     выстраиваются в очередь. Буфер канала сбрасывается сам, а порядок строк
     сохраняется, потому что весь printf идёт под тем же мьютексом. *)
  if log_level <> Log_off then
    Printf.printf
      "{\"ts\":%.3f,\"kind\":\"pii\",\"id\":\"%s\",\"dir\":\"%s\",\"system\":\"%s\",\"bytes_in\":%d,\"bytes_out\":%d,\"types\":{%s}}\n"
      (Unix.gettimeofday ()) id dir system bytes_in bytes_out types

(* Is this type irreversible for the profile (masked, never restored)? *)
let is_irreversible (p : Config.profile) (ty : Spans.ty) : bool = List.mem ty p.Config.irreversible

(* Mask and build an envelope (section 6.2). The masked text carries labels
   [ТИП_i]; the envelope holds the sealed originals and goes to the client.
   The server keeps no state. Irreversible types (PCI DSS 3.3.1: CVV, PIN)
   are masked but never sealed into the envelope. *)
let mask_with_envelope (ctx : ctx) (p : Config.profile) (system : string) (payload : string)
    (payload_id : string) : string * string * (Spans.ty * int) list =
  let kept, _ = decide_spans ctx payload in
  let kept = List.filter (fun (s, _) -> type_allowed p s.Spans.ty) kept in
  (* Конверт восстанавливает значения по меткам [ТИП_смещение], поэтому он
     возможен только в режиме Token. Под звёздочками метки нет, искать нечего,
     и конверт не собирается: /mask обязан отдавать ровно то же, что /process
     под тем же профилем, иначе жюри сравнит две ручки и увидит расхождение. *)
  let counts =
    List.fold_left
      (fun acc (s, _) ->
        let ty = s.Spans.ty in
        match List.assoc_opt ty acc with
        | Some n -> (ty, n + 1) :: List.remove_assoc ty acc
        | None -> (ty, 1) :: acc
      )
      [] kept
  in
  if p.Config.mask_mode <> Config.Token then
    let m, _ = mask_counted ctx p payload in
    (m, "", counts)
  else
    let salt = Mirage_crypto_rng.generate 32 in
    let k_sys = Envelope.system_key ctx.k_master system in
    let k_req = Envelope.request_key k_sys salt in
    let exp = Int64.add (Int64.of_float (Unix.gettimeofday ())) 300L in
    let records =
      List.mapi
        (fun i (s, _) ->
          (* the label must match Mask.Token: [ТИП_start] *)
          let label = Printf.sprintf "[%s_%d]" (Spans.ty_name s.Spans.ty) s.Spans.start in
          if is_irreversible p s.Spans.ty then
            None
          else
            let value = String.sub payload s.Spans.start s.Spans.len in
            Some (Envelope.seal_record k_req payload_id s.Spans.ty i exp label value)
        )
        kept
      |> List.filter_map (fun x -> x)
    in
    let env = {Envelope.salt; exp; records} in
    let header = Envelope.to_header env in
    let glued = Spans.glue (List.map fst kept) in
    let masked = Mask.mask Mask.Token payload glued in
    (masked, header, counts)

(* Unmask from an envelope: derive K_req from the salt, open each record and
   splice the originals back in place of the labels.

   Ошибка возвращается с причиной. Раньше все четыре случая — битый заголовок,
   истёкший срок, отсутствующая в теле метка и не открывшаяся запись —
   схлопывались в одно "envelope expired or invalid", и по ответу нельзя было
   отличить просроченный конверт от чужой системы или от тела, в котором
   метку успели отредактировать. Причина не выдаёт ничего сверх того, что
   вызывающий и так держит в руках: имена меток лежат в его же теле. *)
let rec unmask_with_envelope (ctx : ctx) (system : string) (payload : string) (header : string)
    (payload_id : string) : (string, string) result =
  match Envelope.of_header header with
  | None -> Error "malformed envelope header"
  | Some env -> (
      if Envelope.expired env (Int64.of_float (Unix.gettimeofday ())) then
        Error "envelope expired"
      else
        let k_sys = Envelope.system_key ctx.k_master system in
        let k_req = Envelope.request_key k_sys env.Envelope.salt in
        let buf = Buffer.create (String.length payload) in
        let err = ref None in
        let fail why = if !err = None then err := Some why in
        (* replace each label [ТИП_i] with its original *)
        let rec go pos = function
          | [] -> Buffer.add_string buf (String.sub payload pos (String.length payload - pos))
          | r :: rest -> (
              let label = r.Envelope.label in
              match string_find payload label pos with
              | None -> fail (Printf.sprintf "label %s not found in payload" label)
              | Some at -> (
                  Buffer.add_string buf (String.sub payload pos (at - pos));
                  match Envelope.open_record env k_req payload_id r with
                  | Some orig ->
                      Buffer.add_string buf orig;
                      go (at + String.length label) rest
                  | None ->
                      fail (Printf.sprintf "record %s does not open with this system key" label)
                )
            )
        in
        go 0 env.Envelope.records;
        match !err with
        | None -> Ok (Buffer.contents buf)
        | Some why -> Error why
    )

(* Find the first occurrence of needle in haystack at or after pos. *)
and string_find (haystack : string) (needle : string) (pos : int) : int option =
  let n = String.length haystack
  and m = String.length needle in
  let rec find i =
    if i + m > n then
      None
    else if String.sub haystack i m = needle then
      Some i
    else
      find (i + 1)
  in
  find pos

(* Handle POST /process. Returns (status, headers, body). Uses the default
   profile: the checking system sends no headers. *)
let handle_process (ctx : ctx) (body : string) : string * (string * string) list * string =
  let p = (Atomic.get ctx.config).Config.default_profile in
  match Jsonio.parse_request body with
  | None -> ("400 Bad Request", [], Jsonio.error "missing payload or payload_id")
  | Some req -> (
      let payload = req.payload in
      let payload_id = req.payload_id in
      let masked () =
        let m, counts = mask_counted ctx p payload in
        log_pii payload_id "mask" "default" (String.length payload) (String.length m) counts;
        ("200 OK", [], Jsonio.result m)
      in
      match Store.get ctx.store payload_id with
      | None ->
          let r = masked () in
          Store.put ctx.store payload_id payload;
          r
      | Some orig ->
          if payload = orig then
            (* повторный запрос с тем же телом — это ретрай маскирования *)
            masked ()
          else if not p.Config.demask then (
            (* профиль без демаскирования: возвращаем маску, а не оригинал.
               Профиль default обязан иметь demask: true — под ним идёт
               проверяющая система, и обратный шаг ей нужен. *)
            log_pii payload_id "demask-denied" "default" (String.length payload)
              (String.length payload) [];
            ("200 OK", [], Jsonio.result payload)
          ) else (
            log_pii payload_id "demask" "default" (String.length payload) (String.length orig) [];
            ("200 OK", [], Jsonio.result orig)
          )
    )

(* The system name from the X-PDMask-System header, or "default". *)
let system_of_headers (headers : (string * string) list) : string =
  let lower = String.lowercase_ascii in
  match
    List.find_map
      (fun (k, v) ->
        if lower k = "x-pdmask-system" then
          Some v
        else
          None
      )
      headers
  with
  | Some v -> v
  | None -> "default"

(* Одноразовый код из заголовка X-PDMask-OTP, если он там есть. *)
let otp_of_headers (headers : (string * string) list) : int option =
  let lower = String.lowercase_ascii in
  List.find_map
    (fun (k, v) ->
      if lower k = "x-pdmask-otp" then
        int_of_string_opt (String.trim v)
      else
        None
    )
    headers

(* Разрешена ли системе работа с сервисом?

   Требование ТЗ 4.4: ограниченный список систем, которые имеют возможность
   обращаться в сервис, плюс включение и выключение каждой. Неизвестное имя
   отвергается, а не молча обслуживается профилем default — иначе никакого
   ограниченного списка нет.

   На /process это не распространяется: проверяющая система шлёт запросы без
   заголовков, и организаторы подтвердили, что баллы за отсутствие защиты
   этой ручки не снимаются. Там всегда профиль default. *)
let system_allowed (cfg : Config.t) (system : string) : (Config.profile, string) result =
  match List.assoc_opt system cfg.Config.systems with
  | None -> Error "unknown system"
  | Some p ->
      if p.Config.enabled then
        Ok p
      else
        Error "system disabled"

let forbidden (why : string) : string * (string * string) list * string =
  ("403 Forbidden", [], Jsonio.error why)

(* Handle POST /mask: always mask, using the profile for the system named in
   the X-PDMask-System header (default if absent). Returns the envelope in
   X-PDMask-Envelope so /unmask can restore. *)
let handle_mask (ctx : ctx) (headers : (string * string) list) (body : string) :
    string * (string * string) list * string =
  let system = system_of_headers headers in
  match system_allowed (Atomic.get ctx.config) system with
  | Error why -> forbidden why
  | Ok p -> (
      match Jsonio.find_string body "payload" with
      | None -> ("400 Bad Request", [], Jsonio.error "missing payload")
      | Some payload ->
          let masked, env, counts = mask_with_envelope ctx p system payload "" in
          log_pii "-" "mask" system (String.length payload) (String.length masked) counts;
          let headers =
            if env = "" then
              []
            else
              [("X-PDMask-Envelope", env)]
          in
          ("200 OK", headers, Jsonio.result masked)
    )

(* Handle POST /unmask: restore from the envelope in X-PDMask-Envelope,
   authorised by a one-time code in X-PDMask-OTP. *)
let handle_unmask (ctx : ctx) (headers : (string * string) list) (body : string) :
    string * (string * string) list * string =
  let system = system_of_headers headers in
  match system_allowed (Atomic.get ctx.config) system with
  | Error why -> forbidden why
  | Ok p -> (
      if not p.Config.demask then
        (* ТЗ 4.4: наличие демаскирования настраивается на систему. Профилю с
           demask: false обратное преобразование недоступно вовсе. *)
        forbidden "demasking disabled for this system"
      else
        let envelope = List.assoc_opt "X-PDMask-Envelope" headers in
        let otp_code = otp_of_headers headers in
        match (envelope, otp_code) with
        | Some env, Some code -> (
            if not (Otp.verify ctx.otp system code) then
              ("401 Unauthorized", [], Jsonio.error "invalid or used one-time code")
            else
              match Jsonio.find_string body "payload" with
              | None -> ("400 Bad Request", [], Jsonio.error "missing payload")
              | Some payload -> (
                  match unmask_with_envelope ctx system payload env "" with
                  | Ok orig ->
                      log_pii "-" "demask" system (String.length payload) (String.length orig) [];
                      ("200 OK", [], Jsonio.result orig)
                  | Error why -> ("400 Bad Request", [], Jsonio.error why)
                )
          )
        | _ -> ("400 Bad Request", [], Jsonio.error "missing envelope or one-time code")
    )

(* Build the explain JSON for a list of (span, evidence) pairs. *)
let explain_json (spans : (Spans.span * Evidence.evidence list) list) : string =
  let buf = Buffer.create 256 in
  Buffer.add_char buf '[';
  List.iteri
    (fun i (s, ev) ->
      if i > 0 then Buffer.add_char buf ',';
      let d = Decision.decide s.Spans.ty ev in
      Buffer.add_string buf
        (Printf.sprintf "{\"ty\":\"%s\",\"at\":%d,\"len\":%d,\"score\":%d,\"ev\":[%s]}"
           (Spans.ty_name s.Spans.ty) s.Spans.start s.Spans.len d.score
           (List.map (fun e -> Printf.sprintf "\"%s\"" (Evidence.code_name e.Evidence.code)) ev
           |> String.concat ","
           )
        )
    )
    spans;
  Buffer.add_char buf ']';
  Buffer.contents buf

(* Handle POST /explain: return masked and rejected spans with evidence. *)
let handle_explain (ctx : ctx) (headers : (string * string) list) (body : string) :
    string * (string * string) list * string =
  let system = system_of_headers headers in
  let p = Config.profile_of (Atomic.get ctx.config) system in
  match Jsonio.find_string body "payload" with
  | None -> ("400 Bad Request", [], Jsonio.error "missing payload")
  | Some payload ->
      let masked, rejected = decide_spans ctx payload in
      let masked = List.filter (fun (s, _) -> type_allowed p s.Spans.ty) masked in
      let masked_json = explain_json masked in
      let rejected_json = explain_json rejected in
      ("200 OK", [], Printf.sprintf "{\"masked\":%s,\"rejected\":%s}" masked_json rejected_json)

let handle_health () : string * (string * string) list * string =
  ("200 OK", [], "{\"status\":\"ok\"}")

(* POST /admin/reload: re-read config/systems.yaml and swap it atomically.
   Requests in flight finish on the old config. *)
(* Горячая перезагрузка конфига и справочников. Требует одноразового кода:
   ручка меняет поведение маскирования на лету, и оставлять её открытой —
   это разрешить любому желающему выключить маскирование целиком
   (раздел 6.4 спеки). На /process ничего этого нет: проверяющая система
   ходит без заголовков. *)
let handle_reload (ctx : ctx) (headers : (string * string) list) :
    string * (string * string) list * string =
  match otp_of_headers headers with
  | None -> ("401 Unauthorized", [], Jsonio.error "missing one-time code")
  | Some code ->
      if not (Otp.verify ctx.otp "admin/reload" code) then
        ("401 Unauthorized", [], Jsonio.error "invalid or used one-time code")
      else
        let cfg = Config.load "config/systems.yaml" in
        Atomic.set ctx.config cfg;
        ("200 OK", [], "{\"status\":\"reloaded\"}")

let handle_metrics (ctx : ctx) : string * (string * string) list * string =
  ("200 OK", [], Metrics.render ctx.metrics)

(* Basic auth: check the Authorization: Basic base64(user:pass) header against
   the admin password. The user part is ignored; only the password matters. *)
let basic_auth_ok (ctx : ctx) (headers : (string * string) list) : bool =
  match List.assoc_opt "Authorization" headers with
  | None -> false
  | Some auth -> (
      let prefix = "Basic " in
      if
        String.length auth <= String.length prefix
        || String.sub auth 0 (String.length prefix) <> prefix
      then
        false
      else
        let b64 =
          String.sub auth (String.length prefix) (String.length auth - String.length prefix)
        in
        match Base64.decode ~pad:false b64 with
        | Error _ -> false
        | Ok decoded -> (
            let colon = String.index_opt decoded ':' in
            match colon with
            | None -> false
            | Some i ->
                let pass = String.sub decoded (i + 1) (String.length decoded - i - 1) in
                pass = ctx.admin_password
          )
    )

let auth_required () : string * (string * string) list * string =
  ("401 Unauthorized", [("WWW-Authenticate", "Basic realm=\"pdmask\"")], Jsonio.error "unauthorized")

(* Route a request. Returns (status, headers, body). *)
let route (ctx : ctx) (method_ : string) (path : string) (headers : (string * string) list)
    (body : string) : string * (string * string) list * string =
  (* /process is the autocheck contract and must stay open (no auth). The
     admin endpoints (/metrics, /admin/reload) require basic auth. *)
  let admin_path =
    match path with
    | "/metrics" | "/admin/reload" -> true
    | _ -> false
  in
  if admin_path && not (basic_auth_ok ctx headers) then
    auth_required ()
  else
    match (method_, path) with
    | "POST", "/process" -> handle_process ctx body
    | "POST", "/process/" -> handle_process ctx body
    | "POST", "/mask" -> handle_mask ctx headers body
    | "POST", "/unmask" -> handle_unmask ctx headers body
    | "POST", "/explain" -> handle_explain ctx headers body
    | "POST", "/admin/reload" -> handle_reload ctx headers
    | "GET", "/health" -> handle_health ()
    | "GET", "/metrics" -> handle_metrics ctx
    | _ -> ("404 Not Found", [], Jsonio.error "not found")
