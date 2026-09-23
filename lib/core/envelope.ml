(* envelope.ml — конверт: HKDF + AEAD, без состояния (раздел 6.2).

   Модуль не хранит ничего восстановимого. Ключи уходят к клиенту, наружу —
   только метки. Дамп памяти модуля не содержит ни оригиналов, ни таблицы
   соответствий.

   Схема на каждый запрос:

     S        = 32 случайных байта
     K_req    = HKDF-Expand(K_sys, S, "pdmask/v1")     RFC 5869, один HMAC-SHA256
     K_sys    = HKDF-Expand(K_master, system_id, "pdmask/sys")
     C_i      = AEAD-Seal(K_req, nonce=i, value_i, AAD)  AES-GCM, RFC 5116
     AAD      = payload_id ‖ тип ‖ i ‖ exp ‖ метка

   Счётчик i как nonce безопасен, потому что K_req уникален для запроса:
   требование уникальности nonce на ключ (SP 800-38D §8.2) выполняется по
   построению, координация между доменами не нужна.

   Конверт возвращается клиенту:

     X-PDMask-Envelope: v1.<base64url(S)>.<exp>.<base64url(blob)>

   Клиент предъявляет его при демаскировании; модуль выводит K_req заново
   из S и открывает записи. Состояния на сервере нет. Одноразовость и срок
   жизни — поле exp внутри AAD: конверт, открытый после истечения,
   отбрасывается. *)

type record =
  { index : int; (* nonce / порядковый номер спана *)
    ty : Spans.ty;
    label : string; (* метка, например "[ФИО_1]" *)
    ciphertext : string (* AEAD-Seal(K_req, nonce=index, value, AAD) *)
  }

type t =
  { salt : string; (* S, 32 байта *)
    exp : int64; (* unix time истечения *)
    records : record list
  }

(* --- HKDF-Expand (RFC 5869 §2.3) --- *)

(* Один блок: L <= 32 (размер выхода SHA-256). T(1) = HMAC(PRK, info || 0x01). *)
let hkdf_expand (prk : string) (info : string) : string =
  Digestif.SHA256.hmac_string ~key:prk (info ^ "\x01") |> Digestif.SHA256.to_raw_string

(* --- AES-GCM (RFC 5116) --- *)

let aead_seal (key : string) (nonce : string) (adata : string) (msg : string) : string =
  let k = Mirage_crypto.AES.GCM.of_secret key in
  Mirage_crypto.AES.GCM.authenticate_encrypt ~key:k ~nonce ~adata msg

let aead_open (key : string) (nonce : string) (adata : string) (ct : string) : string option =
  let k = Mirage_crypto.AES.GCM.of_secret key in
  Mirage_crypto.AES.GCM.authenticate_decrypt ~key:k ~nonce ~adata ct

(* --- base64url (RFC 4648 §5) --- *)

let b64url_encode (s : string) : string =
  Base64.encode_string ~alphabet:Base64.uri_safe_alphabet ~pad:false s

let b64url_decode (s : string) : string option =
  match Base64.decode ~alphabet:Base64.uri_safe_alphabet ~pad:false s with
  | Ok v -> Some v
  | Error _ -> None

(* --- построение конверта --- *)

(* K_sys из мастера и system_id. *)
let system_key (k_master : string) (system_id : string) : string =
  hkdf_expand k_master (system_id ^ "pdmask/sys")

(* K_req из K_sys и соли. *)
let request_key (k_sys : string) (salt : string) : string = hkdf_expand k_sys (salt ^ "pdmask/v1")

(* AAD для записи. *)
let aad (payload_id : string) (ty : Spans.ty) (i : int) (exp : int64) (label : string) : string =
  Printf.sprintf "%s|%s|%d|%Ld|%s" payload_id (Spans.ty_name ty) i exp label

(* Запечатать значение в запись. *)
let seal_record (k_req : string) (payload_id : string) (ty : Spans.ty) (i : int) (exp : int64)
    (label : string) (value : string) : record =
  (* nonce = 4 байта нулей + 8 байт счётчика i (big-endian).
     Именно Bytes.make: Bytes.create отдаёт неинициализированную память, и
     первые четыре байта оказывались мусором аллокатора — своим при
     запечатывании и своим при открытии. Совпадали они часто, но не всегда,
     и запись переставала открываться без всякой закономерности. *)
  let nonce = Bytes.make 12 '\000' in
  Bytes.set_int64_be nonce 4 (Int64.of_int i);
  let adata = aad payload_id ty i exp label in
  {index = i; ty; label; ciphertext = aead_seal k_req (Bytes.to_string nonce) adata value}

(* Собрать конверт в строку заголовка. *)
let to_header (t : t) : string =
  let buf = Buffer.create 256 in
  Buffer.add_string buf "v1.";
  Buffer.add_string buf (b64url_encode t.salt);
  Buffer.add_char buf '.';
  Buffer.add_string buf (Int64.to_string t.exp);
  Buffer.add_char buf '.';
  (* blob: для каждой записи — i, тип, метка, шифротекст *)
  let blob = Buffer.create 256 in
  List.iter
    (fun r ->
      Buffer.add_string blob (string_of_int r.index);
      Buffer.add_char blob ':';
      Buffer.add_string blob (Spans.ty_name r.ty);
      Buffer.add_char blob ':';
      Buffer.add_string blob (b64url_encode r.label);
      Buffer.add_char blob ':';
      Buffer.add_string blob (b64url_encode r.ciphertext);
      Buffer.add_char blob ';'
    )
    t.records;
  Buffer.add_string buf (b64url_encode (Buffer.contents blob));
  Buffer.contents buf

(* Разобрать конверт из строки заголовка. *)
let of_header (s : string) : t option =
  let parts = String.split_on_char '.' s in
  match parts with
  | ["v1"; salt_b64; exp_s; blob_b64] -> (
      match (b64url_decode salt_b64, b64url_decode blob_b64, Int64.of_string_opt exp_s) with
      | Some salt, Some blob, Some exp ->
          let records =
            String.split_on_char ';' blob
            |> List.filter (fun x -> x <> "")
            |> List.filter_map (fun rec_s ->
                match String.split_on_char ':' rec_s with
                | [i_s; ty_s; label_b64; ct_b64] -> (
                    match
                      ( int_of_string_opt i_s,
                        Config.ty_of_name ty_s,
                        b64url_decode label_b64,
                        b64url_decode ct_b64
                      )
                    with
                    | Some i, Some ty, Some label, Some ct ->
                        Some {index = i; ty; label; ciphertext = ct}
                    | _ -> None
                  )
                | _ -> None
            )
          in
          Some {salt; exp; records}
      | _ -> None
    )
  | _ -> None

(* Открыть запись: вернуть оригинальное значение, если конверт не истёк и
   AAD совпадает. *)
let open_record (t : t) (k_req : string) (payload_id : string) (r : record) : string option =
  let nonce = Bytes.make 12 '\000' in
  Bytes.set_int64_be nonce 4 (Int64.of_int r.index);
  let adata = aad payload_id r.ty r.index t.exp r.label in
  aead_open k_req (Bytes.to_string nonce) adata r.ciphertext

(* Истёк ли конверт. *)
let expired (t : t) (now : int64) : bool = now > t.exp
