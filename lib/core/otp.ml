(* otp.ml — одноразовые коды RFC 6238 (TOTP поверх RFC 4226 HOTP).

   Демаскирование доступно только авторизованной системе (критерий 3.2).
   Статический ключ в заголовке протухает и утекает с логами; одноразовый
   код — нет.

     T     = floor(unix_time / 30)
     code  = HOTP(K_otp_sys, T) mod 10^8        HMAC-SHA256, 8 цифр

   Одноразовость без блокировок: RFC 6238 §5.2 требует не принимать один и
   тот же шаг дважды. Состояние — одно целое на вызывающего, последний
   принятый T. Atomic.compare_and_set — одна инструкция: два конкурентных
   запроса с одним кодом, один выигрывает CAS, второй получает 401.
   Блокировки нет.

   Счётчик именно на вызывающего, а не один на сервис. Общий счётчик
   означал бы, что во всём сервисе проходит одно демаскирование за
   тридцать секунд: вторая система с собственным верным кодом получала бы
   401 просто потому, что первая успела раньше. Туда же попадал и
   /admin/reload — перезагрузка конфига съедала окно демаскирования.
   Ключей немного и они приходят только из config/systems.yaml (заголовок
   проверяется до кода), так что список не растёт от чужих запросов.

   Сравнение кода — постоянного времени (RFC 6238 §5.2): иначе код
   подбирается по таймингу. *)

type t =
  { secret : string;
    slots : (string * int Atomic.t) list Atomic.t
  }

let create (secret : string) : t = {secret; slots = Atomic.make []}

(* Счётчик вызывающего, заводится при первом обращении. Читается без
   блокировки; на гонке при заведении проигравший CAS просто повторяет и
   находит чужой слот. *)
let rec slot (t : t) (who : string) : int Atomic.t =
  let cur = Atomic.get t.slots in
  match List.assoc_opt who cur with
  | Some a -> a
  | None ->
      let a = Atomic.make 0 in
      if Atomic.compare_and_set t.slots cur ((who, a) :: cur) then
        a
      else
        slot t who

(* 8-байтовый big-endian счётчик, как требует HOTP (RFC 4226 §5.1). *)
let counter_bytes (n : int64) : string =
  let b = Bytes.create 8 in
  for i = 0 to 7 do
    Bytes.set b i
      (Char.chr (Int64.to_int (Int64.logand (Int64.shift_right_logical n (56 - (8 * i))) 0xFFL)))
  done;
  Bytes.to_string b

(* Dynamic truncation (RFC 4226 §5.3): берём 4 байта, начиная с младших 4
   бит последнего байта HMAC, и возвращаем 31-битное число. *)
let dynamic_truncate (mac : string) : int =
  let off = Char.code mac.[String.length mac - 1] land 0x0F in
  let b0 = Char.code mac.[off] land 0x7F in
  let b1 = Char.code mac.[off + 1] in
  let b2 = Char.code mac.[off + 2] in
  let b3 = Char.code mac.[off + 3] in
  (b0 lsl 24) lor (b1 lsl 16) lor (b2 lsl 8) lor b3

(* HOTP(K, counter) mod 10^8, HMAC-SHA256. *)
let hotp (secret : string) (counter : int64) : int =
  let mac = Digestif.SHA256.hmac_string ~key:secret (counter_bytes counter) in
  dynamic_truncate (Digestif.SHA256.to_raw_string mac) mod 100_000_000

(* Код для текущего шага (30-секундное окно). *)
let code_at (t : t) (step : int64) : int = hotp t.secret step

(* Проверить код с допуском ±1 шаг (RFC 6238 §5.2) для вызывающего who.
   Возвращает true, если код верен и шаг этим вызывающим ещё не принимался. *)
let verify (t : t) (who : string) (code : int) : bool =
  let now = Int64.of_float (Unix.gettimeofday ()) in
  let step = Int64.div now 30L in
  let candidates = [step; Int64.sub step 1L; Int64.add step 1L] in
  let last = slot t who in
  let rec try_step = function
    | [] -> false
    | s :: rest ->
        if code_at t s = code then
          (* одноразовость: принять шаг можно, только если CAS прошёл *)
          let s_int = Int64.to_int s in
          let rec cas () =
            let cur = Atomic.get last in
            if s_int <= cur then
              false
            else if Atomic.compare_and_set last cur s_int then
              true
            else
              cas ()
          in
          cas ()
        else
          try_step rest
  in
  try_step candidates

(* Сравнение строк постоянного времени (для кодов, если понадобится). *)
let ct_equal (a : string) (b : string) : bool =
  let n = String.length a in
  if n <> String.length b then
    false
  else
    let acc = ref 0 in
    for i = 0 to n - 1 do
      acc := !acc lor (Char.code a.[i] lxor Char.code b.[i])
    done;
    !acc = 0
