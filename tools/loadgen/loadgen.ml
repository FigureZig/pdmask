(* loadgen.ml — нагрузка на /process через сеть.

   Отдельный проект, а не часть сервиса: генератор нагрузки не должен уезжать
   в архив решения и не должен делить с сервисом ни одной строки кода, иначе
   он померяет сам себя.

   Модель повторяет проверяющую систему (qa_answers.md §4): closed-loop, N
   постоянных соединений, каждое шлёт следующий запрос только получив ответ на
   предыдущий. Это важно: open-loop генератор на таком сервисе покажет другую
   латентность.

   Профиль нагрузки — микротексты вперемешку с плотными крупными. Каждый
   heavy-every-й запрос уходит крупным, остальные микро. Так видно и полку, и
   провалы: пока одно соединение жуёт 400 КБ, остальные должны продолжать
   отвечать за микросекунды, и если не продолжают — это видно в p99.

     dune exec ./loadgen.exe -- --host 127.0.0.1 --port 8080 \
       --conns 200 --duration 30 --heavy-every 50

   Меряется время от отправки первого байта запроса до последнего байта
   ответа, то есть вместе с сетью. *)

let dbg = Atomic.make 0

(* Метка прогона в payload_id. Без неё второй запуск по тому же сервису
   получает из хранилища оригиналы первого (TTL 120 с) и выглядит как
   сломанное демаскирование, хотя сервис ведёт себя ровно по контракту. *)
let run_tag = Printf.sprintf "%x" (int_of_float (Unix.gettimeofday () *. 1000.) land 0xffffff)

let host = ref "127.0.0.1"

let port = ref 8080

let conns = ref 200

let duration = ref 20.0

let heavy_every = ref 50

let heavy_bytes = ref 409600

let domains = ref (Domain.recommended_domain_count ())

let () =
  let rec parse i =
    if i + 1 < Array.length Sys.argv then (
      ( match Sys.argv.(i) with
      | "--host" -> host := Sys.argv.(i + 1)
      | "--port" -> port := int_of_string Sys.argv.(i + 1)
      | "--conns" -> conns := int_of_string Sys.argv.(i + 1)
      | "--duration" -> duration := float_of_string Sys.argv.(i + 1)
      | "--heavy-every" -> heavy_every := int_of_string Sys.argv.(i + 1)
      | "--heavy-bytes" -> heavy_bytes := int_of_string Sys.argv.(i + 1)
      | "--domains" -> domains := int_of_string Sys.argv.(i + 1)
      | _ -> ()
      );
      parse (i + 1)
    )
  in
  parse 1

(* --- полезная нагрузка --- *)

let micro_texts =
  [| "Клиент Иванов Иван Иванович, паспорт 4509 123456";
     "Телефон +7 916 123-45-67, почта ivan@example.com";
     "Карта 4276 3800 1234 5678, пин-код 4321";
     "Поэт Александр Сергеевич Пушкин родился в Москве";
     "Адрес отделения банка: г. Москва, ул. Тверская, 13";
     "ИНН 7707083893, дата рождения 12.03.1990";
     "Заказ номер 1234567890 доставлен вовремя";
     "улица Пушкина, дом 5, квартира 12"
  |]

(* Плотный крупный текст: не повторение одной строки, а перемешанные кейсы —
   иначе детектор идёт по одному и тому же пути и кэш ведёт себя нечестно. *)
let heavy_text =
  let buf = Buffer.create !heavy_bytes in
  let i = ref 0 in
  while Buffer.length buf < !heavy_bytes do
    Buffer.add_string buf micro_texts.(!i mod Array.length micro_texts);
    Buffer.add_string buf ". Дополнительный текст для объёма, ";
    Buffer.add_string buf "чтобы распределение токенов было ближе к реальному. ";
    incr i
  done;
  Buffer.contents buf

let json_escape (s : string) : string =
  let b = Buffer.create (String.length s + 16) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c
    )
    s;
  Buffer.contents b

(* Экранирование считается один раз на старте. Внутри цикла его делать нельзя:
   экранировать 400 КБ дороже, чем сервису их обработать, и замер показал бы
   стоимость генератора вместо стоимости сервиса. *)
let escaped_heavy = lazy (json_escape heavy_text)

let escaped_micro = lazy (Array.map json_escape micro_texts)

let request_esc (path : string) (escaped : string) (id : string) : string =
  let body = Printf.sprintf "{\"payload\":\"%s\",\"payload_id\":\"%s\"}" escaped id in
  Printf.sprintf
    "POST %s HTTP/1.1\r\nHost: %s\r\nContent-Type: application/json\r\nContent-Length: %d\r\nConnection: keep-alive\r\n\r\n%s"
    path !host (String.length body) body

(* --- замеры --- *)

type op =
  | Mask
  | Demask

type sample =
  { heavy : bool;
    op : op;
    us : int; (* латентность в микросекундах *)
    at : float; (* момент завершения, для таймлайна *)
    status : int; (* 200, 429, прочее; 0 — обрыв соединения *)
    resp_len : int;
    variant : int; (* индекс микротекста, -1 для крупного *)
    restored : bool (* для Demask: вернулся ли оригинал байт в байт *)
  }

let percentile (sorted : int array) (p : float) : int =
  let n = Array.length sorted in
  if n = 0 then
    0
  else
    let idx = int_of_float (p *. float_of_int (n - 1) /. 100.) in
    sorted.(max 0 (min (n - 1) idx))

(* --- одно соединение --- *)

let run_conn ~net ~sw ~(stop : float) ~(worker : int) (acc : sample list ref) =
  let addr = `Tcp (Eio_unix.Net.Ipaddr.of_unix (Unix.inet_addr_of_string !host), !port) in
  let flow = Eio.Net.connect ~sw net addr in
  let reader = Eio.Buf_read.of_flow flow ~max_size:(64 * 1024 * 1024) in
  (* Один запрос: отправить, прочитать статус и тело. Возвращает (статус, тело). *)
  let round (req : string) : int * string =
    Eio.Flow.copy_string req flow;
    let len = ref 0 in
    let status = ref 0 in
    let fin = ref false in
    while not !fin do
      let line = Eio.Buf_read.line reader in
      if line = "" then
        fin := true
      else (
        ( if String.length line > 12 && String.sub line 0 9 = "HTTP/1.1 " then
            status := try int_of_string (String.sub line 9 3) with _ -> 0
        );
        let low = String.lowercase_ascii line in
        if String.length low > 16 && String.sub low 0 15 = "content-length:" then
          len := int_of_string (String.trim (String.sub line 15 (String.length line - 15)))
      )
    done;
    (!status, Eio.Buf_read.take !len reader)
  in
  (* Вырезает значение поля result из {"result":"..."} без разэкранирования:
     сервер уже отдал его в экранированном виде, и в таком же виде его надо
     положить обратно в запрос на демаскирование. *)
  let result_of (body : string) : string option =
    let pre = "{\"result\":\"" in
    let n = String.length body
    and m = String.length pre in
    if n > m + 2 && String.sub body 0 m = pre && String.sub body (n - 2) 2 = "\"}" then
      Some (String.sub body m (n - m - 2))
    else
      None
  in
  let n = ref 0 in
  try
    while Unix.gettimeofday () < stop do
      let heavy = (!n + worker) mod !heavy_every = !heavy_every - 1 in
      let variant =
        if heavy then
          -1
        else
          (!n + worker) mod Array.length micro_texts
      in
      let escaped =
        if heavy then
          Lazy.force escaped_heavy
        else
          (Lazy.force escaped_micro).(variant)
      in
      let id = Printf.sprintf "lg-%s-%d-%d" run_tag worker !n in
      (* шаг 1: маскирование *)
      let t0 = Unix.gettimeofday () in
      let st, body = round (request_esc "/process" escaped id) in
      let t1 = Unix.gettimeofday () in
      acc :=
        { heavy;
          op = Mask;
          us = int_of_float ((t1 -. t0) *. 1e6);
          at = t1;
          status = st;
          resp_len = String.length body;
          variant;
          restored = true
        }
        :: !acc;
      (* шаг 2: демаскирование тем же payload_id — ровно как делает чекер *)
      ( match (st, result_of body) with
      | 200, Some masked ->
          let t2 = Unix.gettimeofday () in
          let st2, body2 = round (request_esc "/process" masked id) in
          let t3 = Unix.gettimeofday () in
          let restored =
            match result_of body2 with
            | Some r -> r = escaped
            | None -> false
          in
          (* первые несколько расхождений печатаем подробно: без этого
              непонятно, кто виноват — сервис или генератор *)
          ( if (not restored) && Atomic.fetch_and_add dbg 1 < 3 then
              let got = Option.value (result_of body2) ~default:"<не разобрано>" in
              let stars =
                String.fold_left
                  (fun a c ->
                    if c = '*' then
                      a + 1
                    else
                      a
                  )
                  0 got
              in
              Printf.eprintf
                "  РАСХОЖДЕНИЕ id=%s heavy=%b  статус маски=%d статус демаски=%d\n\    ждали %d симв, получили %d симв, звёздочек в ответе %d\n\    ответ начинается: %s\n%!"
                id heavy st st2 (String.length escaped) (String.length got) stars
                (String.sub got 0 (min 70 (String.length got)))
          );
          acc :=
            { heavy;
              op = Demask;
              us = int_of_float ((t3 -. t2) *. 1e6);
              at = t3;
              status = st2;
              resp_len = String.length body2;
              variant;
              restored
            }
            :: !acc
      | _ -> ()
      );
      incr n
    done
  with _ -> ()

(* --- отчёт --- *)

let report (samples : sample list) (wall : float) =
  let all = Array.of_list samples in
  let total = Array.length all in
  let count f =
    Array.fold_left
      (fun a s ->
        if f s then
          a + 1
        else
          a
      )
      0 all
  in
  let n200 = count (fun s -> s.status = 200) in
  let n429 = count (fun s -> s.status = 429) in
  let ndrop = count (fun s -> s.status = 0) in
  let nother = total - n200 - n429 - ndrop in
  let demasks = Array.to_list all |> List.filter (fun s -> s.op = Demask) in
  let bad_restore = List.length (List.filter (fun s -> not s.restored) demasks) in
  Printf.printf "\n=== нагрузка ===\n";
  Printf.printf "  обменов: %d за %.1f с  =  %.0f оп/с\n" total wall (float_of_int total /. wall);
  Printf.printf "\n=== ответы (критерий: 429 и невалидные) ===\n";
  Printf.printf "  200 OK              %7d  (%.2f%%)\n" n200
    (100. *. float_of_int n200 /. float_of_int total);
  Printf.printf "  429 Too Many        %7d  (%.2f%%)   допустим, чекер ретраит\n" n429
    (100. *. float_of_int n429 /. float_of_int total);
  Printf.printf "  прочие коды         %7d  (%.2f%%)   НЕВАЛИДНЫ\n" nother
    (100. *. float_of_int nother /. float_of_int total);
  Printf.printf "  обрыв без ответа    %7d  (%.2f%%)   НЕВАЛИДНЫ\n" ndrop
    (100. *. float_of_int ndrop /. float_of_int total);
  Printf.printf "\n=== восстановление (критерий: демаскирование) ===\n";
  Printf.printf "  демаскирований: %d, не совпало с оригиналом: %d (%.3f%%)\n" (List.length demasks)
    bad_restore
    ( if demasks = [] then
        0.
      else
        100. *. float_of_int bad_restore /. float_of_int (List.length demasks)
    );
  (* Инвариант 2: один вход — один выход. Разные длины ответа на один и тот же
     текст означают недетерминированное маскирование. *)
  let by_variant = Hashtbl.create 16 in
  Array.iter
    (fun s ->
      if s.op = Mask && s.status = 200 then
        let cur = try Hashtbl.find by_variant s.variant with Not_found -> [] in
        if not (List.mem s.resp_len cur) then
          Hashtbl.replace by_variant s.variant (s.resp_len :: cur)
    )
    all;
  let bad =
    Hashtbl.fold
      (fun v lens acc ->
        if List.length lens > 1 then
          (v, List.sort compare lens) :: acc
        else
          acc
      )
      by_variant []
  in
  if bad = [] then
    Printf.printf "детерминизм: OK, каждый вход дал маску одной длины\n"
  else (
    Printf.printf "\nНЕДЕТЕРМИНИЗМ маскирования:\n";
    List.iter
      (fun (v, lens) ->
        Printf.printf "  вариант %d: длины %s\n" v (String.concat ", " (List.map string_of_int lens))
      )
      bad
  );
  let show name sel =
    let xs =
      Array.of_list
        (List.filter_map
           (fun s ->
             if sel s then
               Some s.us
             else
               None
           )
           samples
        )
    in
    Array.sort compare xs;
    let n = Array.length xs in
    if n > 0 then
      let mean = Array.fold_left ( + ) 0 xs / n in
      Printf.printf "  %-22s n=%-7d  avg %7.2f   p50 %7.2f   p95 %7.2f   p99 %7.2f   max %8.2f\n"
        name n
        (float_of_int mean /. 1000.)
        (float_of_int (percentile xs 50.) /. 1000.)
        (float_of_int (percentile xs 95.) /. 1000.)
        (float_of_int (percentile xs 99.) /. 1000.)
        (float_of_int (percentile xs 100.) /. 1000.)
  in
  Printf.printf "\n=== латентность, мс (критерий: p99/p95/p50/avg, вместе с сетью) ===\n";
  show "маскирование микро" (fun s -> s.op = Mask && not s.heavy);
  show "маскирование крупных" (fun s -> s.op = Mask && s.heavy);
  show "демаскирование микро" (fun s -> s.op = Demask && not s.heavy);
  show "демаскирование крупных" (fun s -> s.op = Demask && s.heavy);
  show "всё вместе" (fun _ -> true);
  let t0 = Array.fold_left (fun a s -> min a s.at) infinity all in
  let buckets = Hashtbl.create 64 in
  Array.iter
    (fun s ->
      let b = int_of_float ((s.at -. t0) *. 2.) in
      let cur = try Hashtbl.find buckets b with Not_found -> [] in
      Hashtbl.replace buckets b (s.us :: cur)
    )
    all;
  Printf.printf "\nтаймлайн по 0.5 с:\n";
  let keys = Hashtbl.fold (fun k _ a -> k :: a) buckets [] |> List.sort compare in
  List.iter
    (fun k ->
      let xs = Array.of_list (Hashtbl.find buckets k) in
      Array.sort compare xs;
      let rps = float_of_int (Array.length xs) *. 2. in
      let p99 = float_of_int (percentile xs 99.) /. 1000. in
      let bar = String.make (min 40 (int_of_float (rps /. 200.))) '#' in
      Printf.printf "  %5.1f с  %7.0f оп/с  p99 %8.2f мс  %s\n" (float_of_int k /. 2.) rps p99 bar
    )
    keys

let () =
  Printf.printf "цель: http://%s:%d/process   соединений: %d   длительность: %.0f с\n" !host !port
    !conns !duration;
  Printf.printf "крупное тело каждые %d запросов, размер %d Б (~%d токенов)\n" !heavy_every
    !heavy_bytes (!heavy_bytes / 4);
  Printf.printf "доменов у генератора: %d\n" !domains;
  Eio_main.run @@ fun env ->
  let net = Eio.Stdenv.net env in
  let dm = Eio.Stdenv.domain_mgr env in
  let stop = Unix.gettimeofday () +. !duration in
  let t0 = Unix.gettimeofday () in
  (* Соединения разложены по доменам. На одном домене фибры кооперативны, и
     двести из них, одна из которых читает 400 КБ, дают латентность генератора,
     а не сервиса — первый прогон показал 285 RPS и пять секунд на крупных,
     хотя одиночный такой запрос обслуживается за 0.1 с. *)
  let per = max 1 (!conns / !domains) in
  let results = Array.make !domains [] in
  Eio.Switch.run (fun sw ->
      for d = 0 to !domains - 1 do
        Eio.Fiber.fork ~sw (fun () ->
            results.(d) <-
              Eio.Domain_manager.run dm (fun () ->
                  let accs = Array.init per (fun _ -> ref []) in
                  Eio.Switch.run (fun sw' ->
                      for i = 0 to per - 1 do
                        Eio.Fiber.fork ~sw:sw' (fun () ->
                            run_conn ~net ~sw:sw' ~stop ~worker:((d * per) + i) accs.(i)
                        )
                      done
                  );
                  Array.fold_left (fun a r -> !r @ a) [] accs
              )
        )
      done
  );
  let wall = Unix.gettimeofday () -. t0 in
  report (Array.fold_left (fun a l -> l @ a) [] results) wall
