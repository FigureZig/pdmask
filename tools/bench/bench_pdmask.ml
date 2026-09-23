(* bench_pdmask.ml — микробенчмарки конвейера на core_bench.

   Отвечает на два вопроса, которые нельзя закрыть замером снаружи по HTTP:
   сколько стоит каждая стадия отдельно и сколько она аллоцирует.

   Колонка mWd/Run (minor words) — главная. Инвариант 5 спеки требует, чтобы в
   горячем пути не было аллокаций сверх переиспользуемых буферов, и это
   единственный способ показать, что он соблюдается, а не заявлен.

     dune exec tools/bench/bench_pdmask.exe -- -ascii -quota 2
     dune exec tools/bench/bench_pdmask.exe -- -ascii -quota 5 +cycles

   Запускать из корня проекта: словари читаются из ./dicts. *)

open Pdmask_core
open Pdmask_corpus

let dicts_dir = "dicts"

let default_corpus = "tools/bench/corpus/own/cases.txt"

(* --- подготовка --- *)

let dict, persons =
  let d = Dict.create () in
  let p = Dictload.load_public_persons dicts_dir in
  Dictload.load d dicts_dir p;
  (d, p)

let bank_index = Textindex.of_keys (Dictload.load_bank_offices dicts_dir)

let cases = Corpus.load default_corpus

(* Склейка кейсов до нужного размера. Крупный вход строится повторением
   корпуса, а не отдельным файлом: 400 КБ текста в репозитории — это ровно то,
   что раздел 7.1 ТЗ просит не класть в архив. *)
let payload_of_size (target : int) : string =
  let buf = Buffer.create target in
  let docs = List.filter (fun (c : Corpus.case) -> c.size <> "micro") cases in
  let arr = Array.of_list docs in
  let i = ref 0 in
  while Buffer.length buf < target && Array.length arr > 0 do
    Buffer.add_string buf arr.(!i mod Array.length arr).Corpus.text;
    Buffer.add_string buf "\n\n";
    incr i
  done;
  Buffer.contents buf

let sizes = [128; 1024; 8192; 65536; 409600]

let payloads = List.map (fun n -> (n, payload_of_size n)) sizes

let payload n = List.assoc n payloads

(* Отдельный буфер токенов на каждую стадию: лексер переиспользует структуру,
   и бенчмарки не должны драться за неё. *)
let toks_for = Hashtbl.create 8

let lexed n =
  match Hashtbl.find_opt toks_for n with
  | Some t -> t
  | None ->
      let t = Lexer.create () in
      Lexer.lex t dict (payload n);
      Hashtbl.add toks_for n t;
      t

let ev_ctx n toks =
  let p = payload n in
  { Evidence.bank_index;
    public_forms = Dictload.public_forms persons;
    payload = p;
    payload_cp = Evidence.code_points_capped p 64;
    toks
  }

(* Входы для стадий ниже по потоку считаются ОДИН раз и запоминаются. Иначе
   замер стадии 4 включал бы в себя стадию 3, стадии 5 — обе предыдущие, и
   таблица показывала бы нарастающий итог вместо стоимости стадии. *)
let memo (tbl : (int, 'a) Hashtbl.t) (f : int -> 'a) (n : int) : 'a =
  match Hashtbl.find_opt tbl n with
  | Some v -> v
  | None ->
      let v = f n in
      Hashtbl.add tbl n v;
      v

let cand_tbl : (int, Spans.span list) Hashtbl.t = Hashtbl.create 8

let weighed_tbl : (int, (Spans.span * Evidence.evidence list) list) Hashtbl.t = Hashtbl.create 8

let accepted_tbl : (int, Spans.span list) Hashtbl.t = Hashtbl.create 8

let candidates n = memo cand_tbl (fun n -> Rules.detect (payload n) (lexed n)) n

let weighed n =
  memo weighed_tbl
    (fun n ->
      let ctx = ev_ctx n (lexed n) in
      List.map (fun s -> (s, Evidence.collect ctx s)) (candidates n)
    )
    n

let accepted n =
  memo accepted_tbl
    (fun n ->
      List.filter_map
        (fun (s, ev) ->
          let d = Decision.decide s.Spans.ty ev in
          if d.Decision.masked then
            Some s
          else
            None
        )
        (weighed n)
    )
    n

(* --- сквозной путь, как его проходит /process --- *)

let final_tbl : (int, Spans.span list) Hashtbl.t = Hashtbl.create 8

let final n = memo final_tbl (fun n -> Spans.glue (Spans.resolve (accepted n))) n

let router_ctx =
  { Pdmask_http.Router.store = Store.create ();
    dict;
    bank_index;
    public_forms = Dictload.public_forms persons;
    config = Atomic.make Pdmask_core.Config.default_config;
    metrics = Pdmask_core.Metrics.create ();
    k_master = "bench-master-key-00000000000000000000000000000000";
    otp = Pdmask_core.Otp.create "bench-otp-secret-00000000000000000000000000000000";
    admin_password = "bench"
  }

let () =
  let idx name f =
    Core_bench.Bench.Test.create_indexed ~name ~args:sizes (fun n ->
        Core.Staged.stage (fun () -> f n)
    )
  in
  let one_word = "Иванова" in
  let tests =
    [ (* элементарные операции: показывают, что свёртка регистра и словарь
         стоят единицы наносекунд и не аллоцируют *)
      Core_bench.Bench.Test.create ~name:"dict: поиск, попадание" (fun () ->
          ignore (Dict.find dict one_word 0 (String.length one_word))
      );
      Core_bench.Bench.Test.create ~name:"dict: поиск, промах" (fun () ->
          ignore (Dict.find dict "щщщщщщ" 0 12)
      );
      Core_bench.Bench.Test.create ~name:"classes: свёртка слова" (fun () ->
          ignore (Classes.fold_string one_word)
      );
      (* стадии конвейера по размеру входа *)
      idx "1 лексер" (fun n -> Lexer.lex (lexed n) dict (payload n));
      idx "2 правила" (fun n -> ignore (Rules.detect (payload n) (lexed n)));
      idx "3 доказательства" (fun n ->
          let ctx = ev_ctx n (lexed n) in
          List.iter (fun s -> ignore (Evidence.collect ctx s)) (candidates n)
      );
      idx "4 решение" (fun n ->
          List.iter (fun (s, ev) -> ignore (Decision.decide s.Spans.ty ev)) (weighed n)
      );
      idx "5 пересечения" (fun n -> ignore (Spans.glue (Spans.resolve (accepted n))));
      idx "6 маска" (fun n -> ignore (Mask.mask Mask.Stars (payload n) (final n)));
      idx "весь конвейер" (fun n ->
          ignore (Pdmask_http.Router.mask router_ctx Pdmask_core.Config.default_profile (payload n))
      )
    ]
  in
  Printf.printf "словарь: %d записей, корпус: %d кейсов\n" (Dict.size dict) (List.length cases);
  Printf.printf "размеры входа: %s\n\n"
    (String.concat ", " (List.map (fun n -> Printf.sprintf "%d Б" n) sizes));
  (* Lexer.lex уступает управление через Eio.Fiber.yield каждые 64 КиБ, поэтому
     вне Eio-контекста он падает с Effect.Unhandled. Бенчмарк запускается внутри
     Eio_main по той же причине, по которой там работает сервис — и заодно меряет
     настоящую стоимость уступки, а не версию без неё. *)
  Eio_main.run @@ fun _env ->
  (* Прогрев внутри Eio: заполняем мемоизацию до замеров, иначе первый прогон
     каждой стадии оплатил бы все предыдущие. И лексер всё равно требует
     Eio-контекста, так что раньше это сделать негде. *)
  List.iter (fun n -> ignore (final n)) sizes;
  Command_unix.run (Core_bench.Bench.make_command tests)
