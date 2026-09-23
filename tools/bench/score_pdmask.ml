(* score_pdmask.ml — качество конвейера против эталонного корпуса.

   Ходит не по HTTP, а прямо в Router.decide_spans, поэтому меряет детекцию,
   а не сеть, и видит спаны, а не строку со звёздочками.

     dune exec tools/bench/score_pdmask.exe
     dune exec tools/bench/score_pdmask.exe -- --fails
     dune exec tools/bench/score_pdmask.exe -- --size micro

   Метрика:
   - recall — доля непробельных байтов эталонных спанов, закрытых маской.
     Пробелы внутри спана маска сохраняет намеренно, поэтому пропуском они не
     считаются.
   - лишних — байты под маской вне эталонных спанов.
   - на кейсах expect=clean любой замаскированный байт является ошибкой.

   Запускать из корня проекта: словари читаются из ./dicts. *)

open Pdmask_core
open Pdmask_corpus
open Pdmask_report

let dicts_dir = "dicts"

let default_corpus = "tools/bench/corpus/own/cases.txt"

(* Путь к корпусу можно задать аргументом: один и тот же инструмент считает и
   наш ручной набор, и чужие датасеты вроде pii-bench. *)
let corpus_path =
  let rec find i =
    if i >= Array.length Sys.argv then
      default_corpus
    else if Sys.argv.(i) = "--corpus" && i + 1 < Array.length Sys.argv then
      Sys.argv.(i + 1)
    else
      find (i + 1)
  in
  find 1

let show_fails = Array.exists (fun a -> a = "--fails") Sys.argv

let only_size =
  let rec find i =
    if i + 1 >= Array.length Sys.argv then
      None
    else if Sys.argv.(i) = "--size" then
      Some Sys.argv.(i + 1)
    else
      find (i + 1)
  in
  find 1

let is_space (c : char) : bool = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* Входит ли тип в перечень, который умеет наш сервис? Чужие корпусы размечают
   шире: в pii-bench есть КПП, ОГРН, ОГРНИП и токены доступа — это реквизиты
   организации и ключи доступа, а не персональные данные раздела 4.1 ТЗ. Такие
   спаны считаются нейтральными: их не требуется замаскировать, и маска поверх
   них не штрафуется. Иначе метрика по ТЗ портится чужой разметкой. *)
let known_type (name : string) : bool = Config.ty_of_name name <> None

(* --- один кейс --- *)

type result =
  { case : Corpus.case;
    recall : float option; (* None, если эталон пуст *)
    over : int; (* байт под маской вне эталона *)
    utf8_ok : bool (* выход остался корректным UTF-8 *)
  }

(* Корректен ли UTF-8? Спан или дырка, обрезанные посреди символа, оставляют
   ведущий байт без продолжения, и ответ перестаёт быть валидным UTF-8 —
   снаружи это порча данных, а не маскирование. Проверка дешёвая, а регрессия
   молчаливая, поэтому она здесь. *)
let valid_utf8 (s : string) : bool =
  let n = String.length s in
  let rec go i =
    if i >= n then
      true
    else
      let c = Char.code s.[i] in
      let w =
        if c < 0x80 then
          1
        else if c land 0xE0 = 0xC0 then
          2
        else if c land 0xF0 = 0xE0 then
          3
        else if c land 0xF8 = 0xF0 then
          4
        else
          0
      in
      if w = 0 || i + w > n then
        false
      else
        let rec cont k = k >= w || (Char.code s.[i + k] land 0xC0 = 0x80 && cont (k + 1)) in
        cont 1 && go (i + w)
  in
  go 0

let run_case (ctx : Pdmask_http.Router.ctx) (c : Corpus.case) : result =
  let kept, _ = Pdmask_http.Router.decide_spans ctx c.Corpus.text in
  let spans = Spans.glue (Spans.resolve (List.map fst kept)) in
  let n = String.length c.Corpus.text in
  let covered = Bytes.make n '\000' in
  List.iter
    (fun (s : Spans.span) ->
      for i = s.Spans.start to min (n - 1) (s.Spans.start + s.Spans.len - 1) do
        Bytes.set covered i '\001'
      done
    )
    spans;
  let truth = Bytes.make n '\000' in
  let neutral = Bytes.make n '\000' in
  List.iter
    (fun (s : Corpus.span) ->
      let mark =
        if known_type s.Corpus.ty then
          truth
        else
          neutral
      in
      for i = s.Corpus.start to min (n - 1) (s.Corpus.stop - 1) do
        if not (is_space c.Corpus.text.[i]) then Bytes.set mark i '\001'
      done
    )
    c.Corpus.spans;
  let hit = ref 0
  and total = ref 0
  and over = ref 0 in
  for i = 0 to n - 1 do
    let t = Bytes.get truth i = '\001'
    and m = Bytes.get covered i = '\001' in
    if t then (
      incr total;
      if m then incr hit
    ) else if m && (not (is_space c.Corpus.text.[i])) && Bytes.get neutral i <> '\001' then
      incr over
  done;
  let recall =
    if !total = 0 then
      None
    else
      Some (float_of_int !hit /. float_of_int !total)
  in
  let masked = Mask.mask Mask.Stars c.Corpus.text (Spans.glue spans) in
  {case = c; recall; over = !over; utf8_ok = valid_utf8 masked}

(* --- сводка --- *)

let () =
  let dict = Dict.create () in
  let persons = Dictload.load_public_persons dicts_dir in
  Dictload.load dict dicts_dir persons;
  let ctx =
    { Pdmask_http.Router.store = Store.create ();
      dict;
      bank_index = Textindex.of_keys (Dictload.load_bank_offices dicts_dir);
      public_forms = Dictload.public_forms persons;
      config = Atomic.make Pdmask_core.Config.default_config;
      metrics = Pdmask_core.Metrics.create ();
      k_master = "bench-master-key-00000000000000000000000000000000";
      otp = Pdmask_core.Otp.create "bench-otp-secret-00000000000000000000000000000000";
      admin_password = "bench"
    }
  in
  let cases =
    Corpus.load corpus_path
    |> List.filter (fun (c : Corpus.case) ->
        match only_size with
        | None -> true
        | Some s -> c.Corpus.size = s
    )
  in
  let results = List.map (run_case ctx) cases in
  Printf.printf "корпус: %d кейсов, словарь: %d записей\n\n" (List.length cases) (Dict.size dict);

  (* по классу размера *)
  Printf.printf "%s %7s %8s %10s\n" (Report.pad 10 "размер") "кейсов" "recall" "лишних Б";
  Printf.printf "%s\n" (String.make 38 '-');
  List.iter
    (fun size ->
      let sel = List.filter (fun r -> r.case.Corpus.size = size) results in
      if sel <> [] then
        let rs = List.filter_map (fun r -> r.recall) sel in
        let avg =
          if rs = [] then
            nan
          else
            List.fold_left ( +. ) 0. rs /. float_of_int (List.length rs)
        in
        let over = List.fold_left (fun a r -> a + r.over) 0 sel in
        Printf.printf "%s %7d %8.3f %10d\n" (Report.pad 10 size) (List.length sel) avg over
    )
    ["micro"; "sentence"; "document"];

  (* по типу ПДН *)
  let tbl = Hashtbl.create 32 in
  List.iter
    (fun r ->
      match r.recall with
      | None -> ()
      | Some v ->
          let types =
            List.sort_uniq compare
              (List.map (fun (s : Corpus.span) -> s.Corpus.ty) r.case.Corpus.spans)
            |> List.filter known_type
          in
          List.iter
            (fun t ->
              let sum, n = try Hashtbl.find tbl t with Not_found -> (0., 0) in
              Hashtbl.replace tbl t (sum +. v, n + 1)
            )
            types
    )
    results;
  let rows =
    Hashtbl.fold (fun t (sum, n) acc -> (t, sum /. float_of_int n, n) :: acc) tbl []
    |> List.sort (fun (_, a, _) (_, b, _) -> compare a b)
  in
  Printf.printf "\n%s %7s %8s\n" (Report.pad 16 "тип ПДН") "кейсов" "recall";
  Printf.printf "%s\n" (String.make 56 '-');
  List.iter
    (fun (t, v, n) -> Printf.printf "%s %7d %8.3f  %s\n" (Report.pad 16 t) n v (Report.bar v))
    rows;

  (* негатив *)
  let clean = List.filter (fun r -> r.case.Corpus.expect = "clean") results in
  let dirty = List.filter (fun r -> r.over > 0) clean in
  Printf.printf "\nнегативных кейсов: %d, с ложным маскированием: %d\n" (List.length clean)
    (List.length dirty);
  let broken = List.filter (fun r -> not r.utf8_ok) results in
  if broken = [] then
    Printf.printf "UTF-8 на выходе: цел во всех %d кейсах\n" (List.length results)
  else (
    Printf.printf "ПОРЧА UTF-8 НА ВЫХОДЕ: %d кейсов\n" (List.length broken);
    List.iteri (fun i r -> if i < 10 then Printf.printf "   %s\n" r.case.Corpus.id) broken
  );

  if show_fails then (
    Printf.printf "\n=== не проходят ===\n";
    List.iter
      (fun r ->
        let bad =
          if r.case.Corpus.expect = "clean" then
            r.over > 0
          else
            match r.recall with
            | Some v -> v < 0.999
            | None -> false
        in
        if bad then
          let what =
            if r.case.Corpus.expect = "clean" then
              Printf.sprintf "ложная маска %d Б" r.over
            else
              Printf.sprintf "recall %.2f" (Option.value r.recall ~default:0.)
          in
          Printf.printf "  %s %s %s\n" (Report.pad 22 r.case.Corpus.id) (Report.pad 20 what)
            r.case.Corpus.probes
      )
      results
  )
