(* Мишень для perf и для поштучной разбивки: prof_stage <стадия> <итераций>.
   Стадии: lexer | rules | evidence | each (правила по одному). *)
open Pdmask_core
module Router = Pdmask_http.Router

let () =
  Eio_main.run @@ fun _env ->
  let dicts_dir = "dicts" in
  let dict = Dict.create () in
  let persons = Dictload.load_public_persons dicts_dir in
  Dictload.load dict dicts_dir persons;
  let bank_index = Textindex.of_keys (Dictload.load_bank_offices dicts_dir) in
  let cases = Pdmask_corpus.Corpus.load "tools/bench/corpus/own/cases.txt" in
  let target = try int_of_string Sys.argv.(3) with _ -> 409600 in
  let i_dense = ref 0 in
  (* Два тела на выбор.

     Плотное — корпус ПДН, повторённый до нужного размера. Это худший случай:
     замаскированный спан на каждые восемьдесят байт, чего в живом тексте не
     бывает никогда.

     Реалистичное — обычная проза с вкраплением кейса примерно раз в два
     килобайта, как в деловой переписке. Четвёртым аргументом "prose". *)
  let realistic = Array.length Sys.argv > 4 && Sys.argv.(4) = "prose" in
  let payload =
    let b = Buffer.create (target + 8192) in
    let docs = List.filter (fun (c : Pdmask_corpus.Corpus.case) -> c.size <> "micro") cases in
    let arr = Array.of_list docs in
    if realistic then
      let prose =
        let ic = open_in_bin "tools/bench/corpus/perf/prose_sample.txt" in
        let n = in_channel_length ic in
        let s = really_input_string ic n in
        close_in ic;
        s
      in
      let pos = ref 0
      and i = ref 0 in
      while Buffer.length b < target do
        let chunk = min 2000 (String.length prose - !pos) in
        if chunk <= 0 then
          pos := 0
        else (
          Buffer.add_string b (String.sub prose !pos chunk);
          pos := !pos + chunk;
          Buffer.add_string b "\n";
          Buffer.add_string b arr.(!i mod Array.length arr).Pdmask_corpus.Corpus.text;
          Buffer.add_string b "\n";
          incr i
        )
      done
    else
      while Buffer.length b < target do
        Buffer.add_string b arr.(!i_dense mod Array.length arr).Pdmask_corpus.Corpus.text;
        Buffer.add_string b "\n\n";
        incr i_dense
      done;
    Buffer.contents b
  in
  let toks = Lexer.create () in
  Lexer.lex toks dict payload;
  let cands = Rules.detect payload toks in
  let ctx =
    { Evidence.bank_index;
      public_forms = Dictload.public_forms persons;
      model_tags = Bytes.empty;
      payload;
      payload_cp = Evidence.code_points_capped payload 64;
      toks
    }
  in
  let stage = Sys.argv.(1) in
  let n = int_of_string Sys.argv.(2) in
  let sink = ref 0 in
  (* Минимум, а не среднее: разброс между прогонами до 5%, и минимум — это
     прогон, которому меньше всего мешали. *)
  let time name f =
    let w0 = Gc.minor_words () in
    let best = ref infinity in
    for _ = 1 to n do
      let t0 = Unix.gettimeofday () in
      f ();
      let dt = Unix.gettimeofday () -. t0 in
      if dt < !best then best := dt
    done;
    let dw = (Gc.minor_words () -. w0) /. float_of_int n in
    Printf.printf "%-22s %8.3f мс  %12.0f слов\n%!" name (!best *. 1000.) dw
  in
  ( match stage with
  | "lexer" -> time "лексер" (fun () -> Lexer.lex toks dict payload)
  | "rules" -> time "правила" (fun () -> sink := !sink + List.length (Rules.detect payload toks))
  | "pipeline" ->
      let rctx =
        { Router.store = Store.create ();
          dict;
          bank_index;
          public_forms = Dictload.public_forms persons;
          seqmodel = Seqmodel.load "models/seqmodel.bin";
          config = Atomic.make Config.default_config;
          metrics = Metrics.create ();
          k_master = "bench-master-key-00000000000000000000000000000000";
          otp = Otp.create "bench-otp-secret-00000000000000000000000000000000";
          admin_password = "bench"
        }
      in
      time "конвейер" (fun () ->
          sink := !sink + String.length (Router.mask rctx Config.default_profile payload)
      )
  | "phases" ->
      (* Разбор конвейера по фазам ровно так, как его проходит Router.mask. *)
      let ev = ref []
      and kept = ref []
      and glued = ref []
      and spans = ref [||] in
      let sent = ref [||] in
      time "1 лексер" (fun () -> Lexer.lex toks dict payload);
      time "2 правила" (fun () -> sink := !sink + List.length (Rules.detect payload toks));
      time "3 доказательства" (fun () ->
          ev := List.map (fun s -> (s, Evidence.collect ctx s)) cands;
          sink := !sink + List.length !ev
      );
      time "3a список->массив" (fun () ->
          spans := Array.of_list !ev;
          sink := !sink + Array.length !spans
      );
      time "4 индекс предложений" (fun () ->
          sent := Router.sentence_ids toks (Array.map fst !spans);
          sink := !sink + Array.length !sent
      );
      time "5 решение x2" (fun () ->
          Array.iter
            (fun (s, e) ->
              sink := !sink + Bool.to_int (Decision.decide s.Spans.ty e).Decision.masked
            )
            !spans;
          Array.iter
            (fun (s, e) ->
              sink := !sink + Bool.to_int (Decision.decide s.Spans.ty e).Decision.masked
            )
            !spans
      );
      let masked = List.filter (fun (s, e) -> (Decision.decide s.Spans.ty e).Decision.masked) !ev in
      time "6 пересечения" (fun () ->
          kept := Spans.resolve_by fst masked;
          sink := !sink + List.length !kept
      );
      time "7 склейка" (fun () ->
          glued := Spans.glue (List.map fst !kept);
          sink := !sink + List.length !glued
      );
      time "8 маска" (fun () -> sink := !sink + String.length (Mask.mask Mask.Stars payload !glued))
  | "ev_each" ->
      (* Поштучно по помощникам сбора доказательств, на всех кандидатах. *)
      let arr = Array.of_list cands in
      let lo = Array.map (fun s -> Evidence.token_at toks s.Spans.start) arr in
      let hi = Array.map (fun s -> Evidence.token_at toks (Spans.end_ s - 1)) arr in
      let each name f = time name (fun () -> Array.iteri (fun k s -> sink := !sink + f k s) arr) in
      each "token_at x2" (fun _ s ->
          Bool.to_int (Evidence.token_at toks s.Spans.start >= 0)
          + Bool.to_int (Evidence.token_at toks (Spans.end_ s - 1) >= 0)
      );
      each "scan_env x2" (fun k _ ->
          Evidence.scan_env toks (lo.(k) - 1) (-1) 5 8 lor Evidence.scan_env toks (hi.(k) + 1) 1 5 8
      );
      each "starts_capital" (fun _ s -> Bool.to_int (Evidence.starts_capital payload s));
      each "has_form" (fun k s ->
          Bool.to_int (Evidence.has_form ctx lo.(k) hi.(k) s (Evidence.span_text ctx s))
      );
      each "inside_quotes" (fun _ s -> Bool.to_int (Evidence.inside_quotes ctx s));
      each "before_quote" (fun _ s -> Bool.to_int (Evidence.before_quote ctx s));
      each "checksum_ok" (fun _ s -> Bool.to_int (Evidence.checksum_ok ctx s));
      each "public_full" (fun _ s -> Bool.to_int (Evidence.match_public_full ctx s));
      each "public_surn" (fun k _ -> Bool.to_int (Evidence.match_public_surn ctx lo.(k) hi.(k)));
      each "find_head_before x2" (fun k _ ->
          Bool.to_int (Evidence.find_head_before ctx lo.(k) Dict.Flag.eponym_head >= 0)
          + Bool.to_int (Evidence.find_head_before ctx lo.(k) Dict.Flag.possess_head >= 0)
      );
      each "bank_office" (fun _ s -> Bool.to_int (Evidence.matches_bank_office ctx s));
      each "flat_number" (fun _ s ->
          Bool.to_int (Evidence.has_flat_number (Evidence.span_text ctx s))
      );
      each "span_text" (fun _ s -> String.length (Evidence.span_text ctx s));
      time "collect целиком" (fun () ->
          List.iter (fun c -> sink := !sink + List.length (Evidence.collect ctx c)) cands
      )
  | "model" -> (
      match Seqmodel.load "models/seqmodel.bin" with
      | None -> print_endline "модель не найдена"
      | Some m ->
          let st = Seqmodel.make_state () in
          time "модель, всё тело" (fun () ->
              sink :=
                !sink + List.length (Seqmodel.tag_range m st dict toks payload 0 (toks.Lexer.n - 1))
          );
          let ents = Seqmodel.tag_range m st dict toks payload 0 (toks.Lexer.n - 1) in
          Printf.printf "сущностей найдено: %d\n" (List.length ents)
    )
  | "evidence" ->
      time "доказательства" (fun () ->
          List.iter (fun c -> sink := !sink + List.length (Evidence.collect ctx c)) cands
      )
  | "each" ->
      let acc = ref [] in
      let runs = Rules.digit_runs payload toks in
      time "digit_runs" (fun () -> sink := !sink + List.length (Rules.digit_runs payload toks));
      let r name f =
        time name (fun () ->
            acc := [];
            f acc;
            sink := !sink + List.length !acc
        )
      in
      r "fio" (fun a -> Rules.rule_fio payload toks a);
      r "date" (fun a -> Rules.rule_date toks runs a);
      r "date_words" (fun a -> Rules.rule_date_words payload toks a);
      r "passport" (fun a -> Rules.rule_passport payload toks runs a);
      r "passport_split" (fun a -> Rules.rule_passport_split payload toks runs a);
      r "extra_docs" (fun a -> Rules.rule_extra_docs payload toks runs a);
      r "dept_code" (fun a -> Rules.rule_dept_code runs a);
      r "inn" (fun a -> Rules.rule_inn runs a);
      r "card" (fun a -> Rules.rule_card runs a);
      r "phone" (fun a -> Rules.rule_phone payload toks a);
      r "email" (fun a -> Rules.rule_email payload toks a);
      r "citizenship" (fun a -> Rules.rule_citizenship toks a);
      r "birth_place" (fun a -> Rules.rule_birth_place toks a);
      r "issuer" (fun a -> Rules.rule_issuer payload toks a);
      r "index" (fun a -> Rules.rule_index toks runs a);
      r "address" (fun a -> Rules.rule_address payload toks a);
      r "cvv" (fun a -> Rules.rule_cvv toks runs a);
      r "pin" (fun a -> Rules.rule_pin toks runs a);
      r "card_holder" (fun a -> Rules.rule_card_holder payload toks a)
  | s -> failwith ("неизвестная стадия: " ^ s)
  );
  (* сколько кандидатов какого типа и сколько из них переживает решение *)
  let tally = Hashtbl.create 32 in
  List.iter
    (fun (c : Spans.span) ->
      let ev = Evidence.collect ctx c in
      let m = (Decision.decide c.Spans.ty ev).Decision.masked in
      let all, ok = try Hashtbl.find tally c.Spans.ty with Not_found -> (0, 0) in
      Hashtbl.replace tally c.Spans.ty (all + 1, ok + Bool.to_int m)
    )
    cands;
  let rows = Hashtbl.fold (fun k (a, o) acc -> (Spans.ty_name k, a, o) :: acc) tally [] in
  let rows = List.sort (fun (_, a, _) (_, b, _) -> Int.compare b a) rows in
  Printf.printf "\nкандидаты по типам (всего / прошли порог):\n";
  List.iter
    (fun (n, a, o) -> Printf.printf "  %-16s %6d %6d  %3d%%\n" n a o (100 * o / max 1 a))
    rows;
  let flagged = ref 0
  and words = ref 0 in
  for i = 0 to toks.Lexer.n - 1 do
    if toks.Lexer.flags.(i) <> 0 then incr flagged;
    match toks.Lexer.kind.(i) with
    | Lexer.WORD_CYR | Lexer.WORD_LAT -> incr words
    | _ -> ()
  done;
  Printf.printf "payload=%d токенов=%d слов=%d с флагами=%d кандидатов=%d sink=%d\n"
    (String.length payload) toks.Lexer.n !words !flagged (List.length cands) !sink
