(* Сверка реализации признаков: читает предложения (токены через пробел) со
   стандартного входа, печатает предсказанные теги. Ровно те же предложения
   прогоняются питоновской реализацией, и теги обязаны совпасть. *)
open Pdmask_core

let () =
  Eio_main.run @@ fun _ ->
  let dict = Dict.create () in
  let persons = Dictload.load_public_persons "dicts" in
  Dictload.load dict "dicts" persons;
  match Seqmodel.load "models/seqmodel.bin" with
  | None ->
      prerr_endline "модель не загрузилась";
      exit 1
  | Some m -> (
      let st = Seqmodel.make_state () in
      let toks = Lexer.create () in
      let names = [|"PER"; "LOC"; "ORG"|] in
      try
        while true do
          let line = input_line stdin in
          Lexer.lex toks dict line;
          let n = toks.Lexer.n in
          let tags = Array.make n "O" in
          let ents = Seqmodel.tag_range m st dict toks line 0 (n - 1) in
          List.iter
            (fun (e : Seqmodel.ent) ->
              tags.(e.Seqmodel.elo) <- "B-" ^ names.(e.Seqmodel.ety);
              for i = e.Seqmodel.elo + 1 to e.Seqmodel.ehi do
                tags.(i) <- "I-" ^ names.(e.Seqmodel.ety)
              done
            )
            ents;
          let out = ref [] in
          for i = n - 1 downto 0 do
            match toks.Lexer.kind.(i) with
            | Lexer.SPACE -> ()
            | _ -> out := tags.(i) :: !out
          done;
          print_endline (String.concat " " !out)
        done
      with End_of_file -> ()
    )
