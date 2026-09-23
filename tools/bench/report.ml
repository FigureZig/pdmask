(* report.ml — форматирование табличек отчёта.

   Вынесено из score_pdmask: выравнивание по кодовым точкам и полоска прогресса
   нужны всем инструментам, которые печатают метрики, и не имеют отношения к
   тому, что именно измеряется. *)

(* Printf дополняет по байтам, а кириллическая буква занимает два — поэтому
   ширину колонок считаем в кодовых точках. *)
let pad (width : int) (s : string) : string =
  let cp = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr cp) s;
  if !cp >= width then
    s
  else
    s ^ String.make (width - !cp) ' '

let bar (v : float) : string =
  let filled = int_of_float ((v *. 20.) +. 0.5) in
  String.concat ""
    (List.init 20 (fun i ->
         if i < filled then
           "#"
         else
           "."
     )
    )
