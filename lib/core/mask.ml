(* mask.ml — masking of spans.

   Design (spec 4.8):
   - Stars: one '*' per code point, exactly the span length.
   - A byte starts a code point if (b land 0xC0) <> 0x80.
   - Outside the spans the output is byte-for-byte identical to the input
     (invariant 1).

   Modes (spec 4.8):
   - Stars: one '*' per code point. The /process mode.
   - Token: [FIO_1]. The LLM path.
   - Synthetic: substitute data, demo only.

   Only Stars is reachable today: router.ml always asks for it. Selecting the
   mode per consuming system is M6, and it is nearly free — the organisers
   confirmed that "[ФИО_1]" scores the same as stars, so Token is a bonus point
   of criterion 3.7 waiting to be switched on. *)

type mode =
  | Stars
  | Token
  | Synthetic

(* Mask a single span with stars. One '*' per code point, but whitespace
   (spaces, tabs, newlines) within the span is preserved so the mask keeps
   the structure of the original (e.g. "4509 123456" -> "**** ******").
   Holes — byte ranges that are not part of the value (the address service
   words г., ул., д., кв.) — are copied through unmasked. *)
(* Пишет маску спана прямо в выходной буфер.

   Раньше на каждый спан заводился свой Buffer, из него делалась строка, и эта
   строка копировалась в выходной буфер — три объекта и два копирования на
   каждое замаскированное значение. На теле в 400 КБ маска аллоцировала 746
   тысяч слов при том, что сам результат весит 51 тысячу.

   Дырки — байтовые участки, которые не входят в значение (служебные слова
   адреса «г.», «ул.», «д.», «кв.»), — копируются как есть. *)
let blit_span_stars (out : Buffer.t) (buf : string) (s : Spans.span) : unit =
  let stop = s.Spans.start + s.Spans.len in
  (* сортировка только когда дырки есть: у подавляющего большинства спанов их
     нет, а полиморфный compare на парах — вызов caml_compare на сравнение *)
  let holes =
    match s.Spans.holes with
    | [] | [_] -> s.Spans.holes
    | l -> List.sort (fun (a, _) (b, _) -> Int.compare a b) l
  in
  let hole = ref holes in
  let i = ref s.Spans.start in
  while !i < stop do
    let b = String.unsafe_get buf !i in
    (* Пропускаем все дырки, которые уже позади, и только потом проверяем
       текущую. Старый вариант снимал ровно одну дырку за шаг и возвращал false
       для этого же байта — значит первый байт каждой следующей дырки уходил
       под маску. Если это ведущий байт символа, символ рвётся пополам и в
       ответ уезжает битый UTF-8.

       Цикл, а не рекурсивная функция внутри тела: замыкание здесь стоило бы
       блока на каждый байт каждого спана. *)
    let scan = ref true in
    while !scan do
      match !hole with
      | (hs, hl) :: rest when !i >= hs + hl -> hole := rest
      | _ -> scan := false
    done;
    let in_hole =
      match !hole with
      | (hs, hl) :: _ -> !i >= hs && !i < hs + hl
      | [] -> false
    in
    ( if in_hole then
        Buffer.add_char out b
      else
        match Classes.class_of b with
        | Classes.SPACE -> Buffer.add_char out b
        | _ -> if Classes.is_codepoint_start b then Buffer.add_char out '*'
    );
    incr i
  done

(* Mask the input, replacing each span with its mask. Outside spans the input
   is copied byte-for-byte.

   Буфер создаётся сразу на длину входа: звёздочная маска никогда не длиннее
   оригинала (одна звёздочка на кодовую точку), поэтому он не удваивается ни
   разу. Начала спанов — числа, сравниваются Int.compare, а не полиморфным
   compare. *)
let mask (mode : mode) (buf : string) (spans : Spans.span list) : string =
  let n = String.length buf in
  let out = Buffer.create (n + 16) in
  let pos = ref 0 in
  (* Спаны приходят из Spans.glue уже по возрастанию начала; пересортировка
     была бы n log n впустую. Проверка линейная. *)
  let sorted =
    if Spans.is_sorted spans then
      spans
    else
      List.sort (fun a b -> Int.compare a.Spans.start b.Spans.start) spans
  in
  List.iter
    (fun s ->
      (* copy bytes before the span *)
      if s.Spans.start > !pos then Buffer.add_substring out buf !pos (s.Spans.start - !pos);
      ( match mode with
      | Stars | Synthetic -> blit_span_stars out buf s
      | Token ->
          Buffer.add_string out (Printf.sprintf "[%s_%d]" (Spans.ty_name s.Spans.ty) s.Spans.start)
      );
      pos := s.Spans.start + s.Spans.len
    )
    sorted;
  if !pos < n then Buffer.add_substring out buf !pos (n - !pos);
  Buffer.contents out
