(* corpus.ml — загрузка корпуса из bench/corpus/cases.txt.

   Корпус — один текстовый файл, который правится руками. Значения ПДН в нём
   размечены как {{тип|значение}}; разметка снимается здесь, а смещения спанов
   вычисляются из неё. Поэтому эталон не может разойтись с текстом: он и есть
   текст.

   Формат записи:
     @case id=<id> size=<class> polarity=<pos|neg|mixed> expect=<mask|clean>
     @probes <что кейс вскрывает>
     @text
     <текст, сколько угодно строк>
     @end

   Смещения байтовые, а не символьные: сервис работает с байтами, и эталон
   должен считаться так же — иначе кириллица сдвинет всё вдвое. *)

type span =
  { start : int;
    stop : int;
    ty : string
  }

type case =
  { id : string;
    size : string; (* micro | sentence | document *)
    polarity : string; (* pos | neg | mixed *)
    expect : string; (* mask | clean *)
    probes : string;
    text : string;
    spans : span list
  }

(* Снимает разметку {{тип|значение}} и возвращает чистый текст со спанами. *)
let strip (raw : string) : string * span list =
  let buf = Buffer.create (String.length raw) in
  let spans = ref [] in
  let n = String.length raw in
  let i = ref 0 in
  while !i < n do
    if !i + 1 < n && raw.[!i] = '{' && raw.[!i + 1] = '{' then (
      let bar = ref (!i + 2) in
      while !bar < n && raw.[!bar] <> '|' do
        incr bar
      done;
      let close = ref !bar in
      while !close + 1 < n && not (raw.[!close] = '}' && raw.[!close + 1] = '}') do
        incr close
      done;
      if !bar < n && !close + 1 < n then (
        let ty = String.sub raw (!i + 2) (!bar - !i - 2) in
        let value = String.sub raw (!bar + 1) (!close - !bar - 1) in
        let start = Buffer.length buf in
        Buffer.add_string buf value;
        spans := {start; stop = Buffer.length buf; ty} :: !spans;
        i := !close + 2
      ) else (
        Buffer.add_char buf raw.[!i];
        incr i
      )
    ) else (
      Buffer.add_char buf raw.[!i];
      incr i
    )
  done;
  (Buffer.contents buf, List.rev !spans)

(* "id=micro-fio-01" -> ("id", "micro-fio-01") *)
let split_attr (s : string) : (string * string) option =
  match String.index_opt s '=' with
  | None -> None
  | Some k -> Some (String.sub s 0 k, String.sub s (k + 1) (String.length s - k - 1))

let attrs (line : string) : (string * string) list =
  String.split_on_char ' ' line |> List.filter_map split_attr

let attr (a : (string * string) list) (k : string) (default : string) : string =
  match List.assoc_opt k a with
  | Some v -> v
  | None -> default

let starts_with (s : string) (p : string) : bool =
  String.length s >= String.length p && String.sub s 0 (String.length p) = p

let load (path : string) : case list =
  let content = In_channel.with_open_bin path In_channel.input_all in
  let lines = String.split_on_char '\n' content in
  let cases = ref [] in
  let cur = ref None in
  let probes = ref "" in
  let body = Buffer.create 256 in
  let in_text = ref false in
  List.iter
    (fun line ->
      if !in_text then
        if starts_with line "@end" then (
          in_text := false;
          match !cur with
          | None -> ()
          | Some a ->
              (* последний перевод строки принадлежит разделителю, не тексту *)
              let raw = Buffer.contents body in
              let raw =
                if String.length raw > 0 && raw.[String.length raw - 1] = '\n' then
                  String.sub raw 0 (String.length raw - 1)
                else
                  raw
              in
              let text, spans = strip raw in
              cases :=
                { id = attr a "id" "?";
                  size = attr a "size" "sentence";
                  polarity = attr a "polarity" "pos";
                  expect = attr a "expect" "mask";
                  probes = !probes;
                  text;
                  spans
                }
                :: !cases;
              cur := None;
              probes := "";
              Buffer.clear body
        ) else (
          Buffer.add_string body line;
          Buffer.add_char body '\n'
        )
      else if starts_with line "@case " then
        cur := Some (attrs line)
      else if starts_with line "@probes " then
        probes := String.sub line 8 (String.length line - 8)
      else if starts_with line "@text" then
        in_text := true
    )
    lines;
  List.rev !cases
