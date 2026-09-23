(* jsonio.ml - specialized JSON parsing and building.

   We deliberately avoid a general-purpose JSON library (spec 4.10):
   - On a megabyte body a generic parser makes several copies.
   - yojson escapes non-ASCII as \uXXXX by default, doubling the response.

   Reading: a scanner finds the "payload" and "payload_id" keys and unescapes
   their string values directly into a reusable Buffer. All RFC 8259 section 7
   escapes are handled, including \uXXXX and surrogate pairs.

   Writing: a manual writer. Only the double-quote, backslash and control
   characters below 0x20 are escaped. Non-ASCII is emitted raw (valid per
   RFC 8259 and half the size). *)

(* --- UTF-8 helpers --- *)

(* Decode a \uXXXX escape (RFC 8259 section 7). Returns the code point. *)
let hex_val (c : char) : int =
  match c with
  | '0' .. '9' -> Char.code c - Char.code '0'
  | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
  | _ -> -1

(* Encode a code point as UTF-8 into buf. *)
let add_utf8 (buf : Buffer.t) (cp : int) =
  if cp < 0x80 then
    Buffer.add_char buf (Char.chr cp)
  else if cp < 0x800 then (
    Buffer.add_char buf (Char.chr (0xC0 lor (cp lsr 6)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  ) else if cp < 0x10000 then (
    Buffer.add_char buf (Char.chr (0xE0 lor (cp lsr 12)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  ) else (
    Buffer.add_char buf (Char.chr (0xF0 lor (cp lsr 18)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char buf (Char.chr (0x80 lor (cp land 0x3F)))
  )

(* --- Reading --- *)

type request =
  { payload : string;
    payload_id : string
  }

(* Read a JSON string starting at the opening quote at body.[i]. Returns
   (value, index just past the closing quote), or None on malformed input.
   Handles all RFC 8259 section 7 escapes, including \uXXXX and surrogate
   pairs. *)
let read_string (body : string) (i : int) : (string * int) option =
  let blen = String.length body in
  let buf = Buffer.create 64 in
  let rec go j =
    if j >= blen then
      None
    else
      match body.[j] with
      | '"' -> Some (Buffer.contents buf, j + 1)
      | '\\' when j + 1 < blen -> (
          match body.[j + 1] with
          | '"' ->
              Buffer.add_char buf '"';
              go (j + 2)
          | '\\' ->
              Buffer.add_char buf '\\';
              go (j + 2)
          | '/' ->
              Buffer.add_char buf '/';
              go (j + 2)
          | 'b' ->
              Buffer.add_char buf '\b';
              go (j + 2)
          | 'f' ->
              Buffer.add_char buf '\012';
              go (j + 2)
          | 'n' ->
              Buffer.add_char buf '\n';
              go (j + 2)
          | 'r' ->
              Buffer.add_char buf '\r';
              go (j + 2)
          | 't' ->
              Buffer.add_char buf '\t';
              go (j + 2)
          | 'u' when j + 5 < blen ->
              let h1 = hex_val body.[j + 2] in
              let h2 = hex_val body.[j + 3] in
              let h3 = hex_val body.[j + 4] in
              let h4 = hex_val body.[j + 5] in
              if h1 < 0 || h2 < 0 || h3 < 0 || h4 < 0 then
                None
              else
                let cp = (h1 lsl 12) lor (h2 lsl 8) lor (h3 lsl 4) lor h4 in
                if
                  cp >= 0xD800
                  && cp <= 0xDBFF
                  && j + 11 < blen
                  && body.[j + 6] = '\\'
                  && body.[j + 7] = 'u'
                then (
                  let l1 = hex_val body.[j + 8] in
                  let l2 = hex_val body.[j + 9] in
                  let l3 = hex_val body.[j + 10] in
                  let l4 = hex_val body.[j + 11] in
                  if l1 < 0 || l2 < 0 || l3 < 0 || l4 < 0 then
                    None
                  else
                    let low = (l1 lsl 12) lor (l2 lsl 8) lor (l3 lsl 4) lor l4 in
                    let full = 0x10000 + ((cp - 0xD800) lsl 10) + (low - 0xDC00) in
                    add_utf8 buf full;
                    go (j + 12)
                ) else (
                  add_utf8 buf cp;
                  go (j + 6)
                )
          | _ -> go (j + 2)
        )
      | _ ->
          (* Обычные байты копируются куском до ближайшего спецсимвола, а не по
             одному. В теле на 400 КБ экранированных байтов единицы, а
             Buffer.add_char на каждый байт был одиннадцатью процентами всего
             времени сервиса под нагрузкой. *)
          let k = ref j in
          while !k < blen && body.[!k] <> '"' && body.[!k] <> '\\' do
            incr k
          done;
          Buffer.add_substring buf body j (!k - j);
          go !k
  in
  go (i + 1)

(* Skip a JSON value starting at body.[i]. Returns the index just past it.
   Handles nested objects and arrays with balanced braces/brackets, so a
   top-level key is not shadowed by a same-named key inside a nested value. *)
let skip_value (body : string) (i : int) : int =
  let blen = String.length body in
  if i >= blen then
    (* Тело оборвалось на месте значения: "{\"payload\":" и ничего дальше.
       Без этой проверки чтение уходит за конец строки, обработчик соединения
       падает на Invalid_argument, и клиент получает не 400, а разрыв без
       ответа. Пять таких подряд останавливают весь прогон по Приложению B. *)
    blen
  else
    match body.[i] with
    | '"' -> (
        match read_string body i with
        | Some (_, after) -> after
        | None -> i + 1
      )
    | '{' | '[' ->
        let depth = ref 1 in
        let j = ref (i + 1) in
        let in_str = ref false in
        while !j < blen && !depth > 0 do
          ( match body.[!j] with
          | '"' when not !in_str -> in_str := true
          | '"' when !in_str -> in_str := false
          | '\\' when !in_str -> incr j
          | '{' when not !in_str -> incr depth
          | '[' when not !in_str -> incr depth
          | '}' when not !in_str -> decr depth
          | ']' when not !in_str -> decr depth
          | _ -> ()
          );
          incr j
        done;
        !j
    | _ ->
        (* number, literal, etc: skip to the next comma or brace *)
        let j = ref i in
        while !j < blen && body.[!j] <> ',' && body.[!j] <> '}' && body.[!j] <> ']' do
          incr j
        done;
        !j

(* Find the value of a top-level string key. Returns None if not found.
   Scans the top-level object once, comparing keys byte-by-byte without
   allocating a substring. Nested objects are skipped, so a "payload" inside
   a nested object does not shadow the top-level one. *)
let find_string (body : string) (key : string) : string option =
  let blen = String.length body in
  let result = ref None in
  let i = ref 0 in
  (* skip to the opening '{' *)
  while !i < blen && body.[!i] <> '{' do
    incr i
  done;
  incr i;
  let stop = ref false in
  while (not !stop) && !i < blen && !result = None do
    (* skip whitespace, commas, colons *)
    while
      !i < blen
      && (body.[!i] = ' '
         || body.[!i] = '\t'
         || body.[!i] = '\n'
         || body.[!i] = '\r'
         || body.[!i] = ','
         || body.[!i] = ':'
         )
    do
      incr i
    done;
    if !i >= blen then
      stop := true
    else if body.[!i] = '}' then
      stop := true
    else if body.[!i] = '"' then
      match read_string body !i with
      | Some (k, after) ->
          (* skip to ':' *)
          let j = ref after in
          while !j < blen && body.[!j] <> ':' do
            incr j
          done;
          incr j;
          while
            !j < blen
            && (body.[!j] = ' ' || body.[!j] = '\t' || body.[!j] = '\n' || body.[!j] = '\r')
          do
            incr j
          done;
          if !j < blen && body.[!j] = '"' then
            match read_string body !j with
            | Some (value, after2) ->
                if k = key then result := Some value;
                i := after2
            | None -> stop := true
          else
            (* non-string value: skip the whole value (nested objects too) *)
            i := skip_value body !j
      | None -> stop := true
    else
      incr i
  done;
  !result

(* Parse a /process request body in a single pass, extracting both payload and
   payload_id. Returns None if either is missing. *)
let parse_request (body : string) : request option =
  let blen = String.length body in
  let payload = ref None
  and payload_id = ref None in
  let i = ref 0 in
  (* skip to the opening '{' *)
  while !i < blen && body.[!i] <> '{' do
    incr i
  done;
  incr i;
  let stop = ref false in
  while (not !stop) && !i < blen do
    (* skip whitespace, commas, colons *)
    while
      !i < blen
      && (body.[!i] = ' '
         || body.[!i] = '\t'
         || body.[!i] = '\n'
         || body.[!i] = '\r'
         || body.[!i] = ','
         || body.[!i] = ':'
         )
    do
      incr i
    done;
    if !i >= blen then
      stop := true
    else if body.[!i] = '}' then
      stop := true
    else if body.[!i] = '"' then
      match read_string body !i with
      | Some (key, after) ->
          (* skip to ':' *)
          let j = ref after in
          while !j < blen && body.[!j] <> ':' do
            incr j
          done;
          incr j;
          while
            !j < blen
            && (body.[!j] = ' ' || body.[!j] = '\t' || body.[!j] = '\n' || body.[!j] = '\r')
          do
            incr j
          done;
          if !j < blen && body.[!j] = '"' then
            match read_string body !j with
            | Some (value, after2) ->
                if key = "payload" then
                  payload := Some value
                else if key = "payload_id" then
                  payload_id := Some value;
                i := after2
            | None -> stop := true
          else
            (* non-string value: skip the whole value (nested objects too) *)
            i := skip_value body !j
      | None -> stop := true
    else
      incr i
  done;
  match (!payload, !payload_id) with
  | Some payload, Some payload_id -> Some {payload; payload_id}
  | _ -> None

(* --- Writing --- *)

(* Требует ли байт экранирования в строке JSON? *)
let needs_escape (c : char) : bool = c = '"' || c = '\\' || Char.code c < 0x20

(* Build {"result": "..."} with minimal escaping.

   Байты, которые экранировать не надо, копируются кусками. Посимвольный
   обход с Buffer.add_char на каждый байт ответа в 400 КБ стоил сервису
   одиннадцати процентов времени под нагрузкой — при том, что экранировать в
   русском тексте почти нечего. *)
let result (s : string) : string =
  let n = String.length s in
  let buf = Buffer.create (n + 32) in
  Buffer.add_string buf "{\"result\":\"";
  let i = ref 0 in
  while !i < n do
    let j = ref !i in
    while !j < n && not (needs_escape (String.unsafe_get s !j)) do
      incr j
    done;
    if !j > !i then Buffer.add_substring buf s !i (!j - !i);
    if !j < n then (
      ( match String.unsafe_get s !j with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | '\b' -> Buffer.add_string buf "\\b"
      | '\012' -> Buffer.add_string buf "\\f"
      | c -> Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
      );
      incr j
    );
    i := !j
  done;
  Buffer.add_string buf "\"}";
  Buffer.contents buf

(* Build a simple error object {"error": "..."}. *)
let error (msg : string) : string = Printf.sprintf "{\"error\":\"%s\"}" msg
