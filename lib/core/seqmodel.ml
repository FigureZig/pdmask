(* seqmodel.ml — последовательная модель распознавания имён и мест.

   Структурный усреднённый перцептрон, обученный на Collection3 (русский
   NER-корпус), с признаками из орфографии, морфологических суффиксов и
   ФЛАГОВ НАШИХ СЛОВАРЕЙ. Это и есть гибрид: словарь не решает сам, а входит
   в модель одним из признаков наряду с формой слова и окончанием.

   Зачем вообще модель, если есть правила. Правила ловят то, что есть в
   словаре. Абляция при обучении показала, что модель БЕЗ словарных признаков
   даёт по персонам F1 0.937 против 0.952 со словарём — то есть почти весь
   сигнал несут форма и окончание, а не список. Значит модель узнаёт фамилию,
   которой нет ни в одном словаре, а правила — нет.

   Почему перцептрон, а не трансформер: у нас бюджет в доли миллисекунды на
   запрос, а T5-small по опубликованным замерам тратит 1.46 с на сообщение.
   Viterbi по семи тегам — это сложения целых чисел и один проход.

   Признаки описаны в tools/model/features.py и повторены здесь ОДИН В ОДИН.
   Любое расхождение делает веса бессмысленными молча, поэтому есть отдельная
   сверка: tools/model/verify.py прогоняет одни и те же предложения через обе
   реализации и сравнивает теги.

   Формат файла модели — см. tools/model/export.py. *)

let magic = "PDMSEQ01"

type t =
  { ntags : int;
    nfeat : int;
    tbl_mask : int;
    tbl_hash : int array; (* открытая адресация, 0 = пусто *)
    tbl_id : int array;
    trans : float array; (* (ntags+1) * ntags, строка ntags — начальное состояние *)
    w : float array (* nfeat * ntags *)
  }

(* --- чтение двоичного файла --- *)

let ru32 (s : string) (off : int) : int = Int32.to_int (String.get_int32_le s off)

let rf32 (s : string) (off : int) : float = Int32.float_of_bits (String.get_int32_le s off)

let ru64 (s : string) (off : int) : int = Int64.to_int (String.get_int64_le s off)

let load (path : string) : t option =
  match open_in_bin path with
  | exception _ -> None
  | ic ->
      let n = in_channel_length ic in
      let s = really_input_string ic n in
      close_in ic;
      if String.length s < 20 || String.sub s 0 8 <> magic then
        None
      else
        let ntags = ru32 s 8 in
        let nfeat = ru32 s 12 in
        let size = ru32 s 16 in
        let o = ref 20 in
        let trans = Array.make ((ntags + 1) * ntags) 0.0 in
        for i = 0 to ((ntags + 1) * ntags) - 1 do
          trans.(i) <- rf32 s (!o + (4 * i))
        done;
        o := !o + (4 * (ntags + 1) * ntags);
        let th = Array.make size 0 in
        for i = 0 to size - 1 do
          th.(i) <- ru64 s (!o + (8 * i))
        done;
        o := !o + (8 * size);
        let ti = Array.make size 0 in
        for i = 0 to size - 1 do
          ti.(i) <- ru32 s (!o + (4 * i))
        done;
        o := !o + (4 * size);
        let w = Array.make (nfeat * ntags) 0.0 in
        for i = 0 to (nfeat * ntags) - 1 do
          w.(i) <- rf32 s (!o + (4 * i))
        done;
        Some {ntags; nfeat; tbl_mask = size - 1; tbl_hash = th; tbl_id = ti; trans; w}

(* --- хеш признака, считается без построения строки ---

   Признак — это конкатенация нескольких кусков («suf3=» и три последних
   символа слова). Материализовать её значило бы аллоцировать строку на каждый
   признак каждого токена, то есть сотни аллокаций на предложение. Хеш
   накапливается по кускам. *)

let fnv_off = 0x3bf29ce484222325

let fnv_prime = 0x100000001b3

let hmask = max_int (* 62 бита, совпадает с маской в export.py *)

let hb (h : int) (b : int) : int = h lxor b * fnv_prime land hmask

let hs (h : int) (s : string) : int =
  let r = ref h in
  for i = 0 to String.length s - 1 do
    r := hb !r (Char.code (String.unsafe_get s i))
  done;
  !r

let hsub (h : int) (s : string) (off : int) (len : int) : int =
  let r = ref h in
  for i = off to off + len - 1 do
    r := hb !r (Char.code (String.unsafe_get s i))
  done;
  !r

let hint (h : int) (n : int) : int =
  if n < 0 then
    hs (hb h (Char.code '-')) (string_of_int (-n))
  else
    hs h (string_of_int n)

let lookup (m : t) (h : int) : int =
  let h =
    if h = 0 then
      1
    else
      h
  in
  let p = ref (h land m.tbl_mask) in
  let res = ref (-1) in
  let go = ref true in
  while !go do
    let v = Array.unsafe_get m.tbl_hash !p in
    if v = 0 then
      go := false
    else if v = h then (
      res := Array.unsafe_get m.tbl_id !p;
      go := false
    ) else
      p := (!p + 1) land m.tbl_mask
  done;
  !res

(* --- разбор токена на символы UTF-8 ---

   Суффиксы, префиксы, длина и регистр считаются по СИМВОЛАМ: в кириллице
   символ занимает два байта, и «последние три символа» это шесть байт. *)

let max_chars = 64

let max_bytes = 192

type scratch =
  { mutable nch : int;
    coff : int array; (* смещение символа в fold *)
    clen : int array;
    fold : Bytes.t (* свёрнутый токен *)
  }

let make_scratch () =
  { nch = 0;
    coff = Array.make (max_chars + 1) 0;
    clen = Array.make (max_chars + 1) 0;
    fold = Bytes.create max_bytes
  }

(* Свернуть токен buf[off..off+len) в scratch и разметить символы. *)
let take (sc : scratch) (buf : string) (off : int) (len : int) : unit =
  let len = min len max_bytes in
  let i = ref 0
  and n = ref 0 in
  while !i < len && !n < max_chars do
    let b = String.unsafe_get buf (off + !i) in
    let c = Char.code b in
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
        1
    in
    let w = min w (len - !i) in
    if w = 2 && (c = 0xD0 || c = 0xD1) then (
      let p = Classes.fold_pair b (String.unsafe_get buf (off + !i + 1)) in
      Bytes.unsafe_set sc.fold !i (Char.unsafe_chr (p lsr 8));
      Bytes.unsafe_set sc.fold (!i + 1) (Char.unsafe_chr (p land 0xFF))
    ) else
      for k = 0 to w - 1 do
        let bb = String.unsafe_get buf (off + !i + k) in
        Bytes.unsafe_set sc.fold (!i + k)
          ( if k = 0 then
              Classes.fold_byte bb
            else
              bb
          )
      done;
    sc.coff.(!n) <- !i;
    sc.clen.(!n) <- w;
    incr n;
    i := !i + w
  done;
  sc.nch <- !n;
  sc.coff.(!n) <- !i

(* --- классы символов исходного (несвёрнутого) токена --- *)

let is_digit_at (buf : string) (o : int) (w : int) : bool =
  w = 1 && buf.[o] >= '0' && buf.[o] <= '9'

let is_upper_at (buf : string) (o : int) (w : int) : bool =
  if w = 1 then
    buf.[o] >= 'A' && buf.[o] <= 'Z'
  else if w = 2 then
    let a = Char.code buf.[o]
    and b = Char.code buf.[o + 1] in
    a = 0xD0 && ((b >= 0x90 && b <= 0xAF) || b = 0x81)
  else
    false

let is_lower_at (buf : string) (o : int) (w : int) : bool =
  if w = 1 then
    buf.[o] >= 'a' && buf.[o] <= 'z'
  else if w = 2 then
    let a = Char.code buf.[o]
    and b = Char.code buf.[o + 1] in
    (a = 0xD0 && b >= 0xB0) || (a = 0xD1 && (b <= 0x8F || b = 0x91))
  else
    false

let is_alpha_at (buf : string) (o : int) (w : int) : bool =
  is_upper_at buf o w || is_lower_at buf o w

(* Соответствует features.shape в Python. *)
let shape (sc : scratch) (buf : string) (off : int) : int =
  let n = sc.nch in
  if n = 0 then
    0
  else
    let alldig = ref true
    and letters = ref 0
    and allup = ref true
    and alllow = ref true in
    for k = 0 to n - 1 do
      let o = off + sc.coff.(k)
      and w = sc.clen.(k) in
      if not (is_digit_at buf o w) then alldig := false;
      if is_alpha_at buf o w then (
        incr letters;
        if not (is_upper_at buf o w) then allup := false;
        if not (is_lower_at buf o w) then alllow := false
      )
    done;
    if !alldig then
      4
    (* SHAPE_DIGIT *)
    else if !letters = 0 then
      5
    (* SHAPE_PUNCT *)
    else if !allup && !letters > 1 then
      3
    (* SHAPE_ALLCAP *)
    else if is_upper_at buf (off + sc.coff.(0)) sc.clen.(0) then
      2
    (* SHAPE_CAP *)
    else if !alllow then
      1
    (* SHAPE_LOWER *)
    else
      0
(* SHAPE_OTHER *)

let lenbucket (n : int) : int =
  if n <= 2 then
    n
  else if n <= 4 then
    3
  else if n <= 6 then
    4
  else if n <= 9 then
    5
  else
    6

(* --- морфология: русское имя размечает себя окончанием --- *)

let patr_suf = [|"ович"; "евич"; "ьич"; "овна"; "евна"; "ична"; "инична"; "иничн"|]

let surn_suf =
  [| "ов";
     "ев";
     "ин";
     "ын";
     "ский";
     "цкий";
     "ская";
     "цкая";
     "ской";
     "ко";
     "ук";
     "юк";
     "ян";
     "дзе";
     "швили";
     "ия";
     "их";
     "ых";
     "ова";
     "ева";
     "ина";
     "ына";
     "ову";
     "еву";
     "ину";
     "овым";
     "евым";
     "иным";
     "овой";
     "евой";
     "иной";
     "овы";
     "евы";
     "ины"
  |]

let ends_with (sc : scratch) (suf : string) : bool =
  let ls = String.length suf
  and lb = sc.coff.(sc.nch) in
  ls <= lb
  &&
  let ok = ref true in
  for i = 0 to ls - 1 do
    if Bytes.unsafe_get sc.fold (lb - ls + i) <> String.unsafe_get suf i then ok := false
  done;
  !ok

let morph (sc : scratch) : int =
  let m = ref 0 in
  Array.iter (fun s -> if !m land 1 = 0 && ends_with sc s then m := !m lor 1) patr_suf;
  Array.iter (fun s -> if !m land 2 = 0 && ends_with sc s then m := !m lor 2) surn_suf;
  !m

(* --- сопоставление флагов словаря с битами модели ---

   Порядок обязан совпадать с FLAG_FILES в features.py. *)

let kw_any =
  Dict.Flag.kw_passport
  lor Dict.Flag.kw_birth
  lor Dict.Flag.kw_issue
  lor Dict.Flag.kw_dept
  lor Dict.Flag.kw_dl
  lor Dict.Flag.kw_addr
  lor Dict.Flag.kw_inn
  lor Dict.Flag.kw_card
  lor Dict.Flag.kw_cvv
  lor Dict.Flag.kw_cvv_weak
  lor Dict.Flag.kw_pin
  lor Dict.Flag.kw_holder
  lor Dict.Flag.kw_citizen
  lor Dict.Flag.kw_org
  lor Dict.Flag.kw_birthplace
  lor Dict.Flag.kw_phone
  lor Dict.Flag.kw_doc

let model_flags (f : int) : int =
  let b = ref 0 in
  if f land Dict.Flag.name <> 0 then b := !b lor 1;
  if f land Dict.Flag.surn <> 0 then b := !b lor 2;
  if f land Dict.Flag.patr <> 0 then b := !b lor 4;
  if f land Dict.Flag.geo <> 0 then b := !b lor 8;
  if f land Dict.Flag.country <> 0 then b := !b lor 16;
  if f land Dict.Flag.role <> 0 then b := !b lor 32;
  if f land Dict.Flag.month <> 0 then b := !b lor 64;
  if f land Dict.Flag.addr_marker <> 0 then b := !b lor 128;
  if f land Dict.Flag.stop_ctx <> 0 then b := !b lor 256;
  if f land Dict.Flag.eponym_head <> 0 then b := !b lor 512;
  if f land Dict.Flag.possess_head <> 0 then b := !b lor 1024;
  if f land kw_any <> 0 then b := !b lor 2048;
  !b

let nflags = 12

(* --- подготовленное предложение ---

   Всё, что нужно признакам, считается один раз на токен: свёрнутые байты,
   границы суффиксов и префиксов по символам, форма, флаги, морфология.
   Дальше в горячем цикле только арифметика и обращения в таблицу. *)

type prep =
  { mutable cap : int;
    mutable len : int;
    mutable fbuf : Bytes.t;
    mutable fend : int;
    mutable foff : int array;
    mutable flen : int array;
    mutable nch : int array;
    mutable suf : int array; (* 3 на токен: смещения последних 2,3,4 символов *)
    mutable pre : int array; (* 2 на токен: длины первых 2,3 символов *)
    mutable shp : int array;
    mutable flg : int array;
    mutable mor : int array;
    mutable tok : int array (* индекс в исходном массиве токенов *)
  }

let make_prep () =
  { cap = 0;
    len = 0;
    fbuf = Bytes.create 4096;
    fend = 0;
    foff = [||];
    flen = [||];
    nch = [||];
    suf = [||];
    pre = [||];
    shp = [||];
    flg = [||];
    mor = [||];
    tok = [||]
  }

let ensure_prep (p : prep) (n : int) =
  if n > p.cap then (
    let c = max 256 (max n (2 * p.cap)) in
    p.cap <- c;
    p.foff <- Array.make c 0;
    p.flen <- Array.make c 0;
    p.nch <- Array.make c 0;
    p.suf <- Array.make (3 * c) (-1);
    p.pre <- Array.make (2 * c) (-1);
    p.shp <- Array.make c 0;
    p.flg <- Array.make c 0;
    p.mor <- Array.make c 0;
    p.tok <- Array.make c 0
  )

(* --- небольшие константы, чтобы не звать string_of_int в горячем цикле --- *)

let dig = [|"0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "11"; "12"; "13"; "14"; "15"|]

let off_lbl = [|"-2"; "-1"; "+1"; "+2"|]

let off_val = [|-2; -1; 1; 2|]

let h0 = fnv_off

(* --- вычисление признаков позиции и их вклада в оценки тегов --- *)

let add_feat (m : t) (h : int) (sc : float array) (base : int) =
  let id = lookup m h in
  if id >= 0 then
    let wb = id * m.ntags in
    for t = 0 to m.ntags - 1 do
      sc.(base + t) <- sc.(base + t) +. Array.unsafe_get m.w (wb + t)
    done

let score_pos (m : t) (p : prep) (i : int) (sc : float array) =
  let nt = m.ntags in
  let base = i * nt in
  let fb = Bytes.unsafe_to_string p.fbuf in
  let o = p.foff.(i)
  and l = p.flen.(i) in
  add_feat m (hsub (hs h0 "w=") fb o l) sc base;
  add_feat m (hs (hs h0 "sh=") dig.(p.shp.(i))) sc base;
  add_feat m (hs (hs h0 "len=") dig.(lenbucket p.nch.(i))) sc base;
  for k = 0 to 2 do
    let s = p.suf.((3 * i) + k) in
    if s >= 0 then
      add_feat m (hsub (hs (hs (hs h0 "suf") dig.(k + 2)) "=") fb (o + s) (l - s)) sc base
  done;
  for k = 0 to 1 do
    let e = p.pre.((2 * i) + k) in
    if e >= 0 then add_feat m (hsub (hs (hs (hs h0 "pre") dig.(k + 2)) "=") fb o e) sc base
  done;
  let fl = p.flg.(i) in
  for b = 0 to nflags - 1 do
    if fl land (1 lsl b) <> 0 then add_feat m (hs (hs h0 "d") dig.(b)) sc base
  done;
  let mo = p.mor.(i) in
  if mo land 1 <> 0 then add_feat m (hs h0 "mpatr") sc base;
  if mo land 2 <> 0 then add_feat m (hs h0 "msurn") sc base;
  if i = 0 then add_feat m (hs h0 "bos") sc base;
  if i = p.len - 1 then add_feat m (hs h0 "eos") sc base;
  for k = 0 to 3 do
    let off = off_val.(k) in
    let lbl = off_lbl.(k) in
    let j = i + off in
    if j >= 0 && j < p.len then (
      add_feat m (hs (hs (hs (hs h0 "sh") lbl) "=") dig.(p.shp.(j))) sc base;
      let fj = p.flg.(j) in
      for b = 0 to nflags - 1 do
        if fj land (1 lsl b) <> 0 then add_feat m (hs (hs (hs (hs h0 "d") lbl) "_") dig.(b)) sc base
      done;
      if off = -1 || off = 1 then (
        add_feat m (hsub (hs (hs (hs h0 "w") lbl) "=") fb p.foff.(j) p.flen.(j)) sc base;
        let mj = p.mor.(j) in
        if mj land 1 <> 0 then add_feat m (hs (hs h0 "mpatr") lbl) sc base;
        if mj land 2 <> 0 then add_feat m (hs (hs h0 "msurn") lbl) sc base
      )
    ) else
      add_feat m (hs (hs (hs (hs h0 "sh") lbl) "=") "X") sc base
  done;
  if i > 0 then
    add_feat m (hs (hs (hs (hs h0 "shb=") dig.(p.shp.(i - 1))) "_") dig.(p.shp.(i))) sc base

(* --- подготовка последовательности и разбор --- *)

type state =
  { p : prep;
    s : scratch;
    mutable sco : float array;
    mutable dp : float array;
    mutable bp : int array;
    mutable path : int array
  }

let make_state () =
  {p = make_prep (); s = make_scratch (); sco = [||]; dp = [||]; bp = [||]; path = [||]}

(* Модель работает по содержательным токенам: пробелы из последовательности
   выбрасываются, как и в корпусе, где токенизация уже сделана. *)
let prepare (st : state) (dict : Dict.t) (toks : Lexer.toks) (buf : string) (lo : int) (hi : int) :
    unit =
  let p = st.p in
  let n = ref 0 in
  for i = lo to hi do
    match toks.Lexer.kind.(i) with
    | Lexer.SPACE -> ()
    | _ -> incr n
  done;
  ensure_prep p !n;
  p.len <- !n;
  p.fend <- 0;
  let k = ref 0 in
  for i = lo to hi do
    match toks.Lexer.kind.(i) with
    | Lexer.SPACE -> ()
    | _ ->
        let off = toks.Lexer.start.(i)
        and len = toks.Lexer.len.(i) in
        take st.s buf off len;
        let fl = st.s.coff.(st.s.nch) in
        if p.fend + fl + 1 > Bytes.length p.fbuf then (
          let b = Bytes.create (max (2 * Bytes.length p.fbuf) (p.fend + fl + 1)) in
          Bytes.blit p.fbuf 0 b 0 p.fend;
          p.fbuf <- b
        );
        Bytes.blit st.s.fold 0 p.fbuf p.fend fl;
        p.foff.(!k) <- p.fend;
        p.flen.(!k) <- fl;
        p.nch.(!k) <- st.s.nch;
        for j = 0 to 2 do
          let c = j + 2 in
          p.suf.((3 * !k) + j) <-
            ( if st.s.nch >= c then
                st.s.coff.(st.s.nch - c)
              else
                -1
            )
        done;
        for j = 0 to 1 do
          let c = j + 2 in
          p.pre.((2 * !k) + j) <-
            ( if st.s.nch >= c then
                st.s.coff.(c)
              else
                -1
            )
        done;
        p.shp.(!k) <- shape st.s buf off;
        p.flg.(!k) <- model_flags (Dict.find dict buf off len);
        p.mor.(!k) <- morph st.s;
        p.tok.(!k) <- i;
        p.fend <- p.fend + fl;
        incr k
  done

type ent =
  { ety : int; (* 0 = PER, 1 = LOC, 2 = ORG *)
    elo : int; (* индекс первого токена в исходном массиве *)
    ehi : int;
    (* Есть ли у сущности словарная или морфологическая опора. Модель обучена
       на новостях и охотно принимает за имя название марки: «Хендай Солярис»
       она размечает как персону. У настоящего русского имени есть либо
       словарный флаг, либо окончание -ов/-ин/-ский/-ович. Опора позволяет
       отличить одно от другого, не отказываясь от модели целиком. *)
    esup : bool
  }

let decode (m : t) (st : state) : ent list =
  let n = st.p.len
  and nt = m.ntags in
  if n = 0 then
    []
  else (
    if Array.length st.sco < n * nt then (
      st.sco <- Array.make (n * nt * 2) 0.0;
      st.dp <- Array.make (n * nt * 2) 0.0;
      st.bp <- Array.make (n * nt * 2) 0
    );
    if Array.length st.path < n then st.path <- Array.make (2 * n) 0;
    Array.fill st.sco 0 (n * nt) 0.0;
    for i = 0 to n - 1 do
      score_pos m st.p i st.sco
    done;
    (* Viterbi *)
    for t = 0 to nt - 1 do
      st.dp.(t) <- m.trans.((nt * nt) + t) +. st.sco.(t)
    done;
    for i = 1 to n - 1 do
      let bi = i * nt
      and pi = (i - 1) * nt in
      for t = 0 to nt - 1 do
        let best = ref neg_infinity
        and arg = ref 0 in
        for q = 0 to nt - 1 do
          let v = st.dp.(pi + q) +. m.trans.((q * nt) + t) in
          if v > !best then (
            best := v;
            arg := q
          )
        done;
        st.dp.(bi + t) <- !best +. st.sco.(bi + t);
        st.bp.(bi + t) <- !arg
      done
    done;
    let last = (n - 1) * nt in
    let best = ref neg_infinity
    and arg = ref 0 in
    for t = 0 to nt - 1 do
      if st.dp.(last + t) > !best then (
        best := st.dp.(last + t);
        arg := t
      )
    done;
    let path = st.path in
    path.(n - 1) <- !arg;
    for i = n - 1 downto 1 do
      path.(i - 1) <- st.bp.((i * nt) + path.(i))
    done;
    (* BIO -> сущности *)
    let out = ref [] in
    let i = ref 0 in
    while !i < n do
      let t = path.(!i) in
      if t >= 1 && t land 1 = 1 then (
        (* B-тег: 1=B-PER, 3=B-LOC, 5=B-ORG *)
        let ty = (t - 1) / 2 in
        let j = ref (!i + 1) in
        while !j < n && path.(!j) = t + 1 do
          incr j
        done;
        let sup = ref false in
        for q = !i to !j - 1 do
          let fl = st.p.flg.(q)
          and mo = st.p.mor.(q) in
          if fl land (1 lor 2 lor 4 lor 8 lor 16) <> 0 || mo <> 0 then sup := true
        done;
        out := {ety = ty; elo = st.p.tok.(!i); ehi = st.p.tok.(!j - 1); esup = !sup} :: !out;
        i := !j
      ) else
        incr i
    done;
    List.rev !out
  )

let tag_range (m : t) (st : state) (dict : Dict.t) (toks : Lexer.toks) (buf : string) (lo : int)
    (hi : int) : ent list =
  prepare st dict toks buf lo hi;
  decode m st

(* Стоит ли вообще запускать модель на этом отрезке.

   Персону или место она может увидеть только там, где есть заглавное слово не
   в начале отрезка или словарный признак имени, места или страны. В обычной
   прозе таких предложений меньшинство, а модель — самая дорогая часть
   конвейера, и прогонять её по всему телу значит платить за каждое
   предложение про погоду. Проверка идёт по уже разобранным токенам и стоит
   один проход без обращений в таблицу весов. *)
let worth_running (st : state) : bool =
  let p = st.p in
  let res = ref false in
  let i = ref 0 in
  while (not !res) && !i < p.len do
    if p.flg.(!i) land (1 lor 2 lor 4 lor 8 lor 16) <> 0 then
      res := true
    (* Заглавное слово с окончанием фамилии или отчества — даже первое в
         предложении. Без этого «Гришин прошу подтвердить» отбрасывалось
         целиком: слова нет в словаре, а заглавная в начале предложения сама
         по себе ничего не значит. *)
    else if p.mor.(!i) <> 0 && p.shp.(!i) = 2 then
      res := true
    else if !i > 0 && p.shp.(!i) = 2 then
      res := true;
    incr i
  done;
  !res

let tag_gated (m : t) (st : state) (dict : Dict.t) (toks : Lexer.toks) (buf : string) (lo : int)
    (hi : int) : ent list =
  prepare st dict toks buf lo hi;
  if worth_running st then
    decode m st
  else
    []
