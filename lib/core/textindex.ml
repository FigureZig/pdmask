(* textindex.ml — индексы для сверки адреса со справочником отделений.

   Задача: для ключа адреса из текста ответить, совпал ли он с каким-нибудь
   отделением банка. Совпадением считается вложение в любую сторону — спан
   редко ложится на справочную запись ровно: правило адреса цепляется за город,
   а справочник начинается с "г.".

   Наивно это K образцов на обе стороны, то есть O(K · |спан| · |офис|) на
   каждого кандидата. Справочник неизменен после загрузки — значит его надо
   проиндексировать один раз. Две стороны вложения — две разные задачи:

   - "офис внутри спана" — множественный поиск образцов в тексте.
     Ахо–Корасик: бор из всех ключей плюс суффиксные ссылки, один проход по
     спану за O(|спан|) независимо от числа отделений.

   - "спан внутри офиса" — принадлежность подстроке множества строк.
     Суффиксный автомат над сцепкой всех ключей через разделитель. Разделитель
     не встречается в ключах (они состоят только из букв и цифр), поэтому
     совпадение не может склеиться из двух соседних отделений.

   Про представление переходов. Первая версия держала их в (char, int)
   Hashtbl на состояние — и профиль показал, что 12% всей стадии доказательств
   уходит в caml_hash, compare_val и Hashtbl.find. Полиморфный хеш ради
   отображения байта в число: асимптотика правильная, а constant factor хуже,
   чем у наивного посимвольного сравнения, которое эти структуры заменяли.

   Поэтому переходы лежат плоско:

   - Алфавит сжат. Из 256 байтов в справочнике встречается несколько десятков
     (кириллица в UTF-8, цифры, латиница); байты сопоставлены плотным
     индексам, всё остальное — один общий символ "прочее". Таблица получается
     состояния × |алфавит| вместо состояния × 256.

   - Fail-ссылки Ахо–Корасика развёрнуты в таблицу при сборке, а не проходятся
     при запросе. Терминальность протянута по ним туда же.

   - У суффиксного автомата заведено поглощающее мёртвое состояние, куда ведут
     все отсутствующие переходы.

   В итоге тело обоих циклов — две индексации массива и ни одной ветки:
   предсказателю нечего предсказывать, а аллокаций нет вовсе. *)

let sep = '\000'

(* --- сжатый алфавит --- *)

(* Байты, которых нет в справочнике, склеены в один символ: переход по любому
   из них устроен одинаково (в корень у бора, в мёртвое состояние у автомата),
   и различать их незачем. *)
let alphabet_of (s : string) : int array * int =
  let map = Array.make 256 (-1) in
  let a = ref 0 in
  String.iter
    (fun c ->
      let b = Char.code c in
      if map.(b) < 0 then (
        map.(b) <- !a;
        incr a
      )
    )
    s;
  let other = !a in
  for b = 0 to 255 do
    if map.(b) < 0 then map.(b) <- other
  done;
  (map, other + 1)

(* --- Ахо–Корасик: есть ли хоть один образец внутри текста --- *)

type ac =
  { ac_alpha : int array; (* байт -> символ алфавита *)
    ac_w : int; (* ширина строки таблицы *)
    ac_goto : int array; (* состояние * w + символ -> состояние *)
    ac_term : int array (* 1, если в состоянии заканчивается образец *)
  }

let ac_build (alpha : int array) (w : int) (patterns : string list) : ac =
  (* верхняя граница числа узлов: корень плюс по узлу на символ *)
  let cap = 1 + List.fold_left (fun a p -> a + String.length p) 0 patterns in
  let goto = Array.make (cap * w) (-1) in
  let term = Array.make cap 0 in
  let n = ref 1 in
  List.iter
    (fun p ->
      let cur = ref 0 in
      String.iter
        (fun c ->
          let s = alpha.(Char.code c) in
          let e = (!cur * w) + s in
          if goto.(e) < 0 then (
            goto.(e) <- !n;
            incr n
          );
          cur := goto.(e)
        )
        p;
      if String.length p > 0 then term.(!cur) <- 1
    )
    patterns;
  (* Обход в ширину: суффиксная ссылка ведёт в самый длинный собственный
     суффикс, который тоже есть в боре. Недостающие переходы тут же
     замещаются переходами по ссылке — после сборки таблица полная, и
     запросу спускаться уже некуда. *)
  let fail = Array.make cap 0 in
  let queue = Queue.create () in
  for s = 0 to w - 1 do
    let v = goto.(s) in
    if v < 0 then
      goto.(s) <- 0
    else (
      fail.(v) <- 0;
      Queue.add v queue
    )
  done;
  while not (Queue.is_empty queue) do
    let u = Queue.pop queue in
    (* терминальность протягивается по ссылке: если суффикс — образец, то и
       здесь есть совпадение *)
    term.(u) <- term.(u) lor term.(fail.(u));
    let base = u * w
    and fbase = fail.(u) * w in
    for s = 0 to w - 1 do
      let v = goto.(base + s) in
      if v < 0 then
        goto.(base + s) <- goto.(fbase + s)
      else (
        fail.(v) <- goto.(fbase + s);
        Queue.add v queue
      )
    done
  done;
  {ac_alpha = alpha; ac_w = w; ac_goto = goto; ac_term = term}

(* Встречается ли хоть один образец внутри text? Совпадения копятся через lor:
   ранний выход стоил бы ветки на каждом байте, а ключи короткие. *)
let ac_matches (a : ac) (text : string) : bool =
  let cur = ref 0
  and hit = ref 0 in
  let w = a.ac_w in
  for i = 0 to String.length text - 1 do
    let s = Array.unsafe_get a.ac_alpha (Char.code (String.unsafe_get text i)) in
    cur := Array.unsafe_get a.ac_goto ((!cur * w) + s);
    hit := !hit lor Array.unsafe_get a.ac_term !cur
  done;
  !hit <> 0

(* --- суффиксный автомат: является ли строка подстрокой сцепки --- *)

(* Строится на хеш-таблицах: сборка идёт один раз при загрузке, и её constant
   factor никого не волнует. В запрос уходит плоская таблица. *)
type sam_build =
  { sb_len : int array;
    sb_link : int array;
    sb_next : (char, int) Hashtbl.t array;
    mutable sb_size : int;
    mutable sb_last : int
  }

type sam =
  { sa_alpha : int array;
    sa_w : int;
    sa_go : int array;
    sa_dead : int
  }

let sb_create (cap : int) : sam_build =
  { sb_len = Array.make cap 0;
    sb_link = Array.make cap (-1);
    sb_next = Array.init cap (fun _ -> Hashtbl.create 4);
    sb_size = 1;
    sb_last = 0
  }

let sb_extend (m : sam_build) (c : char) : unit =
  let cur = m.sb_size in
  m.sb_size <- m.sb_size + 1;
  m.sb_len.(cur) <- m.sb_len.(m.sb_last) + 1;
  m.sb_link.(cur) <- -1;
  Hashtbl.reset m.sb_next.(cur);
  let p = ref m.sb_last in
  while !p <> -1 && not (Hashtbl.mem m.sb_next.(!p) c) do
    Hashtbl.replace m.sb_next.(!p) c cur;
    p := m.sb_link.(!p)
  done;
  ( if !p = -1 then
      m.sb_link.(cur) <- 0
    else
      let q = Hashtbl.find m.sb_next.(!p) c in
      if m.sb_len.(!p) + 1 = m.sb_len.(q) then
        m.sb_link.(cur) <- q
      else
        (* клон: состояние q отвечает за слишком длинные строки, нужен его
         укороченный двойник *)
        let clone = m.sb_size in
        m.sb_size <- m.sb_size + 1;
        m.sb_len.(clone) <- m.sb_len.(!p) + 1;
        m.sb_link.(clone) <- m.sb_link.(q);
        Hashtbl.reset m.sb_next.(clone);
        Hashtbl.iter (fun k v -> Hashtbl.replace m.sb_next.(clone) k v) m.sb_next.(q);
        while !p <> -1 && Hashtbl.find_opt m.sb_next.(!p) c = Some q do
          Hashtbl.replace m.sb_next.(!p) c clone;
          p := m.sb_link.(!p)
        done;
        m.sb_link.(q) <- clone;
        m.sb_link.(cur) <- clone
  );
  m.sb_last <- cur

let sa_build (alpha : int array) (w : int) (s : string) : sam =
  (* состояний не больше 2n *)
  let m = sb_create ((2 * String.length s) + 8) in
  String.iter (fun c -> sb_extend m c) s;
  (* Мёртвое состояние поглощает всё: любой отсутствующий переход ведёт туда,
     и оттуда уже не выбраться. Это убирает проверку "переход есть?" из тела
     цикла запроса. *)
  let dead = m.sb_size in
  let go = Array.make ((dead + 1) * w) dead in
  for u = 0 to dead - 1 do
    Hashtbl.iter (fun c v -> go.((u * w) + alpha.(Char.code c)) <- v) m.sb_next.(u)
  done;
  {sa_alpha = alpha; sa_w = w; sa_go = go; sa_dead = dead}

(* Является ли p подстрокой строки, по которой построен автомат? *)
let sa_contains (m : sam) (p : string) : bool =
  let cur = ref 0 in
  let w = m.sa_w in
  for i = 0 to String.length p - 1 do
    let s = Array.unsafe_get m.sa_alpha (Char.code (String.unsafe_get p i)) in
    cur := Array.unsafe_get m.sa_go ((!cur * w) + s)
  done;
  !cur <> m.sa_dead

(* --- индекс справочника --- *)

type t =
  { ac : ac;
    sam : sam;
    empty : bool;
    min_len : int; (* длина самого короткого ключа справочника *)
    max_len : int (* длина самого длинного *)
  }

let of_keys (keys : string list) : t =
  let keys = List.filter (fun k -> k <> "") keys in
  let joined = String.concat (String.make 1 sep) keys in
  let alpha, w = alphabet_of joined in
  let lens = List.map String.length keys in
  { ac = ac_build alpha w keys;
    sam = sa_build alpha w joined;
    empty = keys = [];
    min_len = List.fold_left min max_int (max_int :: lens);
    max_len = List.fold_left max 0 lens
  }

(* Совпал ли ключ спана со справочником — в любую сторону вложения.

   Отсечки по длине снимают часть работы даром: спан короче самого короткого
   ключа не может содержать ни одного отделения, а спан длиннее самого
   длинного не может быть ничьей подстрокой. *)
(* Короче этого совпадение по вложению бессмысленно: ключ «2» является
   подстрокой почти любого адреса отделения, и спан из одной цифры получал
   E_ORGADDR — а это жёсткий запрет маскирования. Так глушился каждый короткий
   фрагмент адреса: номер дома, номер корпуса. *)
let min_query = 12

let matches (t : t) (key : string) : bool =
  let n = String.length key in
  (not t.empty)
  && n >= min_query
  && ((n <= t.max_len && sa_contains t.sam key) || (n >= t.min_len && ac_matches t.ac key))
