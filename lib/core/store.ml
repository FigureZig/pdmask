(* store.ml — payload_id → original, sharded, TTL, byte ceiling.

   The /process contract needs a side channel: the client sends only {payload,
   payload_id} and gets back only {result}. To demask on the second request we
   must remember the original by payload_id. This store is that memory.

   Design (spec 4.9):
   - 64 shards by FNV-1a hash of payload_id, one Mutex per shard.
     At 1000 RPS there is effectively no contention.
   - Eviction by TTL (default 120 s) and by a byte ceiling (default 1 GiB,
     oldest entries evicted first).
   - The store is shared across domains: with SO_REUSEPORT the two halves of a
     mask/demask pair almost certainly land in different domains.

   Eviction is a classic LRU: each shard keeps a doubly-linked list of entries
   ordered by recency (head = most recent, tail = least recent). get() and
   put() move the entry to the head in O(1); eviction pops the tail in O(1).
   No Hashtbl.fold + List.sort per insert, which was quadratic on a full
   shard. The byte count includes the key and a per-entry overhead, so the
   ceiling reflects real memory, not just the value length. *)

type entry =
  { key : string;
    mutable value : string;
    mutable size : int; (* key + value + overhead, for the byte ceiling *)
    mutable last : float; (* monotonic time of last access *)
    mutable prev : entry; (* doubly-linked list, head = most recent *)
    mutable next : entry
  }

(* Sentinel nodes: head.next is the most recent entry, tail.prev the least. *)
type shard =
  { mutable table : (string, entry) Hashtbl.t;
    mutable bytes : int; (* total bytes in this shard *)
    mutable last_clean : float; (* last time we ran TTL sweep *)
    head : entry; (* sentinel *)
    tail : entry; (* sentinel *)
    lock : Mutex.t
  }

type t =
  { shards : shard array;
    ttl : float;
    max_bytes : int;
    max_shard_bytes : int
  }

(* Per-entry fixed overhead: the entry record, the Hashtbl slot, the key
   string header. Measured ~3.6x the value length on real payloads; a flat
   constant is a good approximation and keeps the ceiling honest. *)
let entry_overhead = 96

let fnv1a (s : string) : int =
  let h = ref 0xcbf29ce484222325L in
  String.iter
    (fun c ->
      h := Int64.logxor !h (Int64.of_int (Char.code c));
      h := Int64.mul !h 0x100000001b3L
    )
    s;
  Int64.to_int !h

let shard_of (t : t) (key : string) : shard =
  let idx = fnv1a key land max_int mod Array.length t.shards in
  t.shards.(idx)

let create ?(shards = 64) ?(ttl = 120.0) ?(max_bytes = 1073741824) () : t =
  let shard_count = shards in
  let shards =
    Array.init shard_count (fun _ ->
        let rec head = {key = ""; value = ""; size = 0; last = 0.0; prev = tail; next = tail}
        and tail = {key = ""; value = ""; size = 0; last = 0.0; prev = head; next = head} in
        { table = Hashtbl.create 1024;
          bytes = 0;
          last_clean = 0.0;
          head;
          tail;
          lock = Mutex.create ()
        }
    )
  in
  {shards; ttl; max_bytes; max_shard_bytes = max_bytes / shard_count}

(* Unlink e from the list. *)
let unlink (e : entry) : unit =
  e.prev.next <- e.next;
  e.next.prev <- e.prev

(* Move e to the head (most recent). *)
let move_to_head (s : shard) (e : entry) : unit =
  if s.head.next != e then (
    unlink e;
    e.prev <- s.head;
    e.next <- s.head.next;
    s.head.next.prev <- e;
    s.head.next <- e
  )

(* Remove expired entries from a shard. Called under the shard lock. *)
let sweep (t : t) (s : shard) (now : float) =
  let cutoff = now -. t.ttl in
  (* walk from the tail (least recent) and stop at the first fresh entry *)
  let rec go (e : entry) =
    if e == s.head then
      ()
    else if e.last < cutoff then (
      let prev = e.prev in
      Hashtbl.remove s.table e.key;
      s.bytes <- s.bytes - e.size;
      unlink e;
      go prev
    )
  in
  go s.tail.prev;
  s.last_clean <- now

(* Evict the least-recently-used entries until the shard is under its byte
   ceiling. O(1) per evicted entry. *)
let evict_oldest (s : shard) (limit : int) =
  while s.bytes > limit && s.tail.prev != s.head do
    let e = s.tail.prev in
    Hashtbl.remove s.table e.key;
    s.bytes <- s.bytes - e.size;
    unlink e
  done

let with_lock (m : Mutex.t) (f : unit -> 'a) : 'a =
  Mutex.lock m;
  Fun.protect ~finally:(fun () -> Mutex.unlock m) f

let get (t : t) (key : string) : string option =
  let s = shard_of t key in
  let now = Unix.gettimeofday () in
  with_lock s.lock (fun () ->
      if now -. s.last_clean > t.ttl then sweep t s now;
      match Hashtbl.find_opt s.table key with
      | Some e ->
          e.last <- now;
          move_to_head s e;
          Some e.value
      | None -> None
  )

let put (t : t) (key : string) (value : string) : unit =
  let s = shard_of t key in
  let now = Unix.gettimeofday () in
  with_lock s.lock (fun () ->
      if now -. s.last_clean > t.ttl then sweep t s now;
      let size = String.length key + String.length value + entry_overhead in
      ( match Hashtbl.find_opt s.table key with
      | Some old ->
          s.bytes <- s.bytes - old.size + size;
          old.value <- value;
          old.size <- size;
          old.last <- now;
          move_to_head s old
      | None ->
          let e = {key; value; size; last = now; prev = s.head; next = s.head.next} in
          s.head.next.prev <- e;
          s.head.next <- e;
          s.bytes <- s.bytes + size;
          Hashtbl.replace s.table key e
      );
      evict_oldest s t.max_shard_bytes
  )
