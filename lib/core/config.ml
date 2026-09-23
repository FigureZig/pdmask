(* config.ml — configuration.

   Reads config/systems.yaml: per-system profiles (which PII types to mask,
   whether demasking is allowed, the mask mode), evidence weights, and the
   HTTP limits. The default profile is used for /process, which the checking
   system calls without headers. A profile is selected by the
   X-PDMask-System header on the other routes.

   The config is immutable and swapped atomically on POST /admin/reload, so
   requests in flight finish on the old config. *)

type limits =
  { max_body_bytes : int; (* above this -> 413 *)
    large_body_threshold : int; (* above this counts as "large" *)
    max_inflight_large : int; (* concurrent large bodies allowed *)
    store_ttl_seconds : float;
    store_max_bytes : int;
    keepalive_idle_seconds : int
  }

type mask_mode =
  | Stars
  | Token
  | Synthetic

type profile =
  { enabled : bool;
    mask_mode : mask_mode;
    demask : bool;
    pii_types : Spans.ty list option; (* None = all *)
    threshold : int;
    irreversible : Spans.ty list (* masked but never stored/restored (PCI DSS 3.3.1) *)
  }

type t =
  { limits : limits;
    systems : (string * profile) list;
    default_profile : profile
  }

let default_limits : limits =
  { max_body_bytes = 67108864;
    large_body_threshold = 65536;
    max_inflight_large = 16;
    store_ttl_seconds = 900.0;
    store_max_bytes = 1073741824;
    keepalive_idle_seconds = 75
  }

let default_profile : profile =
  { enabled = true;
    mask_mode = Stars;
    demask = true;
    pii_types = None;
    threshold = 50;
    irreversible = []
  }

let default_config : t =
  {limits = default_limits; systems = [("default", default_profile)]; default_profile}

(* --- minimal YAML parsing --- *)

let yaml_lines (yaml : string) : string list = String.split_on_char '\n' yaml

(* Find the value of a top-level "key: value" line. *)
let yaml_scalar (lines : string list) (key : string) : string option =
  let prefix = key ^ ":" in
  let rec find = function
    | [] -> None
    | line :: rest ->
        let line = String.trim line in
        if
          String.length line > String.length prefix
          && String.sub line 0 (String.length prefix) = prefix
        then
          Some
            (String.trim
               (String.sub line (String.length prefix) (String.length line - String.length prefix))
            )
        else
          find rest
  in
  find lines

let yaml_int (lines : string list) (key : string) : int option =
  Option.bind (yaml_scalar lines key) int_of_string_opt

let yaml_bool (lines : string list) (key : string) : bool option =
  Option.bind (yaml_scalar lines key) (function
    | "true" | "yes" | "on" -> Some true
    | "false" | "no" | "off" -> Some false
    | _ -> None
    )

(* Parse a mask mode string. *)
let mask_mode_of_string (s : string) : mask_mode option =
  match String.lowercase_ascii s with
  | "stars" -> Some Stars
  | "token" -> Some Token
  | "synthetic" -> Some Synthetic
  | _ -> None

(* Parse a PII type name into Spans.ty. *)
let ty_of_name (s : string) : Spans.ty option =
  match String.lowercase_ascii s with
  | "fio" -> Some Spans.Fio
  | "birth_date" -> Some Spans.Birth_date
  | "birth_place" -> Some Spans.Birth_place
  | "passport" -> Some Spans.Passport
  | "citizenship" -> Some Spans.Citizenship
  | "issuer" -> Some Spans.Issuer
  | "dept_code" -> Some Spans.Dept_code
  | "issue_date" -> Some Spans.Issue_date
  | "driver_license" -> Some Spans.Driver_license
  | "address" -> Some Spans.Address
  | "email" -> Some Spans.Email
  | "phone" -> Some Spans.Phone
  | "inn" -> Some Spans.Inn
  | "card" -> Some Spans.Card
  | "cvv" -> Some Spans.Cvv
  | "pin" -> Some Spans.Pin
  | "card_holder" -> Some Spans.Card_holder
  | "snils" -> Some Spans.Snils
  | "oms" -> Some Spans.Oms
  | "foreign_passport" -> Some Spans.Foreign_passport
  | _ -> None

(* Parse a profile from the lines of a "systems: <name>:" block. The block
   runs until the next top-level key (no indentation). *)
let parse_profile (lines : string list) : profile =
  let base = default_profile in
  (* Parse a "key: [a, b, c]" list of PII types. *)
  let type_list (key : string) : Spans.ty list option =
    match yaml_scalar lines key with
    | Some "all" -> None
    | Some list_str ->
        let list_str =
          String.map
            (fun c ->
              if c = '[' || c = ']' then
                ' '
              else
                c
            )
            list_str
        in
        let types =
          String.split_on_char ',' list_str |> List.map String.trim |> List.filter_map ty_of_name
        in
        if types = [] then
          None
        else
          Some types
    | None -> None
  in
  let pii_types =
    match type_list "pii_types" with
    | Some _ as t -> t
    | None -> base.pii_types
  in
  let irreversible = Option.value (type_list "irreversible") ~default:base.irreversible in
  { enabled = Option.value (yaml_bool lines "enabled") ~default:base.enabled;
    mask_mode =
      Option.value
        (Option.bind (yaml_scalar lines "mask_mode") mask_mode_of_string)
        ~default:base.mask_mode;
    demask = Option.value (yaml_bool lines "demask") ~default:base.demask;
    pii_types;
    threshold = Option.value (yaml_int lines "threshold") ~default:base.threshold;
    irreversible
  }

(* Split the YAML into per-system blocks. A block starts at a line
   "  <name>:" under "systems:" and runs until the next line at the same
   indent that is not a continuation. *)
let system_blocks (lines : string list) : (string * string list) list =
  let rec find_systems = function
    | [] -> []
    | line :: rest when line = "systems:" -> rest
    | _ :: rest -> find_systems rest
  in
  let is_profile_line (line : string) : bool =
    String.length line > 2
    && line.[0] = ' '
    && line.[1] = ' '
    && line.[2] <> ' '
    && not (String.length line > 3 && line.[2] = '<' && line.[3] = '<')
  in
  (* Верхнеуровневый ключ вроде "limits:" закрывает секцию systems. Без этого
     шесть ключей блока limits разбираются как шесть систем, и заголовок
     X-PDMask-System: max_body_bytes проходит как валидная система — то есть
     ограниченного списка систем фактически нет. *)
  let is_top_level (line : string) : bool =
    String.length line > 0 && line.[0] <> ' ' && line.[0] <> '#' && String.trim line <> ""
  in
  let rec go acc = function
    | [] -> List.rev acc
    | line :: _ when is_top_level line -> List.rev acc
    | line :: rest when is_profile_line line ->
        let name = String.trim line |> String.split_on_char ':' |> List.hd |> String.trim in
        let rec collect block = function
          | [] -> (List.rev block, [])
          | l :: rest' when is_profile_line l || is_top_level l -> (List.rev block, l :: rest')
          | l :: rest' -> collect (l :: block) rest'
        in
        let block, rest' = collect [] rest in
        go ((name, block) :: acc) rest'
    | _ :: rest -> go acc rest
  in
  go [] (find_systems lines)

let load (path : string) : t =
  match In_channel.with_open_bin path (fun ic -> In_channel.input_all ic) with
  | exception _ -> default_config
  | yaml ->
      let lines = yaml_lines yaml in
      let l = default_limits in
      let get key default = Option.value (yaml_int lines key) ~default in
      let limits =
        { max_body_bytes = get "max_body_bytes" l.max_body_bytes;
          large_body_threshold = get "large_body_threshold" l.large_body_threshold;
          max_inflight_large = get "max_inflight_large" l.max_inflight_large;
          store_ttl_seconds =
            float_of_int (get "store_ttl_seconds" (int_of_float l.store_ttl_seconds));
          store_max_bytes = get "store_max_bytes" l.store_max_bytes;
          keepalive_idle_seconds = get "keepalive_idle_seconds" l.keepalive_idle_seconds
        }
      in
      let systems =
        system_blocks lines |> List.map (fun (name, block) -> (name, parse_profile block))
      in
      let default_profile =
        match List.assoc_opt "default" systems with
        | Some p -> p
        | None -> default_profile
      in
      {limits; systems; default_profile}

(* Look up the profile for a system name; fall back to default. *)
let profile_of (t : t) (system : string) : profile =
  match List.assoc_opt system t.systems with
  | Some p -> p
  | None -> t.default_profile
