(* Allocation profile for the old structural and cached-sample string filters.
   This is diagnostic evidence only: it checks result contents, allocation, and
   retained graph size on the selected compiler, not a formal cost theorem. *)

module S = StringPatriciaInternal
module Public = StringPatriciaMap

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

let profile_size = positive_env "PATRICIA_MAP_FILTER_PROFILE_SIZE" 10_000

type measurement = { allocated_words : float; retained_words : int }

let allocated_words () =
  let stats = Gc.quick_stat () in
  stats.Gc.minor_words +. stats.Gc.major_words

let measure operation =
  Gc.full_major ();
  Gc.compact ();
  let before_live = (Gc.stat ()).Gc.live_words in
  let before_allocated = allocated_words () in
  let result = operation () in
  let allocated_words = allocated_words () -. before_allocated in
  ignore (Sys.opaque_identity result);
  Gc.full_major ();
  Gc.compact ();
  result, { allocated_words;
            retained_words = (Gc.stat ()).Gc.live_words - before_live }

let key index = Printf.sprintf "%08x" index
let keys = Array.init profile_size key

let input =
  Array.fold_left (fun tree name -> S.set name (int_of_string ("0x" ^ name)) tree)
    S.empty keys

let public_input =
  Array.fold_left
    (fun tree name -> Public.set name (int_of_string ("0x" ^ name)) tree)
    Public.empty keys

let expected label keep =
  Array.fold_left
    (fun count name -> if keep (int_of_string ("0x" ^ name)) then count + 1 else count)
    0 keys

let check label keep tree =
  if List.length (S.elements tree) <> expected label keep then
    failwith (label ^ ": wrong cardinality");
  Array.iter
    (fun name ->
       let value = int_of_string ("0x" ^ name) in
       if S.get name tree <> (if keep value then Some value else None) then
         failwith (label ^ ": lookup mismatch"))
    keys

let check_public label keep tree =
  if List.length (Public.elements tree) <> expected label keep then
    failwith (label ^ ": wrong public cardinality");
  Array.iter
    (fun name ->
       let value = int_of_string ("0x" ^ name) in
       if Public.get name tree <> (if keep value then Some value else None) then
         failwith (label ^ ": public lookup mismatch"))
    keys

let profile workload worker keep =
  let result, measurement = measure (fun () -> worker keep input) in
  check workload keep result;
  measurement

let legacy keep tree = S.map_filter (fun _ value -> if keep value then Some value else None) tree
let cached keep tree = S.map_filter_cached (fun _ value -> if keep value then Some value else None) tree
let public keep tree = Public.map_filter (fun _ value -> if keep value then Some value else None) tree

let profile_public workload keep =
  let result, measurement = measure (fun () -> public keep public_input) in
  check_public workload keep result;
  measurement

let print_row workload worker measurement =
  Printf.printf "  %-10s %-10s %12.0f %12d\n"
    workload worker measurement.allocated_words measurement.retained_words

let () =
  let workloads = [
    "keep-all", (fun _ -> true);
    "keep-even", (fun value -> value land 1 = 0);
    "drop-all", (fun _ -> false);
  ] in
  Printf.printf "String map_filter profile (%d bindings)\n" profile_size;
  Printf.printf "  %-10s %-10s %12s %12s\n"
    "workload" "worker" "allocated" "retained";
  Printf.printf "  %-10s %-10s %12s %12s\n" "" "" "words" "words";
  List.iter
    (fun (label, keep) ->
       print_row label "legacy" (profile label legacy keep);
       print_row label "cached" (profile label cached keep);
       print_row label "public" (profile_public label keep))
    workloads
