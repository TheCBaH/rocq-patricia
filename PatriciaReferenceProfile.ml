(* Native measurement profile for the proof-aligned extraction.

   This executable deliberately links only [reference_extracted/].  Its
   generated module names overlap with the optimized extraction's support
   modules, so trying to compare both implementations in one executable would
   turn this small measurement tool into build-system machinery.  Every result
   is instead checked against Stdlib.Map; compare its output with a regular
   [make benchmark] run using the same compiler configuration. *)

module Int_avl = Map.Make (struct
  type t = int
  let compare = Int.compare
end)

module String_avl = Map.Make (struct
  type t = string
  let compare = Stdlib.String.compare
end)

module Integer = PatriciaReference.Patricia
module Strings = PatriciaReference.StringPatricia

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

(* The direct logical-string extraction is intentionally much slower than the
   optimized packed-byte backend.  A modest default makes the profile usable
   in an interactive development loop; larger series are opt-in. *)
let profile_size = positive_env "PATRICIA_REFERENCE_PROFILE_SIZE" 1_000
let lookup_repetitions = 3

type measurement = {
  seconds : float;
  allocated_words : float;
}

let allocated_words () =
  let stats = Gc.quick_stat () in
  stats.Gc.minor_words +. stats.Gc.major_words

let measure operation =
  Gc.full_major ();
  let before_allocated = allocated_words () in
  let started = Unix.gettimeofday () in
  let result = operation () in
  let seconds = Unix.gettimeofday () -. started in
  let allocated_words = allocated_words () -. before_allocated in
  result, { seconds; allocated_words }

let print_measurement name measurement =
  Printf.printf "  %-18s %9.3f ms  allocated %12.0f words\n"
    name (1_000. *. measurement.seconds) measurement.allocated_words

let int_keys start = Array.init profile_size (fun index -> start + index + 1)

let string_key index = Printf.sprintf "%08x" index

let string_keys start =
  Array.init profile_size (fun index -> string_key (start + index))

let build_int keys =
  Array.fold_left (fun tree key -> Integer.set key key tree) Integer.empty keys

let build_string keys =
  Array.fold_left
    (fun tree key -> Strings.set key (Stdlib.String.length key) tree)
    Strings.empty keys

let int_cardinal tree = Integer.fold (fun count _ _ -> count + 1) tree 0
let string_cardinal tree = Strings.fold (fun count _ _ -> count + 1) tree 0

let check_int context keys expected tree =
  if int_cardinal tree <> Int_avl.cardinal expected then
    failwith (context ^ ": cardinality mismatch");
  Array.iter
    (fun key ->
       if Integer.get key tree <> Int_avl.find_opt key expected then
         failwith (context ^ ": lookup mismatch"))
    keys

let check_string context keys expected tree =
  if string_cardinal tree <> String_avl.cardinal expected then
    failwith (context ^ ": cardinality mismatch");
  Array.iter
    (fun key ->
       if Strings.get key tree <> String_avl.find_opt key expected then
         failwith (context ^ ": lookup mismatch"))
    keys

let profile_int () =
  let left_keys = int_keys 0 in
  let disjoint_keys = int_keys profile_size in
  let overlap_keys = int_keys (profile_size / 2) in
  let avl_left = Array.fold_left (fun map key -> Int_avl.add key key map)
      Int_avl.empty left_keys in
  let left, build = measure (fun () -> build_int left_keys) in
  check_int "integer build" left_keys avl_left left;
  print_measurement "integer build" build;
  let lookup_total, lookup = measure (fun () ->
      let total = ref 0 in
      for _ = 1 to lookup_repetitions do
        Array.iter
          (fun key ->
             match Integer.get key left with Some value -> total := !total + value | None -> ())
          left_keys
      done;
      !total) in
  ignore (Sys.opaque_identity lookup_total);
  print_measurement "integer lookup (3 passes)" lookup;
  let updated, update = measure (fun () ->
      Array.fold_left (fun tree key -> Integer.set key (-key) tree) left left_keys) in
  let avl_updated = Array.fold_left (fun map key -> Int_avl.add key (-key) map)
      avl_left left_keys in
  check_int "integer update" left_keys avl_updated updated;
  print_measurement "integer update" update;
  let disjoint = build_int disjoint_keys in
  let merged, disjoint_union = measure (fun () -> Integer.union_left left disjoint) in
  let all_disjoint = Array.append left_keys disjoint_keys in
  let avl_disjoint = Array.fold_left (fun map key -> Int_avl.add key key map)
      avl_left disjoint_keys in
  check_int "integer disjoint union" all_disjoint avl_disjoint merged;
  print_measurement "integer disjoint union" disjoint_union;
  let overlap = build_int overlap_keys in
  let merged, overlap_union = measure (fun () -> Integer.union_left left overlap) in
  let all_overlap = Array.append left_keys overlap_keys in
  let avl_overlap = Array.fold_left (fun map key -> Int_avl.add key key map)
      avl_left overlap_keys in
  check_int "integer overlap union" all_overlap avl_overlap merged;
  print_measurement "integer overlap union" overlap_union

let profile_strings () =
  let left_keys = string_keys 0 in
  let disjoint_keys = string_keys profile_size in
  let overlap_keys = string_keys (profile_size / 2) in
  let add_avl map key = String_avl.add key (Stdlib.String.length key) map in
  let avl_left = Array.fold_left add_avl String_avl.empty left_keys in
  let left, build = measure (fun () -> build_string left_keys) in
  check_string "string build" left_keys avl_left left;
  print_measurement "string build" build;
  let lookup_total, lookup = measure (fun () ->
      let total = ref 0 in
      for _ = 1 to lookup_repetitions do
        Array.iter
          (fun key ->
             match Strings.get key left with Some value -> total := !total + value | None -> ())
          left_keys
      done;
      !total) in
  ignore (Sys.opaque_identity lookup_total);
  print_measurement "string lookup (3 passes)" lookup;
  let updated, update = measure (fun () ->
      Array.fold_left
        (fun tree key -> Strings.set key (-(Stdlib.String.length key)) tree)
        left left_keys) in
  let avl_updated = Array.fold_left
      (fun map key -> String_avl.add key (-(Stdlib.String.length key)) map)
      avl_left left_keys in
  check_string "string update" left_keys avl_updated updated;
  print_measurement "string update" update;
  let disjoint = build_string disjoint_keys in
  let merged, disjoint_union = measure (fun () -> Strings.union_left left disjoint) in
  let all_disjoint = Array.append left_keys disjoint_keys in
  let avl_disjoint = Array.fold_left add_avl avl_left disjoint_keys in
  check_string "string disjoint union" all_disjoint avl_disjoint merged;
  print_measurement "string disjoint union" disjoint_union;
  let overlap = build_string overlap_keys in
  let merged, overlap_union = measure (fun () -> Strings.union_left left overlap) in
  let all_overlap = Array.append left_keys overlap_keys in
  let avl_overlap = Array.fold_left add_avl avl_left overlap_keys in
  check_string "string overlap union" all_overlap avl_overlap merged;
  print_measurement "string overlap union" overlap_union

let () =
  Printf.printf "Proof-aligned Patricia native profile (%d bindings per input)\n"
    profile_size;
  profile_int ();
  profile_strings ();
  print_endline "Proof-aligned Patricia native profile: ok"
