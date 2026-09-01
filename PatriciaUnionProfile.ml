(* Allocation profile for the native-shaped and changed-result union workers.

   The normal benchmark deliberately uses only the abstract supported maps.
   This diagnostic instead imports the extracted companion modules so that it
   can compare the legacy handwritten realization, the structural and
   closure-free native-shaped candidates, and the established workers. Each
   result is checked pointwise against its known left-biased bindings before it
   is reported. *)

module I = PatriciaInternal
module IU = PatriciaUnion
module S = StringPatriciaInternal
module SU = StringPatriciaUnion

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

let profile_size = positive_env "PATRICIA_UNION_PROFILE_SIZE" 10_000

type measurement = {
  allocated_words : float;
  retained_words : int;
}

(* [==] is deliberately used only by this diagnostic.  The table records how
   much of each immutable input tree the result still reaches by physical
   identity; it is not part of either public map contract. *)
module Physical_nodes = Hashtbl.Make (struct
  type t = Obj.t

  let equal left right = left == right
  let hash value = Hashtbl.hash value
end)

type sharing = {
  result_nodes : int;
  left_shared_nodes : int;
  right_shared_nodes : int;
}

let add_int_nodes table tree =
  let rec visit = function
    | I.Empty -> ()
    | (I.Leaf _ as node) -> Physical_nodes.replace table (Obj.repr node) ()
    | (I.Branch (_, _, left, right) as node) ->
        Physical_nodes.replace table (Obj.repr node) ();
        visit left;
        visit right
  in
  visit tree

let add_string_nodes table tree =
  let rec visit = function
    | S.Empty -> ()
    | (S.Leaf _ as node) -> Physical_nodes.replace table (Obj.repr node) ()
    | (S.Branch (_, _, left, right) as node) ->
        Physical_nodes.replace table (Obj.repr node) ();
        visit left;
        visit right
  in
  visit tree

let count_int_sharing left right result =
  let left_nodes = Physical_nodes.create 128 in
  let right_nodes = Physical_nodes.create 128 in
  add_int_nodes left_nodes left;
  add_int_nodes right_nodes right;
  let rec visit counts = function
    | I.Empty -> counts
    | (I.Leaf _ as node) ->
        let pointer = Obj.repr node in
        { result_nodes = counts.result_nodes + 1;
          left_shared_nodes = counts.left_shared_nodes +
            if Physical_nodes.mem left_nodes pointer then 1 else 0;
          right_shared_nodes = counts.right_shared_nodes +
            if Physical_nodes.mem right_nodes pointer then 1 else 0 }
    | (I.Branch (_, _, left, right) as node) ->
        let pointer = Obj.repr node in
        let counts =
          { result_nodes = counts.result_nodes + 1;
            left_shared_nodes = counts.left_shared_nodes +
              if Physical_nodes.mem left_nodes pointer then 1 else 0;
            right_shared_nodes = counts.right_shared_nodes +
              if Physical_nodes.mem right_nodes pointer then 1 else 0 }
        in
        visit (visit counts left) right
  in
  visit { result_nodes = 0; left_shared_nodes = 0; right_shared_nodes = 0 } result

let count_string_sharing left right result =
  let left_nodes = Physical_nodes.create 128 in
  let right_nodes = Physical_nodes.create 128 in
  add_string_nodes left_nodes left;
  add_string_nodes right_nodes right;
  let rec visit counts = function
    | S.Empty -> counts
    | (S.Leaf _ as node) ->
        let pointer = Obj.repr node in
        { result_nodes = counts.result_nodes + 1;
          left_shared_nodes = counts.left_shared_nodes +
            if Physical_nodes.mem left_nodes pointer then 1 else 0;
          right_shared_nodes = counts.right_shared_nodes +
            if Physical_nodes.mem right_nodes pointer then 1 else 0 }
    | (S.Branch (_, _, left, right) as node) ->
        let pointer = Obj.repr node in
        let counts =
          { result_nodes = counts.result_nodes + 1;
            left_shared_nodes = counts.left_shared_nodes +
              if Physical_nodes.mem left_nodes pointer then 1 else 0;
            right_shared_nodes = counts.right_shared_nodes +
              if Physical_nodes.mem right_nodes pointer then 1 else 0 }
        in
        visit (visit counts left) right
  in
  visit { result_nodes = 0; left_shared_nodes = 0; right_shared_nodes = 0 } result

let allocated_words () =
  let stats = Gc.quick_stat () in
  stats.Gc.minor_words +. stats.Gc.major_words

(* Keep the result live across the compacting collection.  The retained figure
   therefore describes the result graph in addition to the already-live input
   graphs, while allocation includes short-lived worker frames and closures. *)
let measure keep_left keep_right operation =
  Gc.full_major ();
  Gc.compact ();
  let before_live = (Gc.stat ()).Gc.live_words in
  let before_allocated = allocated_words () in
  let result = operation () in
  let allocated_words = allocated_words () -. before_allocated in
  (* The compiler can otherwise prove that an input is dead after [operation]
     and let this collection reclaim it.  Keep both inputs rooted so retained
     memory is the extra result graph, not a result-minus-input delta. *)
  let keep_left = Sys.opaque_identity keep_left in
  let keep_right = Sys.opaque_identity keep_right in
  Gc.full_major ();
  Gc.compact ();
  ignore (Sys.opaque_identity keep_left);
  ignore (Sys.opaque_identity keep_right);
  let retained_words = (Gc.stat ()).Gc.live_words - before_live in
  result, { allocated_words; retained_words }

let int_key index = index + 1

let build_int keys =
  Array.fold_left (fun tree key -> I.set key key tree) I.empty keys

let build_string keys =
  Array.fold_left
    (fun tree key -> S.set key (Stdlib.String.length key) tree)
    S.empty keys

let string_key ?(prefix = "") index =
  prefix ^ Printf.sprintf "%08x" index

let check_int keys expected_cardinal actual =
  Array.iter
    (fun key ->
       if I.get key actual <> Some key then
         failwith "integer union-profile result mismatch")
    keys;
  if List.length (I.elements actual) <> expected_cardinal then
    failwith "integer union-profile cardinality mismatch"

let check_string keys expected_cardinal actual =
  Array.iter
    (fun key ->
       if S.get key actual <> Some (Stdlib.String.length key) then
         failwith "string union-profile result mismatch")
    keys;
  if List.length (S.elements actual) <> expected_cardinal then
    failwith "string union-profile cardinality mismatch"

let print_header title =
  Printf.printf "\n%s (%d bindings in the left input)\n" title profile_size;
  Printf.printf
    "  %-18s %-10s %12s %12s %10s %10s %10s\n"
    "workload" "worker" "allocated" "retained" "nodes" "from left" "from right";
  Printf.printf
    "  %-18s %-10s %12s %12s %10s %10s %10s\n"
    "" "" "words" "words" "left == out" "nodes" "nodes"

let print_row name worker left result measurement sharing =
  Printf.printf "  %-18s %-10s %12.0f %12d %10b %10d %10d\n"
    name worker measurement.allocated_words measurement.retained_words
    (left == result) sharing.left_shared_nodes sharing.right_shared_nodes

let profile_int_case name keys expected_cardinal left right =
  let run worker operation =
    let result, worker_measurement = measure left right operation in
    check_int keys expected_cardinal result;
    let sharing = count_int_sharing left right result in
    if sharing.result_nodes <> I.size result then
      failwith "integer union-profile sharing count mismatch";
    print_row name worker left result worker_measurement sharing
  in
  run "legacy" (fun () -> I.union_left left right);
  run "generated" (fun () -> IU.union_left_native_default left right);
  run "native fuel" (fun () -> IU.union_left_native_fuel_default left right);
  run "inline fuel" (fun () -> IU.union_left_native_fuel_inline_default left right);
  run "proved" (fun () -> IU.union_left_specialized_changed_result left right);
  run "fuel" (fun () ->
      IU.union_left_specialized_changed_fuel_result left right)

let profile_string_case name keys expected_cardinal left right =
  let run worker operation =
    let result, worker_measurement = measure left right operation in
    check_string keys expected_cardinal result;
    let sharing = count_string_sharing left right result in
    if sharing.result_nodes <> S.size result then
      failwith "string union-profile sharing count mismatch";
    print_row name worker left result worker_measurement sharing
  in
  run "legacy" (fun () -> S.union_left left right);
  run "generated" (fun () -> SU.union_left_native_default left right);
  run "native fuel" (fun () -> SU.union_left_native_fuel_default left right);
  run "proved" (fun () -> SU.union_left_specialized_changed_result left right);
  run "fuel" (fun () ->
      SU.union_left_specialized_changed_fuel_result left right)

let profile_int () =
  let left_keys = Array.init profile_size int_key in
  let disjoint_keys = Array.init profile_size (fun index -> int_key (profile_size + index)) in
  let overlap_keys =
    Array.init profile_size (fun index -> int_key ((profile_size / 2) + index))
  in
  let subset_keys = Array.sub left_keys 0 (max 1 (profile_size / 2)) in
  let all_disjoint = Array.append left_keys disjoint_keys in
  let all_overlap = Array.append left_keys overlap_keys in
  let left = build_int left_keys in
  print_header "Positive integer keys";
  profile_int_case "disjoint" all_disjoint (2 * profile_size) left
    (build_int disjoint_keys);
  profile_int_case "half overlap" all_overlap
    (profile_size + (profile_size / 2)) left (build_int overlap_keys);
  profile_int_case "subset" left_keys profile_size left (build_int subset_keys);
  profile_int_case "equal" left_keys profile_size left left;
  profile_int_case "empty right" left_keys profile_size left I.empty

let profile_strings title prefix =
  let keys start =
    Array.init profile_size (fun index -> string_key ~prefix (start + index))
  in
  let left_keys = keys 0 in
  let disjoint_keys = keys profile_size in
  let overlap_keys = keys (profile_size / 2) in
  let subset_keys = Array.sub left_keys 0 (max 1 (profile_size / 2)) in
  let all_disjoint = Array.append left_keys disjoint_keys in
  let all_overlap = Array.append left_keys overlap_keys in
  let left = build_string left_keys in
  print_header title;
  profile_string_case "disjoint" all_disjoint (2 * profile_size) left
    (build_string disjoint_keys);
  profile_string_case "half overlap" all_overlap
    (profile_size + (profile_size / 2)) left (build_string overlap_keys);
  profile_string_case "subset" left_keys profile_size left (build_string subset_keys);
  profile_string_case "equal" left_keys profile_size left left;
  profile_string_case "empty right" left_keys profile_size left S.empty

let () =
  Printf.printf
    "Patricia union-worker allocation profile (words; legacy public worker selected)\n";
  profile_int ();
  profile_strings "Eight-character string keys" "";
  profile_strings "String keys with a 192-byte common prefix"
    (Stdlib.String.make 192 'p');
  print_endline "Patricia union-worker allocation profile: ok"
