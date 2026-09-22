(* Repeated, checked integer measurements.  Inputs, expected values, and maps
   used by updates are made before timing; each task retains its result and
   returns an observable checksum. *)

module Key = struct
  type t = int
  let equal = Int.equal
  let hash ~seed key = key lxor seed
end

module Hash_map = HashMap.Make (Key)
module Native_hash_map = HashMapNative.Make (Key)
module Ordered_map = Map.Make (Int)
module Bench = HashTableBenchmarkSupport

let fail message = failwith ("HashTable benchmark: " ^ message)
let int_env name default = match Sys.getenv_opt name with None -> default | Some v -> int_of_string v
let size = int_env "HASHTABLE_BENCH_SIZE" 2_000
let seed = int_env "HASHTABLE_BENCH_SEED" 31

let pattern = match Sys.getenv_opt "HASHTABLE_BENCH_PATTERN" with
  | None | Some "ascending" -> "ascending"
  | Some "shuffled" -> "shuffled"
  | Some "root-slot-collision" -> "root-slot-collision"
  | Some value -> fail ("unknown HASHTABLE_BENCH_PATTERN " ^ value)

let keys =
  let keys = Array.init size (fun index ->
      if pattern = "root-slot-collision" then (index + 1) lsl 5 else index + 1) in
  if pattern = "shuffled" then begin
    let random = Random.State.make [| seed; size; 0x51eed |] in
    for index = size - 1 downto 1 do
      let other = Random.State.int random (index + 1) in
      let value = keys.(index) in keys.(index) <- keys.(other); keys.(other) <- value
    done
  end;
  keys

let bindings = Array.to_list (Array.map (fun key -> key, string_of_int key) keys)
let duplicate_bindings =
  match bindings with
  | (key, value) :: _ -> bindings @ [ key, "duplicate-ignored-" ^ value ]
  | [] -> assert false
let updated_bindings = Array.to_list (Array.map (fun key -> key, "updated-" ^ string_of_int key) keys)
let new_bindings = Array.to_list (Array.mapi (fun index _ -> size + index + 1, "new-" ^ string_of_int index) keys)
let new_keys = Array.map fst (Array.of_list new_bindings)
let missing_keys = Array.map (fun key -> key + (2 * size) + 1) keys
let samples () = (Bench.config ()).repetitions + 1
let slot repetition = if repetition < 0 then samples () - 1 else repetition

let lookup_checksum get map query =
  Array.fold_left (fun total key -> match get key map with
      | Some value -> total lxor String.length value | None -> total lxor 0x9e3779) 0 query
let mem_checksum mem map query =
  Array.fold_left (fun total key -> if mem key map then total + 1 else total) 0 query

let check_map name get map expected =
  Stdlib.List.iter (fun (key, value) -> if get key map <> Some value then fail (name ^ " binding mismatch")) expected;
  if get missing_keys.(0) map <> None then fail (name ^ " missing lookup mismatch")

let run_persistent name empty of_list set get mem remove elements =
  let count = samples () in
  let bases = Array.init count (fun _ -> of_list duplicate_bindings) in
  let built_first = Array.make count (empty ()) in
  let built_set = Array.make count (empty ()) in
  let changed = Array.make count (empty ()) in
  let added = Array.make count (empty ()) in
  let removed = Array.make count (empty ()) in
  let missing_removed = Array.make count (empty ()) in
  let task operation run = { Bench.implementation = name; operation; run } in
  let tasks = [
    task "build/of_list-first-wins" (fun rep ->
        let result = of_list duplicate_bindings in built_first.(slot rep) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "build/repeated-set" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) duplicate_bindings in
        built_set.(slot rep) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "lookup/hit" (fun rep -> lookup_checksum get bases.(slot rep) keys);
    task "lookup/miss" (fun rep -> lookup_checksum get bases.(slot rep) missing_keys);
    task "mem/hit" (fun rep -> mem_checksum mem bases.(slot rep) keys);
    task "mem/miss" (fun rep -> mem_checksum mem bases.(slot rep) missing_keys);
    task "set/existing" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) bases.(slot rep) updated_bindings in
        changed.(slot rep) <- result; lookup_checksum get result keys);
    task "set/new" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) bases.(slot rep) new_bindings in
        added.(slot rep) <- result; lookup_checksum get result new_keys);
    task "remove/present" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, _) -> remove key map) bases.(slot rep) bindings in
        removed.(slot rep) <- result; lookup_checksum get result keys);
    task "remove/missing" (fun rep ->
        let result = Array.fold_left (fun map key -> remove key map) bases.(slot rep) missing_keys in
        missing_removed.(slot rep) <- result; lookup_checksum get result keys);
    task "elements" (fun rep ->
        Stdlib.List.fold_left (fun total (key, value) -> total lxor key lxor String.length value) 0
          (elements bases.(slot rep)));
  ] in
  Bench.measure tasks;
  for index = 0 to count - 1 do
    check_map (name ^ " of_list") get built_first.(index) bindings;
    if get keys.(0) built_set.(index) <> Some ("duplicate-ignored-" ^ string_of_int keys.(0)) then
      fail (name ^ " repeated-set duplicate mismatch");
    check_map (name ^ " update") get changed.(index) updated_bindings;
    check_map (name ^ " missing remove") get missing_removed.(index) bindings;
    if Array.exists (fun key -> get key removed.(index) <> None) keys then fail (name ^ " present remove mismatch");
    check_map (name ^ " added old keys") get added.(index) bindings;
    Stdlib.List.iter (fun (key, value) -> if get key added.(index) <> Some value then fail (name ^ " new set mismatch")) new_bindings
  done;
  let latest = Bench.live_heap ~implementation:name ~policy:"latest-root" (fun () ->
      Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) bindings) in
  check_map (name ^ " latest root") get latest bindings;
  let roots = Bench.live_heap ~implementation:name ~policy:"all-prefix-roots" (fun () ->
      Stdlib.List.fold_left (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots) [ empty () ] bindings) in
  if Stdlib.List.length roots <> size + 1 then fail (name ^ " retained root count mismatch");
  check_map (name ^ " all-prefix root") get (Stdlib.List.hd roots) bindings

let run_hashtbl () =
  let build_first pairs = Stdlib.List.fold_right (fun (key, value) table -> Hashtbl.replace table key value; table)
      pairs (Hashtbl.create size) in
  let count = samples () in
  let bases = Array.init count (fun _ -> build_first duplicate_bindings) in
  let first_results = Array.init count (fun _ -> Hashtbl.create size) in
  let set_results = Array.init count (fun _ -> Hashtbl.create size) in
  let get key table = Hashtbl.find_opt table key in
  let task operation run = { Bench.implementation = "OCaml Hashtbl"; operation; run } in
  Bench.measure [
    task "build/of_list-first-wins" (fun rep ->
        let result = build_first duplicate_bindings in first_results.(slot rep) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "build/repeated-set" (fun rep ->
        let result = Hashtbl.create size in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) duplicate_bindings;
        set_results.(slot rep) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "lookup/hit" (fun rep -> lookup_checksum get bases.(slot rep) keys);
    task "lookup/miss" (fun rep -> lookup_checksum get bases.(slot rep) missing_keys);
    task "mem/hit" (fun rep -> mem_checksum (fun key table -> Hashtbl.mem table key) bases.(slot rep) keys);
    task "mem/miss" (fun rep -> mem_checksum (fun key table -> Hashtbl.mem table key) bases.(slot rep) missing_keys);
    task "elements" (fun rep -> Hashtbl.fold (fun key value total -> total lxor key lxor String.length value)
        bases.(slot rep) 0);
  ];
  Array.iter (fun table -> check_map "Hashtbl first-wins build" get table bindings) first_results;
  Array.iter (fun table ->
      if get keys.(0) table <> Some ("duplicate-ignored-" ^ string_of_int keys.(0)) then
        fail "Hashtbl repeated-set duplicate mismatch") set_results;
  ignore (Bench.live_heap ~implementation:"OCaml Hashtbl" ~policy:"single-version" (fun () -> build_first bindings))

let () =
  if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive";
  Bench.start ~workload:(pattern ^ " positive integer keys") ~size ~seed;
  run_persistent "Public generated HAMT" (fun () -> Hash_map.empty ~seed) (Hash_map.of_list ~seed)
    Hash_map.set Hash_map.get Hash_map.mem Hash_map.remove Hash_map.elements;
  run_persistent "Standalone array HAMT" (fun () -> Native_hash_map.empty ~seed) (Native_hash_map.of_list ~seed)
    Native_hash_map.set Native_hash_map.get Native_hash_map.mem Native_hash_map.remove Native_hash_map.elements;
  run_persistent "Stdlib Map" (fun () -> Ordered_map.empty)
    (fun pairs -> Stdlib.List.fold_right (fun (key, value) map -> Ordered_map.add key value map) pairs Ordered_map.empty)
    Ordered_map.add Ordered_map.find_opt Ordered_map.mem Ordered_map.remove Ordered_map.bindings;
  run_hashtbl ();
  Bench.finish ();
  Printf.printf "HashTable corrected benchmark passed (%d bindings)\n%!" size
