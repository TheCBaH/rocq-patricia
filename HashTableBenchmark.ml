(* Repeated, checked integer measurements.  Inputs, expected values, and maps
   used by updates are made before timing; each task retains its result and
   returns an observable checksum. *)

let pattern = match Sys.getenv_opt "HASHTABLE_BENCH_PATTERN" with
  | None | Some "ascending" -> "ascending"
  | Some "shuffled" -> "shuffled"
  | Some "root-slot-collision" -> "root-slot-collision"
  | Some "constant-hash" -> "constant-hash"
  | Some "divergence-depth-0" -> "divergence-depth-0"
  | Some "divergence-depth-1" -> "divergence-depth-1"
  | Some "divergence-depth-2" -> "divergence-depth-2"
  | Some "divergence-depth-3" -> "divergence-depth-3"
  | Some "divergence-depth-4" -> "divergence-depth-4"
  | Some "divergence-depth-5" -> "divergence-depth-5"
  | Some value -> failwith ("unknown HASHTABLE_BENCH_PATTERN " ^ value)

module Key = struct
  type t = int
  let equal = Int.equal
  let hash ~seed key = if pattern = "constant-hash" then 0 else key lxor seed
end

module Hash_map = HashMap.Make (Key)
module Native_hash_map = HashMapNative.Make (Key)
module Ordered_map = Map.Make (Int)
module Bench = HashTableBenchmarkSupport

let fail message = failwith ("HashTable benchmark: " ^ message)
let int_env name default = match Sys.getenv_opt name with None -> default | Some v -> int_of_string v
let size = int_env "HASHTABLE_BENCH_SIZE" 2_000
let seed = int_env "HASHTABLE_BENCH_SEED" 31

let divergence_depth = match pattern with
  | "divergence-depth-0" -> Some 0
  | "divergence-depth-1" -> Some 1
  | "divergence-depth-2" -> Some 2
  | "divergence-depth-3" -> Some 3
  | "divergence-depth-4" -> Some 4
  | "divergence-depth-5" -> Some 5
  | _ -> None

(* Make normalized hashes agree through [depth] five-bit chunks, then split
   at that chunk.  The key uses the benchmark seed so the HAMT callback
   [(key lxor seed)] produces the intended hash.  Skip the one ordinal that
   could make a positive Patricia comparison key equal to zero. *)
let divergence_key depth offset index =
  let shift = 5 * depth in
  let forbidden =
    if seed >= 0 && seed land ((1 lsl shift) - 1) = 0 then Some (seed lsr shift)
    else None in
  let ordinal = offset + index in
  let ordinal = match forbidden with
    | Some value when ordinal >= value -> ordinal + 1
    | _ -> ordinal
  in
  seed lxor (ordinal lsl shift)

let key_at offset index = match divergence_depth with
  | Some depth -> divergence_key depth offset index
  | None when pattern = "root-slot-collision" -> (offset + index) lsl 5
  | None -> offset + index

let keys =
  let keys = Array.init size (key_at 1) in
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
let fresh_key index = key_at (size + 1) index

let new_bindings = Array.to_list (Array.mapi (fun index _ -> fresh_key index, "new-" ^ string_of_int index) keys)
let new_keys = Array.map fst (Array.of_list new_bindings)
let missing_keys = Array.init size (key_at ((2 * size) + 1))
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

let check_elements name get elements map expected =
  let found = elements map in
  if Stdlib.List.length found <> Stdlib.List.length expected then
    fail (name ^ " element count mismatch");
  if Stdlib.List.sort Stdlib.compare found <> Stdlib.List.sort Stdlib.compare expected then
    fail (name ^ " element binding mismatch");
  Stdlib.List.iter (fun (key, value) ->
      if get key map <> Some value then fail (name ^ " element mismatch")) expected

let run_persistent name empty of_list set get mem remove elements =
  let count = samples () in
  let bases = Array.init count (fun _ -> of_list duplicate_bindings) in
  let built_first = Array.make 1 (empty ()) in
  let built_set = Array.make 1 (empty ()) in
  let changed = Array.make 1 (empty ()) in
  let added = Array.make 1 (empty ()) in
  let changed_histories = Array.make 1 [ empty () ] in
  let added_histories = Array.make 1 [ empty () ] in
  let removed = Array.make 1 (empty ()) in
  let missing_removed = Array.make 1 (empty ()) in
  let retain repetition results value =
    if repetition = 0 then results.(0) <- value in
  let task operation run = { Bench.implementation = name; operation; run } in
  let tasks = [
    task "build/of_list-first-wins" (fun rep ->
        let result = of_list duplicate_bindings in retain rep built_first result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "build/repeated-set" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) duplicate_bindings in
        retain rep built_set result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "lookup/hit" (fun rep -> lookup_checksum get bases.(slot rep) keys);
    task "lookup/miss" (fun rep -> lookup_checksum get bases.(slot rep) missing_keys);
    task "mem/hit" (fun rep -> mem_checksum mem bases.(slot rep) keys);
    task "mem/miss" (fun rep -> mem_checksum mem bases.(slot rep) missing_keys);
    task "set/existing/latest-root" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) bases.(slot rep) updated_bindings in
        retain rep changed result; lookup_checksum get result keys);
    task "set/new/latest-root" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map) bases.(slot rep) new_bindings in
        retain rep added result; lookup_checksum get result new_keys);
    task "set/existing/all-prefix-roots" (fun rep ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [ bases.(slot rep) ] updated_bindings in
        retain rep changed_histories roots;
        lookup_checksum get (Stdlib.List.hd roots) keys);
    task "set/new/all-prefix-roots" (fun rep ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [ bases.(slot rep) ] new_bindings in
        retain rep added_histories roots;
        lookup_checksum get (Stdlib.List.hd roots) new_keys);
    task "remove/present" (fun rep ->
        let result = Stdlib.List.fold_left (fun map (key, _) -> remove key map) bases.(slot rep) bindings in
        retain rep removed result; lookup_checksum get result keys);
    task "remove/missing" (fun rep ->
        let result = Array.fold_left (fun map key -> remove key map) bases.(slot rep) missing_keys in
        retain rep missing_removed result; lookup_checksum get result keys);
    task "elements" (fun rep ->
        Stdlib.List.fold_left (fun total (key, value) -> total lxor key lxor String.length value) 0
          (elements bases.(slot rep)));
  ] in
  Bench.measure tasks;
  (* Every timed task returns an observable checksum.  Retain one measured
     result for the independent full semantic pass without retaining the other
     full collision histories until the benchmark process exits. *)
  let index = 0 in
    check_map (name ^ " of_list") get built_first.(index) bindings;
    if get keys.(0) built_set.(index) <> Some ("duplicate-ignored-" ^ string_of_int keys.(0)) then
      fail (name ^ " repeated-set duplicate mismatch");
    check_map (name ^ " update") get changed.(index) updated_bindings;
    let updated_roots = changed_histories.(index) in
    if Stdlib.List.length updated_roots <> size + 1 then
      fail (name ^ " update history count mismatch");
    check_map (name ^ " update history latest") get (Stdlib.List.hd updated_roots) updated_bindings;
    check_map (name ^ " update history oldest") get (Stdlib.List.hd (Stdlib.List.rev updated_roots)) bindings;
    check_map (name ^ " missing remove") get missing_removed.(index) bindings;
    if Array.exists (fun key -> get key removed.(index) <> None) keys then fail (name ^ " present remove mismatch");
    check_map (name ^ " added old keys") get added.(index) bindings;
    Stdlib.List.iter (fun (key, value) -> if get key added.(index) <> Some value then fail (name ^ " new set mismatch")) new_bindings;
    let added_roots = added_histories.(index) in
    if Stdlib.List.length added_roots <> size + 1 then
      fail (name ^ " new history count mismatch");
    check_map (name ^ " new history old keys") get (Stdlib.List.hd added_roots) bindings;
    Stdlib.List.iter (fun (key, value) ->
        if get key (Stdlib.List.hd added_roots) <> Some value then
          fail (name ^ " new history latest mismatch")) new_bindings;
    check_map (name ^ " new history oldest") get (Stdlib.List.hd (Stdlib.List.rev added_roots)) bindings;
    check_elements (name ^ " elements") get elements bases.(index) bindings;
  if Bench.live_heap_enabled () then begin
    let latest = Bench.live_heap ~implementation:name ~policy:"latest-root" (fun () ->
        Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) bindings) in
    check_map (name ^ " latest root") get latest bindings;
    let roots = Bench.live_heap ~implementation:name ~policy:"all-prefix-roots" (fun () ->
        Stdlib.List.fold_left (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots) [ empty () ] bindings) in
    if Stdlib.List.length roots <> size + 1 then fail (name ^ " retained root count mismatch");
    check_map (name ^ " all-prefix root") get (Stdlib.List.hd roots) bindings
  end

let run_hashtbl () =
  let build_first pairs = Stdlib.List.fold_right (fun (key, value) table -> Hashtbl.replace table key value; table)
      pairs (Hashtbl.create size) in
  let count = samples () in
  let bases = Array.init count (fun _ -> build_first duplicate_bindings) in
  let update_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let add_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let remove_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let missing_remove_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let first_results = Array.init count (fun _ -> Hashtbl.create size) in
  let set_results = Array.init count (fun _ -> Hashtbl.create size) in
  let get key table = Hashtbl.find_opt table key in
  let elements table = Hashtbl.fold (fun key value pairs -> (key, value) :: pairs) table [] in
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
    task "set/existing" (fun rep ->
        let result = update_inputs.(slot rep) in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) updated_bindings;
        lookup_checksum get result keys);
    task "set/new" (fun rep ->
        let result = add_inputs.(slot rep) in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) new_bindings;
        lookup_checksum get result new_keys);
    task "remove/present" (fun rep ->
        let result = remove_inputs.(slot rep) in
        Stdlib.List.iter (fun (key, _) -> Hashtbl.remove result key) bindings;
        lookup_checksum get result keys);
    task "remove/missing" (fun rep ->
        let result = missing_remove_inputs.(slot rep) in
        Array.iter (fun key -> Hashtbl.remove result key) missing_keys;
        lookup_checksum get result keys);
    task "elements" (fun rep ->
        Stdlib.List.fold_left (fun total (key, value) -> total lxor key lxor String.length value)
          0 (elements bases.(slot rep)));
  ];
  Array.iter (fun table -> check_map "Hashtbl first-wins build" get table bindings) first_results;
  Array.iter (fun table ->
      if get keys.(0) table <> Some ("duplicate-ignored-" ^ string_of_int keys.(0)) then
      fail "Hashtbl repeated-set duplicate mismatch") set_results;
  Array.iter (fun table -> check_map "Hashtbl update" get table updated_bindings) update_inputs;
  Array.iter (fun table ->
      check_map "Hashtbl added old keys" get table bindings;
      Stdlib.List.iter (fun (key, value) ->
          if get key table <> Some value then fail "Hashtbl new set mismatch") new_bindings) add_inputs;
  Array.iter (fun table ->
      if Array.exists (fun key -> get key table <> None) keys then
        fail "Hashtbl present remove mismatch") remove_inputs;
  Array.iter (fun table -> check_map "Hashtbl missing remove" get table bindings) missing_remove_inputs;
  Array.iter (fun table -> check_elements "Hashtbl elements" get elements table bindings) bases;
  if Bench.live_heap_enabled () then
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
