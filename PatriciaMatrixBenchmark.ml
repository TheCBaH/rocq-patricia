(* Integer matrix companion for the HAMT benchmark.  It is deliberately a
   separate executable: the Patricia and HAMT extraction trees both contain
   un-namespaced support modules, so linking them together would invalidate
   either extraction's object graph.  The runner gives both executables the
   same key construction, repetition protocol, and JSONL metadata. *)

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

module Patricia = PatriciaMap
module Ordered_map = Map.Make (Int)
module Bench = HashTableBenchmarkSupport

module Int_hash = Hashtbl.Make (struct
  type t = int
  let equal = Int.equal
  let hash = Hashtbl.hash
end)

let fail message = failwith ("Patricia matrix benchmark: " ^ message)
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

(* Match [HashTableBenchmark]'s positive key construction exactly.  These
   keys share every routing chunk before [depth] under the HAMT callback. *)
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
  let values = Array.init size (key_at 1) in
  if pattern = "shuffled" then begin
    let random = Random.State.make [| seed; size; 0x51eed |] in
    for index = size - 1 downto 1 do
      let other = Random.State.int random (index + 1) in
      let value = values.(index) in values.(index) <- values.(other); values.(other) <- value
    done
  end;
  values

let bindings = Array.to_list (Array.map (fun key -> key, string_of_int key) keys)
let duplicate_bindings =
  match bindings with
  | (key, value) :: _ -> bindings @ [key, "duplicate-ignored-" ^ value]
  | [] -> assert false
let updated_bindings =
  Array.to_list (Array.map (fun key -> key, "updated-" ^ string_of_int key) keys)
let fresh_key index = key_at (size + 1) index
let new_bindings =
  Array.to_list (Array.mapi (fun index _ -> fresh_key index, "new-" ^ string_of_int index) keys)
let new_keys = Array.map fst (Array.of_list new_bindings)
let missing_keys = Array.init size (key_at ((2 * size) + 1))

let patricia_keys = Array.map Patricia.Key.of_int_exn keys
let patricia_bindings =
  Stdlib.List.map (fun (key, value) -> Patricia.Key.of_int_exn key, value) bindings
let patricia_duplicate_bindings =
  Stdlib.List.map (fun (key, value) -> Patricia.Key.of_int_exn key, value) duplicate_bindings
let patricia_updated_bindings =
  Stdlib.List.map (fun (key, value) -> Patricia.Key.of_int_exn key, value) updated_bindings
let patricia_new_bindings =
  Stdlib.List.map (fun (key, value) -> Patricia.Key.of_int_exn key, value) new_bindings
let patricia_new_keys = Array.map Patricia.Key.of_int_exn new_keys
let patricia_missing_keys = Array.map Patricia.Key.of_int_exn missing_keys

let samples () = (Bench.config ()).repetitions + 1
let slot repetition = if repetition < 0 then samples () - 1 else repetition

let lookup_checksum get map query =
  Array.fold_left (fun total key -> match get key map with
      | Some value -> total lxor Stdlib.String.length value | None -> total lxor 0x9e3779) 0 query
let mem_checksum mem map query =
  Array.fold_left (fun total key -> if mem key map then total + 1 else total) 0 query

let check_map missing name get map expected =
  Stdlib.List.iter (fun (key, value) ->
      if get key map <> Some value then fail (name ^ " binding mismatch")) expected;
  if get missing.(0) map <> None then fail (name ^ " missing lookup mismatch")

let check_elements name get elements map expected =
  let found = elements map in
  if Stdlib.List.length found <> Stdlib.List.length expected then
    fail (name ^ " element count mismatch");
  if not (Stdlib.List.for_all (fun binding -> Stdlib.List.mem binding expected) found)
     || not (Stdlib.List.for_all (fun binding -> Stdlib.List.mem binding found) expected) then
    fail (name ^ " element binding mismatch");
  Stdlib.List.iter (fun (key, value) ->
      if get key map <> Some value then fail (name ^ " element mismatch")) expected

let run_persistent name ~keys ~bindings ~duplicate_bindings ~updated_bindings
    ~new_bindings ~new_keys ~missing_keys ~elements_checksum
    empty of_list set get mem remove elements =
  let count = samples () in
  let bases = Array.init count (fun _ -> of_list duplicate_bindings) in
  let built_first = Array.make count (empty ()) in
  let built_set = Array.make count (empty ()) in
  let changed = Array.make count (empty ()) in
  let added = Array.make count (empty ()) in
  let changed_histories = Array.make count [empty ()] in
  let added_histories = Array.make count [empty ()] in
  let removed = Array.make count (empty ()) in
  let missing_removed = Array.make count (empty ()) in
  let task operation run = { Bench.implementation = name; operation; run } in
  Bench.measure [
    task "build/of_list-first-wins" (fun repetition ->
        let result = of_list duplicate_bindings in built_first.(slot repetition) <- result;
        match get keys.(0) result with Some value -> Stdlib.String.length value | None -> -1);
    task "build/repeated-set" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            (empty ()) duplicate_bindings in
        built_set.(slot repetition) <- result;
        match get keys.(0) result with Some value -> Stdlib.String.length value | None -> -1);
    task "lookup/hit" (fun repetition -> lookup_checksum get bases.(slot repetition) keys);
    task "lookup/miss" (fun repetition -> lookup_checksum get bases.(slot repetition) missing_keys);
    task "mem/hit" (fun repetition -> mem_checksum mem bases.(slot repetition) keys);
    task "mem/miss" (fun repetition -> mem_checksum mem bases.(slot repetition) missing_keys);
    task "set/existing/latest-root" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            bases.(slot repetition) updated_bindings in
        changed.(slot repetition) <- result; lookup_checksum get result keys);
    task "set/new/latest-root" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            bases.(slot repetition) new_bindings in
        added.(slot repetition) <- result; lookup_checksum get result new_keys);
    task "set/existing/all-prefix-roots" (fun repetition ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [bases.(slot repetition)] updated_bindings in
        changed_histories.(slot repetition) <- roots;
        lookup_checksum get (Stdlib.List.hd roots) keys);
    task "set/new/all-prefix-roots" (fun repetition ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [bases.(slot repetition)] new_bindings in
        added_histories.(slot repetition) <- roots;
        lookup_checksum get (Stdlib.List.hd roots) new_keys);
    task "remove/present" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, _) -> remove key map)
            bases.(slot repetition) bindings in
        removed.(slot repetition) <- result; lookup_checksum get result keys);
    task "remove/missing" (fun repetition ->
        let result = Array.fold_left (fun map key -> remove key map)
            bases.(slot repetition) missing_keys in
        missing_removed.(slot repetition) <- result; lookup_checksum get result keys);
    task "elements" (fun repetition -> elements_checksum (elements bases.(slot repetition)));
  ];
  let repeated_key, repeated_value = Stdlib.List.hd (Stdlib.List.rev duplicate_bindings) in
  (* The timed checksums retain every sample.  One measured result receives the
     independent full semantic pass; repeating this quadratic pass per sample
     would distort matrix wall time without strengthening timed evidence. *)
  let index = 0 in
    check_map missing_keys (name ^ " of_list") get built_first.(index) bindings;
    if get repeated_key built_set.(index) <> Some repeated_value then
      fail (name ^ " repeated-set duplicate mismatch");
    check_map missing_keys (name ^ " update") get changed.(index) updated_bindings;
    let updated_roots = changed_histories.(index) in
    if Stdlib.List.length updated_roots <> size + 1 then
      fail (name ^ " update history count mismatch");
    check_map missing_keys (name ^ " update history latest") get (Stdlib.List.hd updated_roots) updated_bindings;
    check_map missing_keys (name ^ " update history oldest") get
      (Stdlib.List.hd (Stdlib.List.rev updated_roots)) bindings;
    check_map missing_keys (name ^ " missing remove") get missing_removed.(index) bindings;
    if Array.exists (fun key -> get key removed.(index) <> None) keys then
      fail (name ^ " present remove mismatch");
    check_map missing_keys (name ^ " added old keys") get added.(index) bindings;
    Stdlib.List.iter (fun (key, value) ->
        if get key added.(index) <> Some value then fail (name ^ " new set mismatch")) new_bindings;
    let added_roots = added_histories.(index) in
    if Stdlib.List.length added_roots <> size + 1 then
      fail (name ^ " new history count mismatch");
    check_map missing_keys (name ^ " new history old keys") get (Stdlib.List.hd added_roots) bindings;
    Stdlib.List.iter (fun (key, value) ->
        if get key (Stdlib.List.hd added_roots) <> Some value then
          fail (name ^ " new history latest mismatch")) new_bindings;
    check_map missing_keys (name ^ " new history oldest") get
      (Stdlib.List.hd (Stdlib.List.rev added_roots)) bindings;
    check_elements (name ^ " elements") get elements bases.(index) bindings;
  let latest = Bench.live_heap ~implementation:name ~policy:"latest-root" (fun () ->
      Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) bindings) in
  check_map missing_keys (name ^ " latest root") get latest bindings;
  let roots = Bench.live_heap ~implementation:name ~policy:"all-prefix-roots" (fun () ->
      Stdlib.List.fold_left
        (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
        [empty ()] bindings) in
  if Stdlib.List.length roots <> size + 1 then fail (name ^ " retained root count mismatch");
  check_map missing_keys (name ^ " all-prefix root") get (Stdlib.List.hd roots) bindings

let run_hashtbl () =
  let build_first pairs =
    Stdlib.List.fold_right (fun (key, value) table -> Int_hash.replace table key value; table)
      pairs (Int_hash.create size)
  in
  let count = samples () in
  let bases = Array.init count (fun _ -> build_first duplicate_bindings) in
  let update_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let add_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let remove_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let missing_remove_inputs = Array.init count (fun _ -> build_first duplicate_bindings) in
  let first_results = Array.init count (fun _ -> Int_hash.create size) in
  let set_results = Array.init count (fun _ -> Int_hash.create size) in
  let get key table = Int_hash.find_opt table key in
  let elements table = Int_hash.fold (fun key value pairs -> (key, value) :: pairs) table [] in
  let task operation run = { Bench.implementation = "OCaml Hashtbl"; operation; run } in
  Bench.measure [
    task "build/of_list-first-wins" (fun repetition ->
        let result = build_first duplicate_bindings in first_results.(slot repetition) <- result;
        match get keys.(0) result with Some value -> Stdlib.String.length value | None -> -1);
    task "build/repeated-set" (fun repetition ->
        let result = Int_hash.create size in
        Stdlib.List.iter (fun (key, value) -> Int_hash.replace result key value) duplicate_bindings;
        set_results.(slot repetition) <- result;
        match get keys.(0) result with Some value -> Stdlib.String.length value | None -> -1);
    task "lookup/hit" (fun repetition -> lookup_checksum get bases.(slot repetition) keys);
    task "lookup/miss" (fun repetition -> lookup_checksum get bases.(slot repetition) missing_keys);
    task "mem/hit" (fun repetition -> mem_checksum (fun key table -> Int_hash.mem table key) bases.(slot repetition) keys);
    task "mem/miss" (fun repetition -> mem_checksum (fun key table -> Int_hash.mem table key) bases.(slot repetition) missing_keys);
    task "set/existing" (fun repetition ->
        let result = update_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, value) -> Int_hash.replace result key value) updated_bindings;
        lookup_checksum get result keys);
    task "set/new" (fun repetition ->
        let result = add_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, value) -> Int_hash.replace result key value) new_bindings;
        lookup_checksum get result new_keys);
    task "remove/present" (fun repetition ->
        let result = remove_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, _) -> Int_hash.remove result key) bindings;
        lookup_checksum get result keys);
    task "remove/missing" (fun repetition ->
        let result = missing_remove_inputs.(slot repetition) in
        Array.iter (fun key -> Int_hash.remove result key) missing_keys;
        lookup_checksum get result keys);
    task "elements" (fun repetition ->
        Stdlib.List.fold_left (fun total (key, value) -> total lxor key lxor Stdlib.String.length value)
          0 (elements bases.(slot repetition)));
  ];
  Array.iter (fun table -> check_map missing_keys "Hashtbl first-wins build" get table bindings) first_results;
  Array.iter (fun table ->
      if get keys.(0) table <> Some ("duplicate-ignored-" ^ string_of_int keys.(0)) then
        fail "Hashtbl repeated-set duplicate mismatch") set_results;
  Array.iter (fun table -> check_map missing_keys "Hashtbl update" get table updated_bindings) update_inputs;
  Array.iter (fun table ->
      check_map missing_keys "Hashtbl added old keys" get table bindings;
      Stdlib.List.iter (fun (key, value) ->
          if get key table <> Some value then fail "Hashtbl new set mismatch") new_bindings) add_inputs;
  Array.iter (fun table ->
      if Array.exists (fun key -> get key table <> None) keys then
        fail "Hashtbl present remove mismatch") remove_inputs;
  Array.iter (fun table -> check_map missing_keys "Hashtbl missing remove" get table bindings) missing_remove_inputs;
  Array.iter (fun table -> check_elements "Hashtbl elements" get elements table bindings) bases;
  ignore (Bench.live_heap ~implementation:"OCaml Hashtbl" ~policy:"single-version" (fun () -> build_first bindings))

let int_elements_checksum pairs =
  Stdlib.List.fold_left (fun total (key, value) -> total lxor key lxor Stdlib.String.length value) 0 pairs
let patricia_elements_checksum pairs =
  Stdlib.List.fold_left (fun total (key, value) ->
      total lxor Patricia.Key.to_int key lxor Stdlib.String.length value) 0 pairs

let () =
  if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive";
  Bench.start ~workload:(pattern ^ " positive integer keys") ~size ~seed;
  run_persistent "Patricia" ~keys:patricia_keys ~bindings:patricia_bindings
    ~duplicate_bindings:patricia_duplicate_bindings ~updated_bindings:patricia_updated_bindings
    ~new_bindings:patricia_new_bindings ~new_keys:patricia_new_keys
    ~missing_keys:patricia_missing_keys ~elements_checksum:patricia_elements_checksum
    (fun () -> Patricia.empty) Patricia.of_list
    Patricia.set Patricia.get Patricia.mem Patricia.remove Patricia.elements;
  run_persistent "Stdlib Map" ~keys ~bindings ~duplicate_bindings ~updated_bindings
    ~new_bindings ~new_keys ~missing_keys ~elements_checksum:int_elements_checksum
    (fun () -> Ordered_map.empty)
    (fun pairs -> Stdlib.List.fold_right (fun (key, value) map -> Ordered_map.add key value map)
       pairs Ordered_map.empty)
    Ordered_map.add Ordered_map.find_opt Ordered_map.mem Ordered_map.remove Ordered_map.bindings;
  run_hashtbl ();
  Bench.finish ();
  Printf.printf "Patricia matrix benchmark passed (%d bindings)\n%!" size
