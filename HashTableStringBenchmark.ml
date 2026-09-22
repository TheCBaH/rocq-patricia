(* Checked string-key comparison for the public generated-native and private
   fresh-array backends, [Map.Make(String)], and OCaml's imperative [Hashtbl].
   It is a local measurement harness, not a portable performance claim. *)

module Key = struct
  type t = string
  let equal = String.equal
  let hash ~seed key = Hashtbl.seeded_hash seed key
end

module Hash_map = HashMap.Make (Key)
module Native_hash_map = HashMapNative.Make (Key)
module Ordered_map = Map.Make (String)
module Bench = HashTableBenchmarkSupport

let size =
  match Sys.getenv_opt "HASHTABLE_BENCH_SIZE" with
  | None -> 2_000
  | Some value -> int_of_string value

let seed =
  match Sys.getenv_opt "HASHTABLE_BENCH_SEED" with
  | None -> 31
  | Some value -> int_of_string value

type workload = Fixed_width | Mixed_length | Common_prefix

let workload =
  match Sys.getenv_opt "HASHTABLE_BENCH_STRING_PATTERN" with
  | None | Some "fixed-width" -> Fixed_width
  | Some "mixed-length" -> Mixed_length
  | Some "common-prefix" -> Common_prefix
  | Some value ->
      failwith ("HashTable string benchmark: unknown HASHTABLE_BENCH_STRING_PATTERN " ^ value)

let workload_name, key_of_index =
  match workload with
  | Fixed_width ->
      "fixed-width decimal string keys", (fun index -> Printf.sprintf "key-%08d" index)
  | Mixed_length ->
      "mixed-length byte string keys", (fun index ->
          let width = 1 + (index mod 31) in
          Printf.sprintf "%02d:%0*d" width width index)
  | Common_prefix ->
      let prefix = String.make 192 'p' in
      "192-byte common-prefix string keys", (fun index ->
          prefix ^ Printf.sprintf ":%08d" index)

let fail message = failwith ("HashTable string benchmark: " ^ message)

let () = if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive"

let keys = Array.init size key_of_index
let bindings = Array.to_list (Array.mapi (fun index key -> key, string_of_int index) keys)
let duplicate_bindings =
  match bindings with
  | (key, value) :: _ -> bindings @ [ key, "duplicate-ignored-" ^ value ]
  | [] -> assert false
let updated_bindings =
  Array.to_list (Array.map (fun key -> key, "updated-" ^ key) keys)
let new_bindings =
  Array.to_list (Array.mapi (fun index _ ->
      "fresh:" ^ key_of_index (size + index), "new-" ^ string_of_int index) keys)
let new_keys = Array.map fst (Array.of_list new_bindings)
let missing_keys = Array.map (fun key -> "missing:" ^ key) keys
let samples () = (Bench.config ()).repetitions + 1
let slot repetition = if repetition < 0 then samples () - 1 else repetition

let lookup_checksum get map query =
  Array.fold_left (fun total key -> match get key map with
      | Some value -> total lxor String.length value | None -> total lxor 0x9e3779) 0 query
let mem_checksum mem map query =
  Array.fold_left (fun total key -> if mem key map then total + 1 else total) 0 query
let elements_checksum elements map =
  Stdlib.List.fold_left (fun total (key, value) ->
      total lxor String.length key lxor String.length value) 0 (elements map)

let check_map name get map expected =
  Stdlib.List.iter (fun (key, value) ->
      if get key map <> Some value then fail (name ^ " binding mismatch")) expected;
  if get missing_keys.(0) map <> None then fail (name ^ " missing lookup mismatch")

let check_elements name get elements map expected =
  let found = elements map in
  if Stdlib.List.length found <> Stdlib.List.length expected then
    fail (name ^ " element count mismatch");
  if not (Stdlib.List.for_all (fun binding -> Stdlib.List.mem binding expected) found)
     || not (Stdlib.List.for_all (fun binding -> Stdlib.List.mem binding found) expected) then
    fail (name ^ " element binding mismatch");
  Stdlib.List.iter (fun (key, value) ->
      if get key map <> Some value then fail (name ^ " element mismatch")) expected

let run_persistent name empty of_list set get mem remove elements =
  let count = samples () in
  let bases = Array.init count (fun _ -> of_list duplicate_bindings) in
  let built_first = Array.make count (empty ()) in
  let built_set = Array.make count (empty ()) in
  let changed = Array.make count (empty ()) in
  let added = Array.make count (empty ()) in
  let changed_histories = Array.make count [ empty () ] in
  let added_histories = Array.make count [ empty () ] in
  let removed = Array.make count (empty ()) in
  let missing_removed = Array.make count (empty ()) in
  let task operation run = { Bench.implementation = name; operation; run } in
  Bench.measure [
    task "build/of_list-first-wins" (fun repetition ->
        let result = of_list duplicate_bindings in
        built_first.(slot repetition) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "build/repeated-set" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            (empty ()) duplicate_bindings in
        built_set.(slot repetition) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "lookup/hit" (fun repetition -> lookup_checksum get bases.(slot repetition) keys);
    task "lookup/miss" (fun repetition -> lookup_checksum get bases.(slot repetition) missing_keys);
    task "mem/hit" (fun repetition -> mem_checksum mem bases.(slot repetition) keys);
    task "mem/miss" (fun repetition -> mem_checksum mem bases.(slot repetition) missing_keys);
    task "set/existing/latest-root" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            bases.(slot repetition) updated_bindings in
        changed.(slot repetition) <- result;
        lookup_checksum get result keys);
    task "set/new/latest-root" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, value) -> set key value map)
            bases.(slot repetition) new_bindings in
        added.(slot repetition) <- result;
        lookup_checksum get result new_keys);
    task "set/existing/all-prefix-roots" (fun repetition ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [ bases.(slot repetition) ] updated_bindings in
        changed_histories.(slot repetition) <- roots;
        lookup_checksum get (Stdlib.List.hd roots) keys);
    task "set/new/all-prefix-roots" (fun repetition ->
        let roots = Stdlib.List.fold_left
            (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
            [ bases.(slot repetition) ] new_bindings in
        added_histories.(slot repetition) <- roots;
        lookup_checksum get (Stdlib.List.hd roots) new_keys);
    task "remove/present" (fun repetition ->
        let result = Stdlib.List.fold_left (fun map (key, _) -> remove key map)
            bases.(slot repetition) bindings in
        removed.(slot repetition) <- result;
        lookup_checksum get result keys);
    task "remove/missing" (fun repetition ->
        let result = Array.fold_left (fun map key -> remove key map)
            bases.(slot repetition) missing_keys in
        missing_removed.(slot repetition) <- result;
        lookup_checksum get result keys);
    task "elements" (fun repetition -> elements_checksum elements bases.(slot repetition));
  ];
  for index = 0 to count - 1 do
    check_map (name ^ " of_list") get built_first.(index) bindings;
    if get keys.(0) built_set.(index) <> Some ("duplicate-ignored-" ^ string_of_int 0) then
      fail (name ^ " repeated-set duplicate mismatch");
    check_map (name ^ " update") get changed.(index) updated_bindings;
    let updated_roots = changed_histories.(index) in
    if Stdlib.List.length updated_roots <> size + 1 then
      fail (name ^ " update history count mismatch");
    check_map (name ^ " update history latest") get (Stdlib.List.hd updated_roots) updated_bindings;
    check_map (name ^ " update history oldest") get (Stdlib.List.hd (Stdlib.List.rev updated_roots)) bindings;
    check_map (name ^ " missing remove") get missing_removed.(index) bindings;
    if Array.exists (fun key -> get key removed.(index) <> None) keys then
      fail (name ^ " present remove mismatch");
    check_map (name ^ " added old keys") get added.(index) bindings;
    Stdlib.List.iter (fun (key, value) ->
        if get key added.(index) <> Some value then fail (name ^ " new set mismatch")) new_bindings;
    let added_roots = added_histories.(index) in
    if Stdlib.List.length added_roots <> size + 1 then
      fail (name ^ " new history count mismatch");
    check_map (name ^ " new history old keys") get (Stdlib.List.hd added_roots) bindings;
    Stdlib.List.iter (fun (key, value) ->
        if get key (Stdlib.List.hd added_roots) <> Some value then
          fail (name ^ " new history latest mismatch")) new_bindings;
    check_map (name ^ " new history oldest") get (Stdlib.List.hd (Stdlib.List.rev added_roots)) bindings;
    check_elements (name ^ " elements") get elements bases.(index) bindings
  done;
  let latest = Bench.live_heap ~implementation:name ~policy:"latest-root" (fun () ->
      Stdlib.List.fold_left (fun map (key, value) -> set key value map) (empty ()) bindings) in
  check_map (name ^ " latest root") get latest bindings;
  let roots = Bench.live_heap ~implementation:name ~policy:"all-prefix-roots" (fun () ->
      Stdlib.List.fold_left
        (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
        [ empty () ] bindings) in
  if Stdlib.List.length roots <> size + 1 then fail (name ^ " retained root count mismatch");
  check_map (name ^ " all-prefix root") get (Stdlib.List.hd roots) bindings

let run_hashtbl () =
  let build_first pairs =
    Stdlib.List.fold_right (fun (key, value) table -> Hashtbl.replace table key value; table)
      pairs (Hashtbl.create size)
  in
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
    task "build/of_list-first-wins" (fun repetition ->
        let result = build_first duplicate_bindings in
        first_results.(slot repetition) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "build/repeated-set" (fun repetition ->
        let result = Hashtbl.create size in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) duplicate_bindings;
        set_results.(slot repetition) <- result;
        match get keys.(0) result with Some value -> String.length value | None -> -1);
    task "lookup/hit" (fun repetition -> lookup_checksum get bases.(slot repetition) keys);
    task "lookup/miss" (fun repetition -> lookup_checksum get bases.(slot repetition) missing_keys);
    task "mem/hit" (fun repetition ->
        mem_checksum (fun key table -> Hashtbl.mem table key) bases.(slot repetition) keys);
    task "mem/miss" (fun repetition ->
        mem_checksum (fun key table -> Hashtbl.mem table key) bases.(slot repetition) missing_keys);
    task "set/existing" (fun repetition ->
        let result = update_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) updated_bindings;
        lookup_checksum get result keys);
    task "set/new" (fun repetition ->
        let result = add_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, value) -> Hashtbl.replace result key value) new_bindings;
        lookup_checksum get result new_keys);
    task "remove/present" (fun repetition ->
        let result = remove_inputs.(slot repetition) in
        Stdlib.List.iter (fun (key, _) -> Hashtbl.remove result key) bindings;
        lookup_checksum get result keys);
    task "remove/missing" (fun repetition ->
        let result = missing_remove_inputs.(slot repetition) in
        Array.iter (fun key -> Hashtbl.remove result key) missing_keys;
        lookup_checksum get result keys);
    task "elements" (fun repetition -> elements_checksum elements bases.(slot repetition));
  ];
  Array.iter (fun table -> check_map "Hashtbl first-wins build" get table bindings) first_results;
  Array.iter (fun table ->
      if get keys.(0) table <> Some "duplicate-ignored-0" then
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
  ignore (Bench.live_heap ~implementation:"OCaml Hashtbl" ~policy:"single-version"
            (fun () -> build_first bindings))

let () =
  Bench.start ~workload:workload_name ~size ~seed;
  Printf.printf "HashTable string benchmark workload: %s [0,%d), seed %d\n%!"
    workload_name size seed;
  run_persistent "Public generated HAMT" (fun () -> Hash_map.empty ~seed) (Hash_map.of_list ~seed)
    Hash_map.set Hash_map.get Hash_map.mem Hash_map.remove Hash_map.elements;
  run_persistent "Standalone array HAMT" (fun () -> Native_hash_map.empty ~seed)
    (Native_hash_map.of_list ~seed) Native_hash_map.set Native_hash_map.get Native_hash_map.mem
    Native_hash_map.remove Native_hash_map.elements;
  run_persistent "Stdlib Map" (fun () -> Ordered_map.empty)
    (fun pairs -> Stdlib.List.fold_right (fun (key, value) map -> Ordered_map.add key value map)
       pairs Ordered_map.empty)
    Ordered_map.add Ordered_map.find_opt Ordered_map.mem Ordered_map.remove Ordered_map.bindings;
  run_hashtbl ();
  Bench.finish ();
  Printf.printf "HashTable checked string benchmark passed (%d bindings)\n%!" size
