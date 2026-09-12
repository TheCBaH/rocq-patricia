(* Comparative benchmark for the extracted Patricia trees, Stdlib.Map, and
   Stdlib.Hashtbl.

   Stdlib.Map is the standard-library balanced AVL implementation.  This is a
   measurement test: it checks every measured result against Stdlib.Map while
   reporting time and GC-word measurements instead of imposing machine-
   dependent performance thresholds. *)

module Int_avl = Map.Make (struct
  type t = int
  let compare = Stdlib.compare
end)

module String_avl = Map.Make (struct
  type t = string
  let compare = Stdlib.String.compare
end)

module Int_hash = Hashtbl.Make (struct
  type t = int
  let equal = Int.equal
  let hash = Hashtbl.hash
end)

module String_hash = Hashtbl.Make (struct
  type t = string
  let equal = Stdlib.String.equal
  let hash = Hashtbl.hash
end)

(* Benchmarks exercise the supported abstract interfaces, not the generated
   implementation modules used by the structural oracle test. *)
module Patricia = PatriciaMap
module StringPatricia = StringPatriciaMap

let patricia_key = Patricia.Key.of_int_exn

let benchmark_size =
  match Sys.getenv_opt "PATRICIA_BENCH_SIZE" with
  | None -> 10_000
  | Some value ->
      (try
         let size = int_of_string value in
         if size <= 0 then invalid_arg "PATRICIA_BENCH_SIZE must be positive";
         size
       with Failure _ -> invalid_arg "PATRICIA_BENCH_SIZE must be an integer")

let lookup_repetitions = 3

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

let nonnegative_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed < 0 then invalid_arg (name ^ " must be non-negative");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

(* A single disjoint union can take less than one clock tick.  Repeat only
   these short, pure operations inside each sample and take several samples;
   larger map traversals retain their single-run measurement cost. *)
let short_operation_samples =
  positive_env "PATRICIA_BENCH_SHORT_SAMPLES" 5

let short_operation_batch =
  positive_env "PATRICIA_BENCH_SHORT_BATCH"
    (if benchmark_size <= 100_000 then 32 else 1)

let long_prefix_length =
  nonnegative_env "PATRICIA_BENCH_LONG_PREFIX_LENGTH" 192

let string_key_space_at_least length required =
  let rec loop remaining capacity =
    if capacity >= required then true
    else if remaining = 0 then false
    else loop (remaining - 1) (capacity * 62)
  in
  loop length 1

let has_string_key_space length =
  (* Each workload builds two disjoint input ranges. *)
  string_key_space_at_least length (2 * benchmark_size)

let variable_string_key_space_at_least length required =
  let rec loop remaining width capacity =
    if capacity >= required then true
    else if remaining = 0 then false
    else
      let next_width = width * 62 in
      loop (remaining - 1) next_width (capacity + next_width)
  in
  loop length 1 0

let variable_string_max_length =
  let length = positive_env "PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH" 128 in
  if not (variable_string_key_space_at_least length (2 * benchmark_size)) then
    invalid_arg
      "PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH cannot hold two disjoint input ranges";
  length

let string_key_lengths =
  match Sys.getenv_opt "PATRICIA_BENCH_STRING_LENGTHS" with
  | None ->
      List.filter has_string_key_space [3; 4; 5]
  | Some value ->
      let parse length =
        try
          let parsed = int_of_string length in
          if parsed <= 0 then
            invalid_arg "PATRICIA_BENCH_STRING_LENGTHS lengths must be positive";
          parsed
        with Failure _ ->
          invalid_arg "PATRICIA_BENCH_STRING_LENGTHS must be comma-separated integers"
      in
      let lengths = List.map parse (Stdlib.String.split_on_char ',' value) in
      if lengths = [] then
        invalid_arg "PATRICIA_BENCH_STRING_LENGTHS must not be empty";
      List.iter
        (fun length ->
           if not (has_string_key_space length) then
             invalid_arg
               "PATRICIA_BENCH_STRING_LENGTHS contains a key length that cannot hold two disjoint input ranges")
        lengths;
      lengths

type build_measurement = {
  seconds : float;
  allocated_words : float;
  retained_words : int;
}

type operation_measurement = {
  operation_seconds : float;
  operation_allocated_words : float;
  operation_min_seconds : float;
  operation_max_seconds : float;
  operation_samples : int;
  operation_batch : int;
}

let allocated_words () =
  let stats = Gc.quick_stat () in
  stats.Gc.minor_words +. stats.Gc.major_words

let measure_build cardinal build =
  Gc.full_major ();
  Gc.compact ();
  let before_live = (Gc.stat ()).Gc.live_words in
  let before_allocated = allocated_words () in
  let started = Unix.gettimeofday () in
  let map = build () in
  let seconds = Unix.gettimeofday () -. started in
  let allocated_words = allocated_words () -. before_allocated in
  if cardinal map <> benchmark_size then
    failwith "benchmark construction produced the wrong cardinality";
  Gc.full_major ();
  Gc.compact ();
  let retained_words = (Gc.stat ()).Gc.live_words - before_live in
  (map, { seconds; allocated_words; retained_words })

let median values =
  match List.sort Stdlib.compare values with
  | [] -> invalid_arg "median of an empty sample"
  | sorted -> List.nth sorted (List.length sorted / 2)

let measure_operation ?(samples = 1) ?(batch = 1) operation =
  if samples <= 0 then invalid_arg "measure_operation: samples must be positive";
  if batch <= 0 then invalid_arg "measure_operation: batch must be positive";
  let measure_sample () =
    Gc.full_major ();
    let before_allocated = allocated_words () in
    let started = Unix.gettimeofday () in
    let rec run remaining =
      let result = operation () in
      if remaining = 1 then result else run (remaining - 1)
    in
    let result = run batch in
    let operation_seconds =
      (Unix.gettimeofday () -. started) /. float_of_int batch
    in
    let operation_allocated_words =
      (allocated_words () -. before_allocated) /. float_of_int batch
    in
    (result, operation_seconds, operation_allocated_words)
  in
  let first_result, first_seconds, first_allocated = measure_sample () in
  let rec collect remaining last_result seconds allocated =
    if remaining = 0 then last_result, seconds, allocated
    else
      let result, elapsed, words = measure_sample () in
      collect (remaining - 1) result (elapsed :: seconds) (words :: allocated)
  in
  let result, seconds, allocated =
    collect (samples - 1) first_result [first_seconds] [first_allocated]
  in
  (result, {
     operation_seconds = median seconds;
     operation_allocated_words = median allocated;
     operation_min_seconds = List.fold_left min infinity seconds;
     operation_max_seconds = List.fold_left max neg_infinity seconds;
     operation_samples = samples;
     operation_batch = batch;
   })

let measure_short_operation operation =
  measure_operation ~samples:short_operation_samples
    ~batch:short_operation_batch operation

(* Acceptance compares Patricia bindings. The AVL/hash results still serve as
   correctness oracles, but need not repeat their slower timing batches. *)
let measure_comparison_operation operation =
  if Sys.getenv_opt "PATRICIA_BENCH_FAST_COMPARISONS" = Some "1"
  then measure_operation operation
  else measure_short_operation operation

let report_build ?(operation = "build") title patricia avl hash =
  let report name measurement =
    Printf.printf
      "  %-9s %-12s %7.3f ms  retained %8d words (%5.2f/binding)  allocated %10.0f words\n"
      name operation
      (1000. *. measurement.seconds)
      measurement.retained_words
      (float_of_int measurement.retained_words /. float_of_int benchmark_size)
      measurement.allocated_words
  in
  Printf.printf "%s\n" title;
  report "Patricia" patricia;
  report "Stdlib.Map" avl;
  report "Hashtbl" hash

let report_operation name patricia avl hash operations =
  let report implementation measurement =
    if measurement.operation_samples = 1 then
      Printf.printf
        "  %-9s %-17s %7.3f ms  %8.1f ns/op  allocated %10.0f words\n"
        implementation name
        (1000. *. measurement.operation_seconds)
        (1e9 *. measurement.operation_seconds /. float_of_int operations)
        measurement.operation_allocated_words
    else
      Printf.printf
        "  %-9s %-17s median %7.3f ms  %8.1f ns/op  range %7.3f-%7.3f us  allocated %10.0f words (%dx%d)\n"
        implementation name
        (1000. *. measurement.operation_seconds)
        (1e9 *. measurement.operation_seconds /. float_of_int operations)
        (1e6 *. measurement.operation_min_seconds)
        (1e6 *. measurement.operation_max_seconds)
        measurement.operation_allocated_words
        measurement.operation_samples measurement.operation_batch
  in
  report "Patricia" patricia;
  report "Stdlib.Map" avl;
  report "Hashtbl" hash

(* The equality-aware candidate is deliberately benchmark-local.  Exporting it
   would add a new operation and an equality-reflection premise to the current
   proof-oriented API, so first establish whether its root-reuse benefit is
   worth that expansion. *)
let report_persistent_candidate name patricia avl operations =
  let report implementation measurement =
    Printf.printf
      "  %-9s %-17s %7.3f ms  %8.1f ns/op  allocated %10.0f words\n"
      implementation name
      (1000. *. measurement.operation_seconds)
      (1e9 *. measurement.operation_seconds /. float_of_int operations)
      measurement.operation_allocated_words
  in
  report "Patricia" patricia;
  report "Stdlib.Map" avl

let build_patricia_int keys =
  Array.fold_left
    (fun map key -> Patricia.set (patricia_key key) key map)
    Patricia.empty keys

let build_avl_int keys =
  Array.fold_left (fun map key -> Int_avl.add key key map) Int_avl.empty keys

let build_hash_int keys =
  let map = Int_hash.create benchmark_size in
  Array.iter (fun key -> Int_hash.replace map key key) keys;
  map

let build_patricia_string keys =
  Array.fold_left
    (fun map key -> StringPatricia.set key (Stdlib.String.length key) map)
    StringPatricia.empty keys

let build_avl_string keys =
  Array.fold_left
    (fun map key -> String_avl.add key (Stdlib.String.length key) map)
    String_avl.empty keys

let build_hash_string keys =
  let map = String_hash.create benchmark_size in
  Array.iter
    (fun key -> String_hash.replace map key (Stdlib.String.length key)) keys;
  map

let patricia_set_if_changed equal key value map =
  match Patricia.get key map with
  | Some current when equal current value -> map
  | _ -> Patricia.set key value map

let string_patricia_set_if_changed equal key value map =
  match StringPatricia.get key map with
  | Some current when equal current value -> map
  | _ -> StringPatricia.set key value map

let int_avl_set_if_changed equal key value map =
  match Int_avl.find_opt key map with
  | Some current when equal current value -> map
  | _ -> Int_avl.add key value map

let string_avl_set_if_changed equal key value map =
  match String_avl.find_opt key map with
  | Some current when equal current value -> map
  | _ -> String_avl.add key value map

let permuted_keys keys =
  let result = Array.copy keys in
  let state = Random.State.make [| 0x50_4154 |] in
  for index = Array.length result - 1 downto 1 do
    let other = Random.State.int state (index + 1) in
    let saved = result.(index) in
    result.(index) <- result.(other);
    result.(other) <- saved
  done;
  result

let patricia_cardinal map =
  Patricia.fold (fun count _ _ -> count + 1) map 0

let string_patricia_cardinal map =
  StringPatricia.fold (fun count _ _ -> count + 1) map 0

(* [List.map] in the supported OCaml version uses one stack frame per input
   element.  Benchmark validation processes lists as large as the configured
   map cardinality, so keep this conversion stack-safe. *)
let int_bindings_of_patricia bindings =
  let rec loop reversed = function
    | [] -> List.rev reversed
    | (key, value) :: rest ->
        loop ((Patricia.Key.to_int key, value) :: reversed) rest
  in
  loop [] bindings

let check_int_equivalent keys patricia avl =
  Array.iter
    (fun key ->
       if Patricia.get (patricia_key key) patricia <> Int_avl.find_opt key avl then
         failwith "integer Patricia result differs from Stdlib.Map")
    keys

let check_int_hash_equivalent keys hash avl =
  Array.iter
    (fun key ->
       if Int_hash.find_opt hash key <> Int_avl.find_opt key avl then
         failwith "integer hash-table result differs from Stdlib.Map")
    keys

let check_string_equivalent keys patricia avl =
  Array.iter
    (fun key ->
       if StringPatricia.get key patricia <> String_avl.find_opt key avl then
         failwith "string Patricia result differs from Stdlib.Map")
    keys

let check_string_hash_equivalent keys hash avl =
  Array.iter
    (fun key ->
       if String_hash.find_opt hash key <> String_avl.find_opt key avl then
         failwith "string hash-table result differs from Stdlib.Map")
    keys

let generic_combine_values left right =
  match left, right with
  | Some _, Some _ -> None
  | Some value, None -> Some (value + 1)
  | None, Some value -> Some (-value)
  | None, None -> None

let patricia_combiner : (int, int, int) Patricia.combiner = {
  Patricia.left_only = (fun value -> Some (value + 1));
  right_only = (fun value -> Some (-value));
  both = (fun _ _ -> None);
}

let string_patricia_combiner : (int, int, int) StringPatricia.combiner = {
  StringPatricia.left_only = (fun value -> Some (value + 1));
  right_only = (fun value -> Some (-value));
  both = (fun _ _ -> None);
}

let check_int_bindings context patricia avl =
  let bindings = int_bindings_of_patricia (Patricia.elements patricia) in
  if bindings <> Int_avl.bindings avl then
    failwith (context ^ " differs from Stdlib.Map.merge")

let check_int_hash_bindings context hash avl =
  let bindings = Int_hash.fold (fun key value result -> (key, value) :: result) hash [] in
  if List.sort Stdlib.compare bindings <> Int_avl.bindings avl then
    failwith (context ^ " hash-table result differs from Stdlib.Map.merge")

let check_string_bindings context patricia avl =
  if List.sort Stdlib.compare (StringPatricia.elements patricia)
     <> String_avl.bindings avl then
    failwith (context ^ " differs from Stdlib.Map.merge")

let check_string_hash_bindings context hash avl =
  let bindings =
    String_hash.fold (fun key value result -> (key, value) :: result) hash []
  in
  if List.sort Stdlib.compare bindings <> String_avl.bindings avl then
    failwith (context ^ " hash-table result differs from Stdlib.Map.merge")

let set_hash_binding replace remove table key = function
  | Some value -> replace table key value
  | None -> remove table key

let combine_int_hash first second =
  let result = Int_hash.create (Int_hash.length first + Int_hash.length second) in
  Int_hash.iter
    (fun key value ->
       set_hash_binding Int_hash.replace Int_hash.remove result key
         (generic_combine_values (Some value) None))
    first;
  Int_hash.iter
    (fun key value ->
       set_hash_binding Int_hash.replace Int_hash.remove result key
         (generic_combine_values (Int_hash.find_opt first key) (Some value)))
    second;
  result

let combine_string_hash first second =
  let result =
    String_hash.create (String_hash.length first + String_hash.length second)
  in
  String_hash.iter
    (fun key value ->
       set_hash_binding String_hash.replace String_hash.remove result key
         (generic_combine_values (Some value) None))
    first;
  String_hash.iter
    (fun key value ->
       set_hash_binding String_hash.replace String_hash.remove result key
         (generic_combine_values (String_hash.find_opt first key) (Some value)))
    second;
  result

let union_left_int_hash first second =
  let result = Int_hash.copy first in
  Int_hash.iter
    (fun key value ->
       if not (Int_hash.mem result key) then Int_hash.replace result key value)
    second;
  result

let union_left_string_hash first second =
  let result = String_hash.copy first in
  String_hash.iter
    (fun key value ->
       if not (String_hash.mem result key) then String_hash.replace result key value)
    second;
  result

let time_int_lookups keys patricia avl hash =
  let patricia_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match Patricia.get (patricia_key key) patricia with
           | Some value when value = key -> checksum := !checksum lxor value
           | _ -> failwith "integer Patricia lookup failed")
        keys
    done;
    !checksum
  in
  let avl_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match Int_avl.find_opt key avl with
           | Some value when value = key -> checksum := !checksum lxor value
           | _ -> failwith "integer Stdlib.Map lookup failed")
        keys
    done;
    !checksum
  in
  let hash_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match Int_hash.find_opt hash key with
           | Some value when value = key -> checksum := !checksum lxor value
           | _ -> failwith "integer hash-table lookup failed")
        keys
    done;
    !checksum
  in
  let patricia_result, patricia_measurement = measure_operation patricia_lookup in
  let avl_result, avl_measurement = measure_operation avl_lookup in
  let hash_result, hash_measurement = measure_operation hash_lookup in
  if patricia_result <> avl_result || patricia_result <> hash_result then
    failwith "integer lookup checksums differ";
  report_operation "lookup" patricia_measurement avl_measurement hash_measurement
    (benchmark_size * lookup_repetitions)

let time_string_lookups keys patricia avl hash =
  let patricia_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match StringPatricia.get key patricia with
           | Some actual when actual = Stdlib.String.length key -> checksum := !checksum lxor actual
           | _ -> failwith "string Patricia lookup failed")
        keys
    done;
    !checksum
  in
  let avl_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match String_avl.find_opt key avl with
           | Some actual when actual = Stdlib.String.length key -> checksum := !checksum lxor actual
           | _ -> failwith "string Stdlib.Map lookup failed")
        keys
    done;
    !checksum
  in
  let hash_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match String_hash.find_opt hash key with
           | Some actual when actual = Stdlib.String.length key ->
               checksum := !checksum lxor actual
           | _ -> failwith "string hash-table lookup failed")
        keys
    done;
    !checksum
  in
  let patricia_result, patricia_measurement = measure_operation patricia_lookup in
  let avl_result, avl_measurement = measure_operation avl_lookup in
  let hash_result, hash_measurement = measure_operation hash_lookup in
  if patricia_result <> avl_result || patricia_result <> hash_result then
    failwith "string lookup checksums differ";
  report_operation "lookup" patricia_measurement avl_measurement hash_measurement
    (benchmark_size * lookup_repetitions)

let time_int_membership present absent patricia avl hash =
  let run mem map =
    let present_count = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           if mem key map then incr present_count
           else failwith "integer membership missed a present key")
        present;
      Array.iter
        (fun key ->
           if mem key map then failwith "integer membership found an absent key")
        absent
    done;
    !present_count
  in
  let patricia_result, patricia_measurement =
    measure_operation
      (fun () ->
         run
           (fun key map -> Patricia.mem (patricia_key key) map)
           patricia)
  in
  let avl_result, avl_measurement =
    measure_operation (fun () -> run Int_avl.mem avl)
  in
  let hash_result, hash_measurement =
    measure_operation (fun () -> run (fun key map -> Int_hash.mem map key) hash)
  in
  if patricia_result <> avl_result || patricia_result <> hash_result then
    failwith "integer membership counts differ";
  report_operation "membership" patricia_measurement avl_measurement hash_measurement
    (2 * benchmark_size * lookup_repetitions)

let time_string_membership present absent patricia avl hash =
  let run mem map =
    let present_count = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           if mem key map then incr present_count
           else failwith "string membership missed a present key")
        present;
      Array.iter
        (fun key ->
           if mem key map then failwith "string membership found an absent key")
        absent
    done;
    !present_count
  in
  let patricia_result, patricia_measurement =
    measure_operation (fun () -> run StringPatricia.mem patricia)
  in
  let avl_result, avl_measurement =
    measure_operation (fun () -> run String_avl.mem avl)
  in
  let hash_result, hash_measurement =
    measure_operation (fun () -> run (fun key map -> String_hash.mem map key) hash)
  in
  if patricia_result <> avl_result || patricia_result <> hash_result then
    failwith "string membership counts differ";
  report_operation "membership" patricia_measurement avl_measurement hash_measurement
    (2 * benchmark_size * lookup_repetitions)

let time_int_elements patricia avl hash =
  let patricia_bindings, patricia_measurement =
    measure_operation (fun () -> Patricia.elements patricia)
  in
  let avl_bindings, avl_measurement =
    measure_operation (fun () -> Int_avl.bindings avl)
  in
  let hash_bindings, hash_measurement =
    measure_operation (fun () ->
        Int_hash.fold (fun key value result -> (key, value) :: result) hash [])
  in
  let patricia_bindings = int_bindings_of_patricia patricia_bindings in
  if patricia_bindings <> avl_bindings then
    failwith "integer elements differ from Stdlib.Map bindings";
  if List.sort Stdlib.compare hash_bindings <> avl_bindings then
    failwith "integer hash-table elements differ from Stdlib.Map bindings";
  report_operation "elements" patricia_measurement avl_measurement hash_measurement
    benchmark_size

let time_string_elements patricia avl hash =
  let patricia_bindings, patricia_measurement =
    measure_operation (fun () -> StringPatricia.elements patricia)
  in
  let avl_bindings, avl_measurement =
    measure_operation (fun () -> String_avl.bindings avl)
  in
  let hash_bindings, hash_measurement =
    measure_operation (fun () ->
        String_hash.fold (fun key value result -> (key, value) :: result) hash [])
  in
  if List.sort Stdlib.compare patricia_bindings <> avl_bindings then
    failwith "string elements differ from Stdlib.Map bindings";
  if List.sort Stdlib.compare hash_bindings <> avl_bindings then
    failwith "string hash-table elements differ from Stdlib.Map bindings";
  report_operation "elements" patricia_measurement avl_measurement hash_measurement
    benchmark_size

let time_int_generic_combine keys patricia avl hash =
  let key = keys.(benchmark_size / 2) in
  let patricia_leaf = Patricia.singleton (patricia_key key) (-key) in
  let avl_leaf = Int_avl.singleton key (-key) in
  let hash_leaf = Int_hash.create 1 in
  Int_hash.replace hash_leaf key (-key);
  let avl_combine = Int_avl.merge (fun _ -> generic_combine_values) in
  let patricia_left, patricia_left_measurement =
    measure_operation (fun () ->
        Patricia.combine patricia_combiner patricia_leaf patricia)
  in
  let avl_left, avl_left_measurement =
    measure_operation (fun () -> avl_combine avl_leaf avl)
  in
  let hash_left, hash_left_measurement =
    measure_operation (fun () -> combine_int_hash hash_leaf hash)
  in
  check_int_bindings "integer leaf/tree combine" patricia_left avl_left;
  check_int_hash_bindings "integer leaf/tree combine" hash_left avl_left;
  report_operation "combine leaf/tree" patricia_left_measurement
    avl_left_measurement hash_left_measurement 1;
  let patricia_right, patricia_right_measurement =
    measure_operation (fun () ->
        Patricia.combine patricia_combiner patricia patricia_leaf)
  in
  let avl_right, avl_right_measurement =
    measure_operation (fun () -> avl_combine avl avl_leaf)
  in
  let hash_right, hash_right_measurement =
    measure_operation (fun () -> combine_int_hash hash hash_leaf)
  in
  check_int_bindings "integer tree/leaf combine" patricia_right avl_right;
  check_int_hash_bindings "integer tree/leaf combine" hash_right avl_right;
  report_operation "combine tree/leaf" patricia_right_measurement
    avl_right_measurement hash_right_measurement 1

let time_string_generic_combine keys patricia avl hash =
  let key = keys.(benchmark_size / 2) in
  let value = -(Stdlib.String.length key) in
  let patricia_leaf = StringPatricia.singleton key value in
  let avl_leaf = String_avl.singleton key value in
  let hash_leaf = String_hash.create 1 in
  String_hash.replace hash_leaf key value;
  let avl_combine = String_avl.merge (fun _ -> generic_combine_values) in
  let patricia_left, patricia_left_measurement =
    measure_operation (fun () ->
        StringPatricia.combine string_patricia_combiner patricia_leaf patricia)
  in
  let avl_left, avl_left_measurement =
    measure_operation (fun () -> avl_combine avl_leaf avl)
  in
  let hash_left, hash_left_measurement =
    measure_operation (fun () -> combine_string_hash hash_leaf hash)
  in
  check_string_bindings "string leaf/tree combine" patricia_left avl_left;
  check_string_hash_bindings "string leaf/tree combine" hash_left avl_left;
  report_operation "combine leaf/tree" patricia_left_measurement
    avl_left_measurement hash_left_measurement 1;
  let patricia_right, patricia_right_measurement =
    measure_operation (fun () ->
        StringPatricia.combine string_patricia_combiner patricia patricia_leaf)
  in
  let avl_right, avl_right_measurement =
    measure_operation (fun () -> avl_combine avl avl_leaf)
  in
  let hash_right, hash_right_measurement =
    measure_operation (fun () -> combine_string_hash hash hash_leaf)
  in
  check_string_bindings "string tree/leaf combine" patricia_right avl_right;
  check_string_hash_bindings "string tree/leaf combine" hash_right avl_right;
  report_operation "combine tree/leaf" patricia_right_measurement
    avl_right_measurement hash_right_measurement 1

let time_int_mutations keys fresh_keys patricia avl hash =
  let all_keys = Array.append keys fresh_keys in
  let patricia_added, patricia_add =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Patricia.set (patricia_key key) key map)
          patricia fresh_keys)
  in
  let avl_added, avl_add =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Int_avl.add key key map)
          avl fresh_keys)
  in
  let hash_added, hash_add =
    measure_operation (fun () ->
        let result = Int_hash.copy hash in
        Array.iter (fun key -> Int_hash.replace result key key) fresh_keys;
        result)
  in
  if patricia_cardinal patricia_added <> 2 * benchmark_size
     || Int_avl.cardinal avl_added <> 2 * benchmark_size
     || Int_hash.length hash_added <> 2 * benchmark_size then
    failwith "integer additions produced the wrong cardinality";
  check_int_equivalent all_keys patricia_added avl_added;
  check_int_hash_equivalent all_keys hash_added avl_added;
  report_operation "add keys" patricia_add avl_add hash_add benchmark_size;
  let patricia_updated, patricia_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Patricia.set (patricia_key key) (-key) map)
          patricia keys)
  in
  let avl_updated, avl_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Int_avl.add key (-key) map)
          avl keys)
  in
  let hash_updated, hash_update =
    measure_operation (fun () ->
        let result = Int_hash.copy hash in
        Array.iter (fun key -> Int_hash.replace result key (-key)) keys;
        result)
  in
  check_int_equivalent keys patricia_updated avl_updated;
  check_int_hash_equivalent keys hash_updated avl_updated;
  Array.iter
    (fun key ->
       if Patricia.get (patricia_key key) patricia_updated <> Some (-key)
          || Int_avl.find_opt key avl_updated <> Some (-key)
          || Int_hash.find_opt hash_updated key <> Some (-key) then
         failwith "integer update did not replace the binding")
    keys;
  report_operation "update keys" patricia_update avl_update hash_update benchmark_size;
  let patricia_same, patricia_same_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key ->
             patricia_set_if_changed Int.equal (patricia_key key) key map)
          patricia keys)
  in
  let avl_same, avl_same_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> int_avl_set_if_changed Int.equal key key map)
          avl keys)
  in
  if patricia_same != patricia then
    failwith "unchanged integer equality-aware set did not preserve Patricia root";
  if avl_same != avl then
    failwith "unchanged integer equality-aware set did not preserve AVL root";
  check_int_equivalent keys patricia_same avl_same;
  report_persistent_candidate "set unchanged" patricia_same_update avl_same_update
    benchmark_size;
  let absent_keys = Array.make benchmark_size fresh_keys.(0) in
  let patricia_unchanged, patricia_remove_absent =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Patricia.remove (patricia_key key) map)
          patricia absent_keys)
  in
  let avl_unchanged, avl_remove_absent =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Int_avl.remove key map)
          avl absent_keys)
  in
  let hash_unchanged, hash_remove_absent =
    measure_operation (fun () ->
        let result = Int_hash.copy hash in
        Array.iter (fun key -> Int_hash.remove result key) absent_keys;
        result)
  in
  if patricia_unchanged != patricia then
    failwith "absent integer removal did not preserve Patricia root identity";
  check_int_equivalent keys patricia_unchanged avl_unchanged;
  check_int_hash_equivalent keys hash_unchanged avl_unchanged;
  report_operation "remove absent" patricia_remove_absent avl_remove_absent
    hash_remove_absent benchmark_size;
  let patricia_removed, patricia_remove =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> Patricia.remove (patricia_key key) map)
          patricia keys)
  in
  let avl_removed, avl_remove =
    measure_operation (fun () ->
        Array.fold_left (fun map key -> Int_avl.remove key map) avl keys)
  in
  let hash_removed, hash_remove =
    measure_operation (fun () ->
        let result = Int_hash.copy hash in
        Array.iter (Int_hash.remove result) keys;
        result)
  in
  if patricia_cardinal patricia_removed <> 0 || Int_avl.cardinal avl_removed <> 0
     || Int_hash.length hash_removed <> 0 then
    failwith "integer removals produced a non-empty map";
  Array.iter
    (fun key ->
       if Patricia.get (patricia_key key) patricia_removed <> None
          || Int_avl.find_opt key avl_removed <> None
          || Int_hash.find_opt hash_removed key <> None then
         failwith "integer removal did not delete the binding")
    keys;
  report_operation "remove keys" patricia_remove avl_remove hash_remove benchmark_size

let time_string_mutations keys fresh_keys patricia avl hash =
  let all_keys = Array.append keys fresh_keys in
  let patricia_added, patricia_add =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> StringPatricia.set key (Stdlib.String.length key) map)
          patricia fresh_keys)
  in
  let avl_added, avl_add =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> String_avl.add key (Stdlib.String.length key) map)
          avl fresh_keys)
  in
  let hash_added, hash_add =
    measure_operation (fun () ->
        let result = String_hash.copy hash in
        Array.iter
          (fun key -> String_hash.replace result key (Stdlib.String.length key))
          fresh_keys;
        result)
  in
  if string_patricia_cardinal patricia_added <> 2 * benchmark_size
     || String_avl.cardinal avl_added <> 2 * benchmark_size
     || String_hash.length hash_added <> 2 * benchmark_size then
    failwith "string additions produced the wrong cardinality";
  check_string_equivalent all_keys patricia_added avl_added;
  check_string_hash_equivalent all_keys hash_added avl_added;
  report_operation "add keys" patricia_add avl_add hash_add benchmark_size;
  let updated_value key = -Stdlib.String.length key in
  let patricia_updated, patricia_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> StringPatricia.set key (updated_value key) map)
          patricia keys)
  in
  let avl_updated, avl_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> String_avl.add key (updated_value key) map)
          avl keys)
  in
  let hash_updated, hash_update =
    measure_operation (fun () ->
        let result = String_hash.copy hash in
        Array.iter
          (fun key -> String_hash.replace result key (updated_value key)) keys;
        result)
  in
  check_string_equivalent keys patricia_updated avl_updated;
  check_string_hash_equivalent keys hash_updated avl_updated;
  Array.iter
    (fun key ->
       if StringPatricia.get key patricia_updated <> Some (updated_value key)
          || String_avl.find_opt key avl_updated <> Some (updated_value key)
          || String_hash.find_opt hash_updated key <> Some (updated_value key) then
         failwith "string update did not replace the binding")
    keys;
  report_operation "update keys" patricia_update avl_update hash_update benchmark_size;
  let patricia_same, patricia_same_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key ->
             string_patricia_set_if_changed Int.equal key
               (Stdlib.String.length key) map)
          patricia keys)
  in
  let avl_same, avl_same_update =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key ->
             string_avl_set_if_changed Int.equal key (Stdlib.String.length key) map)
          avl keys)
  in
  if patricia_same != patricia then
    failwith "unchanged string equality-aware set did not preserve Patricia root";
  if avl_same != avl then
    failwith "unchanged string equality-aware set did not preserve AVL root";
  check_string_equivalent keys patricia_same avl_same;
  report_persistent_candidate "set unchanged" patricia_same_update avl_same_update
    benchmark_size;
  let absent_keys = Array.make benchmark_size fresh_keys.(0) in
  let patricia_unchanged, patricia_remove_absent =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> StringPatricia.remove key map)
          patricia absent_keys)
  in
  let avl_unchanged, avl_remove_absent =
    measure_operation (fun () ->
        Array.fold_left
          (fun map key -> String_avl.remove key map)
          avl absent_keys)
  in
  let hash_unchanged, hash_remove_absent =
    measure_operation (fun () ->
        let result = String_hash.copy hash in
        Array.iter (fun key -> String_hash.remove result key) absent_keys;
        result)
  in
  if patricia_unchanged != patricia then
    failwith "absent string removal did not preserve Patricia root identity";
  check_string_equivalent keys patricia_unchanged avl_unchanged;
  check_string_hash_equivalent keys hash_unchanged avl_unchanged;
  report_operation "remove absent" patricia_remove_absent avl_remove_absent
    hash_remove_absent benchmark_size;
  let patricia_removed, patricia_remove =
    measure_operation (fun () ->
        Array.fold_left (fun map key -> StringPatricia.remove key map) patricia keys)
  in
  let avl_removed, avl_remove =
    measure_operation (fun () ->
        Array.fold_left (fun map key -> String_avl.remove key map) avl keys)
  in
  let hash_removed, hash_remove =
    measure_operation (fun () ->
        let result = String_hash.copy hash in
        Array.iter (String_hash.remove result) keys;
        result)
  in
  if string_patricia_cardinal patricia_removed <> 0
     || String_avl.cardinal avl_removed <> 0
     || String_hash.length hash_removed <> 0 then
    failwith "string removals produced a non-empty map";
  Array.iter
    (fun key ->
       if StringPatricia.get key patricia_removed <> None
          || String_avl.find_opt key avl_removed <> None
          || String_hash.find_opt hash_removed key <> None then
         failwith "string removal did not delete the binding")
    keys;
  report_operation "remove keys" patricia_remove avl_remove hash_remove benchmark_size

(* A deterministic mixed trace covers successful and unsuccessful lookup and
   removal, replacement of an existing binding, and insertion of a fresh one.
   Every implementation executes the same trace and its final map is checked
   against the AVL result. *)
let time_int_mixed_operations keys fresh_keys patricia avl hash =
  let run_patricia () =
    let current = ref patricia and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match Patricia.get (patricia_key key) !current with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "integer mixed Patricia lookup missed")
         | 1 ->
             if Patricia.get (patricia_key fresh) !current <> None then
               failwith "integer mixed Patricia lookup found fresh key"
         | 2 -> current := Patricia.set (patricia_key key) (-key) !current
         | 3 -> current := Patricia.remove (patricia_key fresh) !current
         | 4 -> current := Patricia.remove (patricia_key key) !current
         | _ -> current := Patricia.set (patricia_key fresh) fresh !current)
      keys;
    !current, !checksum
  in
  let run_avl () =
    let current = ref avl and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match Int_avl.find_opt key !current with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "integer mixed AVL lookup missed")
         | 1 ->
             if Int_avl.find_opt fresh !current <> None then
               failwith "integer mixed AVL lookup found fresh key"
         | 2 -> current := Int_avl.add key (-key) !current
         | 3 -> current := Int_avl.remove fresh !current
         | 4 -> current := Int_avl.remove key !current
         | _ -> current := Int_avl.add fresh fresh !current)
      keys;
    !current, !checksum
  in
  let run_hash () =
    let current = Int_hash.copy hash and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match Int_hash.find_opt current key with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "integer mixed hash lookup missed")
         | 1 ->
             if Int_hash.find_opt current fresh <> None then
               failwith "integer mixed hash lookup found fresh key"
         | 2 -> Int_hash.replace current key (-key)
         | 3 -> Int_hash.remove current fresh
         | 4 -> Int_hash.remove current key
         | _ -> Int_hash.replace current fresh fresh)
      keys;
    current, !checksum
  in
  let (patricia_result, patricia_checksum), patricia_measurement =
    measure_operation run_patricia
  in
  let (avl_result, avl_checksum), avl_measurement = measure_operation run_avl in
  let (hash_result, hash_checksum), hash_measurement = measure_operation run_hash in
  if patricia_checksum <> avl_checksum || patricia_checksum <> hash_checksum then
    failwith "integer mixed-operation checksums differ";
  check_int_equivalent (Array.append keys fresh_keys) patricia_result avl_result;
  check_int_hash_equivalent (Array.append keys fresh_keys) hash_result avl_result;
  report_operation "mixed operations" patricia_measurement avl_measurement
    hash_measurement benchmark_size

let time_string_mixed_operations keys fresh_keys patricia avl hash =
  let run_patricia () =
    let current = ref patricia and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match StringPatricia.get key !current with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "string mixed Patricia lookup missed")
         | 1 ->
             if StringPatricia.get fresh !current <> None then
               failwith "string mixed Patricia lookup found fresh key"
         | 2 ->
             current := StringPatricia.set key (-Stdlib.String.length key) !current
         | 3 -> current := StringPatricia.remove fresh !current
         | 4 -> current := StringPatricia.remove key !current
         | _ ->
             current := StringPatricia.set fresh (Stdlib.String.length fresh) !current)
      keys;
    !current, !checksum
  in
  let run_avl () =
    let current = ref avl and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match String_avl.find_opt key !current with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "string mixed AVL lookup missed")
         | 1 ->
             if String_avl.find_opt fresh !current <> None then
               failwith "string mixed AVL lookup found fresh key"
         | 2 -> current := String_avl.add key (-Stdlib.String.length key) !current
         | 3 -> current := String_avl.remove fresh !current
         | 4 -> current := String_avl.remove key !current
         | _ ->
             current := String_avl.add fresh (Stdlib.String.length fresh) !current)
      keys;
    !current, !checksum
  in
  let run_hash () =
    let current = String_hash.copy hash and checksum = ref 0 in
    Array.iteri
      (fun index key ->
         let fresh = fresh_keys.(index) in
         match index mod 6 with
         | 0 ->
             (match String_hash.find_opt current key with
              | Some value -> checksum := !checksum lxor value
              | None -> failwith "string mixed hash lookup missed")
         | 1 ->
             if String_hash.find_opt current fresh <> None then
               failwith "string mixed hash lookup found fresh key"
         | 2 -> String_hash.replace current key (-Stdlib.String.length key)
         | 3 -> String_hash.remove current fresh
         | 4 -> String_hash.remove current key
         | _ -> String_hash.replace current fresh (Stdlib.String.length fresh))
      keys;
    current, !checksum
  in
  let (patricia_result, patricia_checksum), patricia_measurement =
    measure_operation run_patricia
  in
  let (avl_result, avl_checksum), avl_measurement = measure_operation run_avl in
  let (hash_result, hash_checksum), hash_measurement = measure_operation run_hash in
  if patricia_checksum <> avl_checksum || patricia_checksum <> hash_checksum then
    failwith "string mixed-operation checksums differ";
  check_string_equivalent (Array.append keys fresh_keys) patricia_result avl_result;
  check_string_hash_equivalent (Array.append keys fresh_keys) hash_result avl_result;
  report_operation "mixed operations" patricia_measurement avl_measurement
    hash_measurement benchmark_size

let time_int_union name keys expected_cardinal first_patricia first_avl first_hash
    second_patricia second_avl second_hash =
  let patricia_result, patricia_measurement =
    measure_short_operation (fun () ->
        Patricia.union_left first_patricia second_patricia)
  in
  let avl_result, avl_measurement =
    measure_comparison_operation (fun () ->
        Int_avl.union (fun _ left _ -> Some left) first_avl second_avl)
  in
  let hash_result, hash_measurement =
    measure_comparison_operation (fun () -> union_left_int_hash first_hash second_hash)
  in
  if patricia_cardinal patricia_result <> expected_cardinal
     || Int_avl.cardinal avl_result <> expected_cardinal
     || Int_hash.length hash_result <> expected_cardinal then
    failwith ("integer " ^ name ^ " produced the wrong cardinality");
  check_int_equivalent keys patricia_result avl_result;
  check_int_hash_equivalent keys hash_result avl_result;
  report_operation name patricia_measurement avl_measurement hash_measurement 1

let time_string_union ?(right_bias = false) name keys expected_cardinal first_patricia first_avl first_hash
    second_patricia second_avl second_hash =
  let patricia_result, patricia_measurement =
    measure_short_operation (fun () ->
        (if right_bias then StringPatricia.union_right else StringPatricia.union_left)
          first_patricia second_patricia)
  in
  let avl_result, avl_measurement =
    measure_comparison_operation (fun () ->
        String_avl.union (fun _ left right -> Some (if right_bias then right else left))
          first_avl second_avl)
  in
  let hash_result, hash_measurement =
    measure_comparison_operation (fun () ->
      if right_bias then union_left_string_hash second_hash first_hash
      else union_left_string_hash first_hash second_hash)
  in
  if string_patricia_cardinal patricia_result <> expected_cardinal
     || String_avl.cardinal avl_result <> expected_cardinal
     || String_hash.length hash_result <> expected_cardinal then
    failwith ("string " ^ name ^ " produced the wrong cardinality");
  check_string_equivalent keys patricia_result avl_result;
  check_string_hash_equivalent keys hash_result avl_result;
  report_operation name patricia_measurement avl_measurement hash_measurement 1

let benchmark_int () =
  let left_keys = Array.init benchmark_size (fun index -> index + 1) in
  let disjoint_keys = Array.init benchmark_size (fun index -> benchmark_size + index + 1) in
  let overlap_keys =
    Array.init benchmark_size (fun index -> (benchmark_size / 2) + index + 1)
  in
  let patricia_left, patricia_build =
    measure_build patricia_cardinal (fun () -> build_patricia_int left_keys)
  in
  let avl_left, avl_build =
    measure_build Int_avl.cardinal (fun () -> build_avl_int left_keys)
  in
  let hash_left, hash_build =
    measure_build Int_hash.length (fun () -> build_hash_int left_keys)
  in
  check_int_equivalent left_keys patricia_left avl_left;
  check_int_hash_equivalent left_keys hash_left avl_left;
  report_build "Integer keys" patricia_build avl_build hash_build;
  let random_keys = permuted_keys left_keys in
  let random_patricia, random_patricia_build =
    measure_build patricia_cardinal (fun () -> build_patricia_int random_keys)
  in
  let random_avl, random_avl_build =
    measure_build Int_avl.cardinal (fun () -> build_avl_int random_keys)
  in
  let random_hash, random_hash_build =
    measure_build Int_hash.length (fun () -> build_hash_int random_keys)
  in
  check_int_equivalent left_keys random_patricia random_avl;
  check_int_hash_equivalent left_keys random_hash random_avl;
  report_build ~operation:"random build" "Integer keys (random insertion order)"
    random_patricia_build random_avl_build random_hash_build;
  time_int_lookups left_keys patricia_left avl_left hash_left;
  time_int_membership left_keys disjoint_keys patricia_left avl_left hash_left;
  time_int_elements patricia_left avl_left hash_left;
  time_int_generic_combine left_keys patricia_left avl_left hash_left;
  time_int_mutations left_keys disjoint_keys patricia_left avl_left hash_left;
  time_int_mixed_operations left_keys disjoint_keys patricia_left avl_left hash_left;
  let patricia_disjoint = build_patricia_int disjoint_keys in
  let avl_disjoint = build_avl_int disjoint_keys in
  let hash_disjoint = build_hash_int disjoint_keys in
  let patricia_merged, patricia_merge =
    measure_short_operation (fun () -> Patricia.union_left patricia_left patricia_disjoint)
  in
  let avl_merged, avl_merge =
    measure_comparison_operation (fun () ->
        Int_avl.union (fun _ left _ -> Some left) avl_left avl_disjoint)
  in
  let hash_merged, hash_merge =
    measure_comparison_operation (fun () -> union_left_int_hash hash_left hash_disjoint)
  in
  let all_disjoint = Array.append left_keys disjoint_keys in
  if patricia_cardinal patricia_merged <> 2 * benchmark_size
     || Int_avl.cardinal avl_merged <> 2 * benchmark_size
     || Int_hash.length hash_merged <> 2 * benchmark_size then
    failwith "integer disjoint union produced the wrong cardinality";
  check_int_equivalent all_disjoint patricia_merged avl_merged;
  check_int_hash_equivalent all_disjoint hash_merged avl_merged;
  report_operation "disjoint union" patricia_merge avl_merge hash_merge 1;
  let patricia_overlap = build_patricia_int overlap_keys in
  let avl_overlap = build_avl_int overlap_keys in
  let hash_overlap = build_hash_int overlap_keys in
  let patricia_merged, patricia_merge =
    measure_short_operation (fun () -> Patricia.union_left patricia_left patricia_overlap)
  in
  let avl_merged, avl_merge =
    measure_comparison_operation (fun () ->
        Int_avl.union (fun _ left _ -> Some left) avl_left avl_overlap)
  in
  let hash_merged, hash_merge =
    measure_comparison_operation (fun () -> union_left_int_hash hash_left hash_overlap)
  in
  let all_overlap = Array.append left_keys overlap_keys in
  let expected_overlap = benchmark_size + (benchmark_size / 2) in
  if patricia_cardinal patricia_merged <> expected_overlap
     || Int_avl.cardinal avl_merged <> expected_overlap
     || Int_hash.length hash_merged <> expected_overlap then
    failwith "integer overlapping union produced the wrong cardinality";
  check_int_equivalent all_overlap patricia_merged avl_merged;
  check_int_hash_equivalent all_overlap hash_merged avl_merged;
  report_operation "overlap union" patricia_merge avl_merge hash_merge 1;
  let subset_keys = Array.sub left_keys 0 (max 1 (benchmark_size / 2)) in
  let subset_patricia = build_patricia_int subset_keys in
  let subset_avl = build_avl_int subset_keys in
  let subset_hash = build_hash_int subset_keys in
  time_int_union "subset union" left_keys benchmark_size patricia_left avl_left
    hash_left subset_patricia subset_avl subset_hash;
  time_int_union "equal union" left_keys benchmark_size patricia_left avl_left
    hash_left patricia_left avl_left hash_left;
  time_int_union "no-op union" left_keys benchmark_size patricia_left avl_left
    hash_left Patricia.empty Int_avl.empty (Int_hash.create 1);
  let sparse_existing = max 1 (benchmark_size / 8) in
  let sparse_keys =
    Array.init (2 * sparse_existing) (fun index ->
        if index mod 2 = 0 then 1 + ((index / 2) * 8)
        else benchmark_size + (index / 2) + 1)
  in
  let sparse_patricia = build_patricia_int sparse_keys in
  let sparse_avl = build_avl_int sparse_keys in
  let sparse_hash = build_hash_int sparse_keys in
  time_int_union "sparse-overlap union" (Array.append left_keys sparse_keys)
    (benchmark_size + sparse_existing) patricia_left avl_left hash_left
    sparse_patricia sparse_avl sparse_hash;
  print_newline ()

let short_string_key length index =
  let alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz" in
  let base = Stdlib.String.length alphabet in
  let key = Bytes.make length '0' in
  let remaining = ref index in
  for position = length - 1 downto 0 do
    Bytes.set key position (Stdlib.String.get alphabet (!remaining mod base));
    remaining := !remaining / base
  done;
  if !remaining <> 0 then invalid_arg "PATRICIA_BENCH_SIZE exceeds short-key space";
  Bytes.unsafe_to_string key

let short_string_keys length start =
  Array.init benchmark_size (fun index -> short_string_key length (start + index))

let variable_string_key maximum_length index =
  let rec select length width offset =
    if length > maximum_length then
      invalid_arg "PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH exceeds variable-key space"
    else if index < offset + width then short_string_key length (index - offset)
    else select (length + 1) (width * 62) (offset + width)
  in
  select 1 62 0

let benchmark_strings title make_key =
  let keys start = Array.init benchmark_size (fun index -> make_key (start + index)) in
  let left_keys = keys 0 in
  let disjoint_keys = keys benchmark_size in
  let overlap_keys = keys (benchmark_size / 2) in
  let patricia_left, patricia_build =
    measure_build string_patricia_cardinal (fun () -> build_patricia_string left_keys)
  in
  let avl_left, avl_build =
    measure_build String_avl.cardinal (fun () -> build_avl_string left_keys)
  in
  let hash_left, hash_build =
    measure_build String_hash.length (fun () -> build_hash_string left_keys)
  in
  check_string_equivalent left_keys patricia_left avl_left;
  check_string_hash_equivalent left_keys hash_left avl_left;
  report_build title patricia_build avl_build hash_build;
  let random_keys = permuted_keys left_keys in
  let random_patricia, random_patricia_build =
    measure_build string_patricia_cardinal (fun () -> build_patricia_string random_keys)
  in
  let random_avl, random_avl_build =
    measure_build String_avl.cardinal (fun () -> build_avl_string random_keys)
  in
  let random_hash, random_hash_build =
    measure_build String_hash.length (fun () -> build_hash_string random_keys)
  in
  check_string_equivalent left_keys random_patricia random_avl;
  check_string_hash_equivalent left_keys random_hash random_avl;
  report_build ~operation:"random build"
    (title ^ " (random insertion order)") random_patricia_build
    random_avl_build random_hash_build;
  time_string_lookups left_keys patricia_left avl_left hash_left;
  time_string_membership left_keys disjoint_keys patricia_left avl_left hash_left;
  time_string_elements patricia_left avl_left hash_left;
  time_string_generic_combine left_keys patricia_left avl_left hash_left;
  time_string_mutations left_keys disjoint_keys patricia_left avl_left hash_left;
  time_string_mixed_operations left_keys disjoint_keys patricia_left avl_left hash_left;
  let patricia_disjoint = build_patricia_string disjoint_keys in
  let avl_disjoint = build_avl_string disjoint_keys in
  let hash_disjoint = build_hash_string disjoint_keys in
  let patricia_merged, patricia_merge =
    measure_short_operation (fun () -> StringPatricia.union_left patricia_left patricia_disjoint)
  in
  let avl_merged, avl_merge =
    measure_comparison_operation (fun () ->
        String_avl.union (fun _ left _ -> Some left) avl_left avl_disjoint)
  in
  let hash_merged, hash_merge =
    measure_comparison_operation (fun () -> union_left_string_hash hash_left hash_disjoint)
  in
  let all_disjoint = Array.append left_keys disjoint_keys in
  if string_patricia_cardinal patricia_merged <> 2 * benchmark_size
     || String_avl.cardinal avl_merged <> 2 * benchmark_size
     || String_hash.length hash_merged <> 2 * benchmark_size then
    failwith "string disjoint union produced the wrong cardinality";
  check_string_equivalent all_disjoint patricia_merged avl_merged;
  check_string_hash_equivalent all_disjoint hash_merged avl_merged;
  report_operation "disjoint union" patricia_merge avl_merge hash_merge 1;
  let patricia_overlap = build_patricia_string overlap_keys in
  let avl_overlap = build_avl_string overlap_keys in
  let hash_overlap = build_hash_string overlap_keys in
  let patricia_merged, patricia_merge =
    measure_short_operation (fun () -> StringPatricia.union_left patricia_left patricia_overlap)
  in
  let avl_merged, avl_merge =
    measure_comparison_operation (fun () ->
        String_avl.union (fun _ left _ -> Some left) avl_left avl_overlap)
  in
  let hash_merged, hash_merge =
    measure_comparison_operation (fun () -> union_left_string_hash hash_left hash_overlap)
  in
  let all_overlap = Array.append left_keys overlap_keys in
  let expected_overlap = benchmark_size + (benchmark_size / 2) in
  if string_patricia_cardinal patricia_merged <> expected_overlap
     || String_avl.cardinal avl_merged <> expected_overlap
     || String_hash.length hash_merged <> expected_overlap then
    failwith "string overlapping union produced the wrong cardinality";
  check_string_equivalent all_overlap patricia_merged avl_merged;
  check_string_hash_equivalent all_overlap hash_merged avl_merged;
  report_operation "overlap union" patricia_merge avl_merge hash_merge 1;
  let subset_keys = Array.sub left_keys 0 (max 1 (benchmark_size / 2)) in
  let subset_patricia = build_patricia_string subset_keys in
  let subset_avl = build_avl_string subset_keys in
  let subset_hash = build_hash_string subset_keys in
  time_string_union "subset union" left_keys benchmark_size patricia_left avl_left
    hash_left subset_patricia subset_avl subset_hash;
  time_string_union "equal union" left_keys benchmark_size patricia_left avl_left
    hash_left patricia_left avl_left hash_left;
  let equal_keys = Array.map (fun key -> Bytes.to_string (Bytes.of_string key)) left_keys in
  let equal_patricia = build_patricia_string equal_keys in
  let equal_avl = build_avl_string equal_keys in
  let equal_hash = build_hash_string equal_keys in
  time_string_union "equal copies union" left_keys benchmark_size patricia_left avl_left
    hash_left equal_patricia equal_avl equal_hash;
  time_string_union ~right_bias:true "right disjoint union" all_disjoint (2 * benchmark_size)
    patricia_left avl_left hash_left patricia_disjoint avl_disjoint hash_disjoint;
  time_string_union ~right_bias:true "right overlap union" all_overlap expected_overlap
    patricia_left avl_left hash_left patricia_overlap avl_overlap hash_overlap;
  time_string_union ~right_bias:true "right subset union" left_keys benchmark_size
    patricia_left avl_left hash_left subset_patricia subset_avl subset_hash;
  time_string_union ~right_bias:true "right equal union" left_keys benchmark_size
    patricia_left avl_left hash_left patricia_left avl_left hash_left;
  time_string_union ~right_bias:true "right copies union" left_keys benchmark_size
    patricia_left avl_left hash_left equal_patricia equal_avl equal_hash;
  time_string_union "no-op union" left_keys benchmark_size patricia_left avl_left
    hash_left StringPatricia.empty String_avl.empty (String_hash.create 1);
  let sparse_existing = max 1 (benchmark_size / 8) in
  let sparse_keys =
    Array.init (2 * sparse_existing) (fun index ->
        if index mod 2 = 0 then make_key ((index / 2) * 8)
        else make_key (benchmark_size + (index / 2)))
  in
  let sparse_patricia = build_patricia_string sparse_keys in
  let sparse_avl = build_avl_string sparse_keys in
  let sparse_hash = build_hash_string sparse_keys in
  time_string_union "sparse-overlap union" (Array.append left_keys sparse_keys)
    (benchmark_size + sparse_existing) patricia_left avl_left hash_left
    sparse_patricia sparse_avl sparse_hash;
  print_newline ()

let long_prefix_string_key =
  let prefix = Stdlib.String.make long_prefix_length 'p' in
  fun index -> prefix ^ short_string_key 4 index

let () =
  Printf.printf
    "Patricia versus Stdlib.Map (AVL) and Stdlib.Hashtbl, %d bindings per input tree\n\n"
    benchmark_size;
  benchmark_int ();
  List.iter
    (fun length ->
       benchmark_strings (Printf.sprintf "String keys (%d characters)" length)
         (short_string_key length))
    string_key_lengths;
  benchmark_strings
    (Printf.sprintf "String keys (variable length, up to %d characters)"
       variable_string_max_length)
    (variable_string_key variable_string_max_length);
  benchmark_strings
    (Printf.sprintf "String keys (%d-byte common prefix)" long_prefix_length)
    long_prefix_string_key;
  print_endline "Patricia comparison benchmark: ok"
