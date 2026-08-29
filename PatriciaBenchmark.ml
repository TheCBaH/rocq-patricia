(* Comparative benchmark for the extracted Patricia trees and Stdlib.Map.

   Stdlib.Map is the standard-library balanced AVL implementation.  This is a
   measurement test: it checks that every measured map agrees with Stdlib.Map,
   while reporting time and GC-word measurements instead of imposing machine-
   dependent performance thresholds. *)

module Int_avl = Map.Make (struct
  type t = int
  let compare = Stdlib.compare
end)

module String_avl = Map.Make (struct
  type t = string
  let compare = Stdlib.String.compare
end)

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

type build_measurement = {
  seconds : float;
  allocated_words : float;
  retained_words : int;
}

type operation_measurement = {
  operation_seconds : float;
  operation_allocated_words : float;
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

let measure_operation operation =
  Gc.full_major ();
  let before_allocated = allocated_words () in
  let started = Unix.gettimeofday () in
  let result = operation () in
  let operation_seconds = Unix.gettimeofday () -. started in
  let operation_allocated_words = allocated_words () -. before_allocated in
  (result, { operation_seconds; operation_allocated_words })

let report_build title patricia avl =
  let report name measurement =
    Printf.printf
      "  %-9s build %7.3f ms  retained %8d words (%5.2f/binding)  allocated %10.0f words\n"
      name
      (1000. *. measurement.seconds)
      measurement.retained_words
      (float_of_int measurement.retained_words /. float_of_int benchmark_size)
      measurement.allocated_words
  in
  Printf.printf "%s\n" title;
  report "Patricia" patricia;
  report "Stdlib.Map" avl

let report_operation name patricia avl operations =
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
  Array.fold_left (fun map key -> Patricia.set key key map) Patricia.empty keys

let build_avl_int keys =
  Array.fold_left (fun map key -> Int_avl.add key key map) Int_avl.empty keys

let build_patricia_string keys =
  Array.fold_left
    (fun map key -> StringPatricia.set key (Stdlib.String.length key) map)
    StringPatricia.empty keys

let build_avl_string keys =
  Array.fold_left
    (fun map key -> String_avl.add key (Stdlib.String.length key) map)
    String_avl.empty keys

(* [size] in the extracted APIs counts constructors, not bindings. *)
let rec patricia_cardinal = function
  | Patricia.Empty -> 0
  | Patricia.Leaf _ -> 1
  | Patricia.Branch (_, _, left, right) ->
      patricia_cardinal left + patricia_cardinal right

let rec string_patricia_cardinal = function
  | StringPatricia.Empty -> 0
  | StringPatricia.Leaf _ -> 1
  | StringPatricia.Branch (_, _, left, right) ->
      string_patricia_cardinal left + string_patricia_cardinal right

let check_int_equivalent keys patricia avl =
  Array.iter
    (fun key ->
       if Patricia.get key patricia <> Int_avl.find_opt key avl then
         failwith "integer Patricia result differs from Stdlib.Map")
    keys

let check_string_equivalent keys patricia avl =
  Array.iter
    (fun key ->
       if StringPatricia.get key patricia <> String_avl.find_opt key avl then
         failwith "string Patricia result differs from Stdlib.Map")
    keys

let time_int_lookups keys patricia avl =
  let patricia_lookup () =
    let checksum = ref 0 in
    for _ = 1 to lookup_repetitions do
      Array.iter
        (fun key ->
           match Patricia.get key patricia with
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
  let patricia_result, patricia_measurement = measure_operation patricia_lookup in
  let avl_result, avl_measurement = measure_operation avl_lookup in
  if patricia_result <> avl_result then failwith "integer lookup checksums differ";
  report_operation "lookup" patricia_measurement avl_measurement
    (benchmark_size * lookup_repetitions)

let time_string_lookups keys patricia avl =
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
  let patricia_result, patricia_measurement = measure_operation patricia_lookup in
  let avl_result, avl_measurement = measure_operation avl_lookup in
  if patricia_result <> avl_result then failwith "string lookup checksums differ";
  report_operation "lookup" patricia_measurement avl_measurement
    (benchmark_size * lookup_repetitions)

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
  check_int_equivalent left_keys patricia_left avl_left;
  report_build "Integer keys" patricia_build avl_build;
  time_int_lookups left_keys patricia_left avl_left;
  let patricia_disjoint = build_patricia_int disjoint_keys in
  let avl_disjoint = build_avl_int disjoint_keys in
  let patricia_merged, patricia_merge =
    measure_operation (fun () -> Patricia.union_left patricia_left patricia_disjoint)
  in
  let avl_merged, avl_merge =
    measure_operation (fun () ->
        Int_avl.union (fun _ left _ -> Some left) avl_left avl_disjoint)
  in
  let all_disjoint = Array.append left_keys disjoint_keys in
  if patricia_cardinal patricia_merged <> 2 * benchmark_size
     || Int_avl.cardinal avl_merged <> 2 * benchmark_size then
    failwith "integer disjoint union produced the wrong cardinality";
  check_int_equivalent all_disjoint patricia_merged avl_merged;
  report_operation "disjoint union" patricia_merge avl_merge 1;
  let patricia_overlap = build_patricia_int overlap_keys in
  let avl_overlap = build_avl_int overlap_keys in
  let patricia_merged, patricia_merge =
    measure_operation (fun () -> Patricia.union_left patricia_left patricia_overlap)
  in
  let avl_merged, avl_merge =
    measure_operation (fun () ->
        Int_avl.union (fun _ left _ -> Some left) avl_left avl_overlap)
  in
  let all_overlap = Array.append left_keys overlap_keys in
  let expected_overlap = benchmark_size + (benchmark_size / 2) in
  if patricia_cardinal patricia_merged <> expected_overlap
     || Int_avl.cardinal avl_merged <> expected_overlap then
    failwith "integer overlapping union produced the wrong cardinality";
  check_int_equivalent all_overlap patricia_merged avl_merged;
  report_operation "overlap union" patricia_merge avl_merge 1;
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

let benchmark_strings length =
  let left_keys = short_string_keys length 0 in
  let disjoint_keys = short_string_keys length benchmark_size in
  let overlap_keys = short_string_keys length (benchmark_size / 2) in
  let patricia_left, patricia_build =
    measure_build string_patricia_cardinal (fun () -> build_patricia_string left_keys)
  in
  let avl_left, avl_build =
    measure_build String_avl.cardinal (fun () -> build_avl_string left_keys)
  in
  check_string_equivalent left_keys patricia_left avl_left;
  report_build (Printf.sprintf "String keys (%d characters)" length) patricia_build avl_build;
  time_string_lookups left_keys patricia_left avl_left;
  let patricia_disjoint = build_patricia_string disjoint_keys in
  let avl_disjoint = build_avl_string disjoint_keys in
  let patricia_merged, patricia_merge =
    measure_operation (fun () -> StringPatricia.union_left patricia_left patricia_disjoint)
  in
  let avl_merged, avl_merge =
    measure_operation (fun () ->
        String_avl.union (fun _ left _ -> Some left) avl_left avl_disjoint)
  in
  let all_disjoint = Array.append left_keys disjoint_keys in
  if string_patricia_cardinal patricia_merged <> 2 * benchmark_size
     || String_avl.cardinal avl_merged <> 2 * benchmark_size then
    failwith "string disjoint union produced the wrong cardinality";
  check_string_equivalent all_disjoint patricia_merged avl_merged;
  report_operation "disjoint union" patricia_merge avl_merge 1;
  let patricia_overlap = build_patricia_string overlap_keys in
  let avl_overlap = build_avl_string overlap_keys in
  let patricia_merged, patricia_merge =
    measure_operation (fun () -> StringPatricia.union_left patricia_left patricia_overlap)
  in
  let avl_merged, avl_merge =
    measure_operation (fun () ->
        String_avl.union (fun _ left _ -> Some left) avl_left avl_overlap)
  in
  let all_overlap = Array.append left_keys overlap_keys in
  let expected_overlap = benchmark_size + (benchmark_size / 2) in
  if string_patricia_cardinal patricia_merged <> expected_overlap
     || String_avl.cardinal avl_merged <> expected_overlap then
    failwith "string overlapping union produced the wrong cardinality";
  check_string_equivalent all_overlap patricia_merged avl_merged;
  report_operation "overlap union" patricia_merge avl_merge 1;
  print_newline ()

let () =
  Printf.printf
    "Patricia versus Stdlib.Map (AVL), %d bindings per input tree\n\n"
    benchmark_size;
  benchmark_int ();
  List.iter benchmark_strings [3; 4; 5];
  print_endline "Patricia comparison benchmark: ok"
