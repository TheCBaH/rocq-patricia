(* Isolated attribution measurements for the generated HAMT boundary.
   These are not map-operation timings: they distinguish checked scalar calls,
   sequence reads/edits/views, and the callback shape used by the integer
   benchmark when a compatible sampling profiler is unavailable. *)

module Bench = HashTableBenchmarkSupport

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      let parsed = int_of_string value in
      if parsed < 1 then invalid_arg (name ^ " must be positive") else parsed

let iterations = positive_env "HASHTABLE_PRIMITIVE_BENCH_ITERATIONS" 100_000
let values = Array.init 32 Fun.id
let sequence = HashTablePrimitives.of_list (Array.to_list values)

let fold_indices f =
  let total = ref 0 in
  for index = 0 to iterations - 1 do
    total := !total lxor f index
  done;
  !total

let hash_callback ~seed key = key lxor seed

let () =
  Bench.start ~workload:"isolated HAMT scalar/sequence attribution (no compatible profiler)"
    ~size:iterations ~seed:31;
  Bench.measure [
    { Bench.implementation = "native scalar"; operation = "chunk";
      run = fun _ -> fold_indices (fun index ->
        HashTableScalarPrimitives.chunk (index land ((1 lsl 30) - 1)) (index mod 6)) };
    { Bench.implementation = "native scalar"; operation = "bitmap_has";
      run = fun _ -> fold_indices (fun index ->
        if HashTableScalarPrimitives.bitmap_has 0x5555_5555 (index land 31) then 1 else 0) };
    { Bench.implementation = "native scalar"; operation = "rank";
      run = fun _ -> fold_indices (fun index ->
        HashTableScalarPrimitives.rank 0x5555_5555 (index land 31)) };
    { Bench.implementation = "hash callback"; operation = "integer callback";
      run = fun _ -> fold_indices (fun index -> hash_callback ~seed:31 index) };
    { Bench.implementation = "private sequence"; operation = "get";
      run = fun _ -> fold_indices (fun index ->
        match HashTablePrimitives.get (index land 31) sequence with
        | Some value -> value | None -> -1) };
    { Bench.implementation = "private sequence"; operation = "replace/fresh-copy";
      run = fun _ -> fold_indices (fun index ->
        HashTablePrimitives.length
          (HashTablePrimitives.replace (index land 31) index sequence)) };
    { Bench.implementation = "private sequence"; operation = "insert/fresh-copy";
      run = fun _ -> fold_indices (fun index ->
        HashTablePrimitives.length
          (HashTablePrimitives.insert (index land 31) index sequence)) };
    { Bench.implementation = "private sequence"; operation = "remove/fresh-copy";
      run = fun _ -> fold_indices (fun index ->
        HashTablePrimitives.length
          (HashTablePrimitives.remove (index land 31) sequence)) };
    { Bench.implementation = "private sequence"; operation = "to_list/view";
      run = fun _ -> fold_indices (fun _ -> Stdlib.List.length (HashTablePrimitives.to_list sequence)) };
  ];
  Bench.finish ()
