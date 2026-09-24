type config = {
  repetitions : int;
  warmups : int;
  live_heap : bool;
  pre_sample_gc : string;
  result_file : string;
}

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      let parsed = int_of_string value in
      if parsed < 1 then invalid_arg (name ^ " must be positive") else parsed

let boolean_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some "true" -> true
  | Some "false" -> false
  | Some _ -> invalid_arg (name ^ " must be true or false")

let config () =
  let repetitions = positive_env "HASHTABLE_BENCH_REPETITIONS" 7 in
  let warmups = positive_env "HASHTABLE_BENCH_WARMUPS" 1 in
  let live_heap = boolean_env "HASHTABLE_BENCH_LIVE_HEAP" true in
  let pre_sample_gc =
    match Sys.getenv_opt "HASHTABLE_BENCH_PRE_SAMPLE_GC" with
    | None | Some "compact" -> "compact"
    | Some "major" -> "major"
    | Some "minor" -> "minor"
    | Some _ -> invalid_arg "HASHTABLE_BENCH_PRE_SAMPLE_GC must be compact, major or minor"
  in
  let result_file =
    match Sys.getenv_opt "HASHTABLE_BENCH_RESULTS" with
    | Some path -> path
    | None -> Filename.concat (Filename.get_temp_dir_name ())
                (Printf.sprintf "hashtable-performance-%d.jsonl" (Unix.getpid ()))
  in
  { repetitions; warmups; live_heap; pre_sample_gc; result_file }

let active_config = ref None
let output = ref None

let json_string value = Printf.sprintf "%S" value

let has_suffix suffix value =
  let suffix_length = String.length suffix in
  let value_length = String.length value in
  suffix_length <= value_length &&
  String.sub value (value_length - suffix_length) suffix_length = suffix

let history_policy operation =
  if has_suffix "/all-prefix-roots" operation then "all-prefix-roots"
  else if has_suffix "/latest-root" operation then "latest-root"
  else "single-version"

let live_heap_enabled () =
  match !active_config with
  | Some settings -> settings.live_heap
  | None -> invalid_arg "HashTableBenchmarkSupport.live_heap_enabled"

let write_json line =
  match !output with
  | None -> ()
  | Some channel -> output_string channel line; output_char channel '\n'; flush channel

let read_first_line path =
  try
    let channel = open_in path in
    let line = input_line channel in
    close_in_noerr channel;
    line
  with Sys_error _ | End_of_file -> "unavailable"

let command_first_line command =
  try
    let channel = Unix.open_process_in command in
    let line = input_line channel in
    ignore (Unix.close_process_in channel);
    line
  with Unix.Unix_error _ | Sys_error _ | End_of_file -> "unavailable"

let env name = match Sys.getenv_opt name with Some value -> value | None -> "unknown"

let start ~workload ~size ~seed =
  let settings = config () in
  active_config := Some settings;
  output := Some (open_out settings.result_file);
  let system = command_first_line "uname -s" in
  let release = command_first_line "uname -r" in
  let machine = command_first_line "uname -m" in
  let cpu = read_first_line "/proc/cpuinfo" in
  let gc = Gc.get () in
  write_json
    (Printf.sprintf
       "{\"record\":\"metadata\",\"workload\":%s,\"size\":%d,\"seed\":%d,\"repetitions\":%d,\"warmups\":%d,\"live_heap\":%b,\"pre_sample_gc\":%s,\"revision\":%s,\"dirty\":%s,\"ocaml_version\":%s,\"word_size\":%d,\"os\":%s,\"release\":%s,\"machine\":%s,\"cpu\":%s,\"gc\":%s}"
       (json_string workload) size seed settings.repetitions settings.warmups settings.live_heap
       (json_string settings.pre_sample_gc)
       (json_string (env "HASHTABLE_BENCH_REVISION"))
       (json_string (env "HASHTABLE_BENCH_DIRTY"))
       (json_string Sys.ocaml_version) Sys.word_size
       (json_string system) (json_string release) (json_string machine)
       (json_string cpu)
       (json_string
          (Printf.sprintf "minor_heap=%d;major_increment=%d;space_overhead=%d;verbose=%d;max_overhead=%d"
             gc.Gc.minor_heap_size gc.Gc.major_heap_increment gc.Gc.space_overhead
             gc.Gc.verbose gc.Gc.max_overhead)));
  Printf.printf "machine-readable records: %s\n%!" settings.result_file

type task = {
  implementation : string;
  operation : string;
  run : int -> int;
}

type sample = { seconds : float; bytes : float; checksum : int }

let rotate offset values =
  let length = Stdlib.List.length values in
  if length = 0 then [] else
    let offset = offset mod length in
    let rec split count before after =
      if count = 0 then Stdlib.List.rev before, after
      else match after with
      | [] -> assert false
      | value :: rest -> split (count - 1) (value :: before) rest
    in
    let before, after = split offset [] values in
    after @ before

let median values =
  let ordered = Array.of_list values in
  Array.sort Float.compare ordered;
  let count = Array.length ordered in
  if count mod 2 = 1 then ordered.(count / 2)
  else (ordered.(count / 2 - 1) +. ordered.(count / 2)) /. 2.

let task_samples = Hashtbl.create 17

let add_sample task sample =
  let previous = match Hashtbl.find_opt task_samples task with Some xs -> xs | None -> [] in
  Hashtbl.replace task_samples task (sample :: previous)

let timed task repetition =
  let settings = match !active_config with Some value -> value | None -> invalid_arg "HashTableBenchmarkSupport.start" in
  (match settings.pre_sample_gc with
   | "compact" -> Gc.compact ()
   | "major" -> Gc.full_major ()
   | "minor" -> Gc.minor ()
   | _ -> assert false);
  let before = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  let checksum = Sys.opaque_identity (task.run repetition) in
  let seconds = Unix.gettimeofday () -. started in
  let bytes = Gc.allocated_bytes () -. before in
  let sample = { seconds; bytes; checksum } in
  add_sample (task.implementation, task.operation) sample;
  write_json
    (Printf.sprintf
       "{\"record\":\"sample\",\"implementation\":%s,\"operation\":%s,\"history_policy\":%s,\"repetition\":%d,\"seconds\":%.9f,\"allocated_bytes\":%.0f,\"checksum\":%d}"
       (json_string task.implementation) (json_string task.operation)
       (json_string (history_policy task.operation)) repetition seconds bytes checksum)

let measure tasks =
  let settings = match !active_config with Some value -> value | None -> invalid_arg "HashTableBenchmarkSupport.start" in
  Stdlib.List.iter
    (fun task ->
       for _ = 1 to settings.warmups do ignore (Sys.opaque_identity (task.run (-1))) done)
    tasks;
  for repetition = 0 to settings.repetitions - 1 do
    Stdlib.List.iter (fun task -> timed task repetition) (rotate repetition tasks)
  done;
  Hashtbl.iter
    (fun (implementation, operation) samples ->
       let seconds = Stdlib.List.map (fun sample -> sample.seconds) samples in
       let bytes = Stdlib.List.map (fun sample -> sample.bytes) samples in
       let min_seconds = Stdlib.List.fold_left min infinity seconds in
       let max_seconds = Stdlib.List.fold_left max neg_infinity seconds in
       let min_bytes = Stdlib.List.fold_left min infinity bytes in
       let max_bytes = Stdlib.List.fold_left max neg_infinity bytes in
       let median_seconds = median seconds in
       let median_bytes = median bytes in
       Printf.printf "%s %s: %.6fs (%.6f..%.6f), %.0f bytes (%.0f..%.0f)\n%!"
         implementation operation median_seconds min_seconds max_seconds
         median_bytes min_bytes max_bytes;
       write_json
         (Printf.sprintf
            "{\"record\":\"summary\",\"implementation\":%s,\"operation\":%s,\"history_policy\":%s,\"median_seconds\":%.9f,\"min_seconds\":%.9f,\"max_seconds\":%.9f,\"median_allocated_bytes\":%.0f,\"min_allocated_bytes\":%.0f,\"max_allocated_bytes\":%.0f}"
            (json_string implementation) (json_string operation)
            (json_string (history_policy operation))
            median_seconds min_seconds max_seconds median_bytes min_bytes max_bytes))
    task_samples;
  Hashtbl.reset task_samples

let live_heap ~implementation ~policy construct =
  Gc.compact ();
  let before = (Gc.stat ()).live_words in
  let value = construct () in
  Gc.compact ();
  let value = Sys.opaque_identity value in
  let after = (Gc.stat ()).live_words in
  let bytes = (after - before) * (Sys.word_size / 8) in
  Printf.printf "%s retained heap (%s): %d bytes\n%!" implementation policy bytes;
  write_json
    (Printf.sprintf
       "{\"record\":\"live_heap\",\"implementation\":%s,\"policy\":%s,\"bytes\":%d}"
       (json_string implementation) (json_string policy) bytes);
  value

let finish () =
  match !output with
  | None -> ()
  | Some channel -> close_out channel; output := None; active_config := None
