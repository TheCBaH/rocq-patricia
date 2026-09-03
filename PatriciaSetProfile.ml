(* Allocation profile for the public source-extracted string [set] and its
   ordinary extracted alternatives. This is diagnostic evidence only; it does
   not establish a formal cost claim. *)

module S = StringPatriciaInternal

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

let profile_size = positive_env "PATRICIA_SET_PROFILE_SIZE" 10_000

type measurement = {
  allocated_words : float;
  retained_words : int;
}

let allocated_words () =
  let stats = Gc.quick_stat () in
  stats.Gc.minor_words +. stats.Gc.major_words

let measure operation =
  Gc.full_major ();
  Gc.compact ();
  let before_live = (Gc.stat ()).Gc.live_words in
  let before_allocated = allocated_words () in
  let result = operation () in
  let allocated_words = allocated_words () -. before_allocated in
  ignore (Sys.opaque_identity result);
  Gc.full_major ();
  Gc.compact ();
  result, { allocated_words;
            retained_words = (Gc.stat ()).Gc.live_words - before_live }

let key index = Printf.sprintf "%08x" index

let keys = Array.init profile_size key

let build setter =
  Array.fold_left
    (fun tree name -> setter name (Stdlib.String.length name) tree)
    S.empty keys

let update setter tree =
  Array.fold_left
    (fun result name -> setter name (1 + Stdlib.String.length name) result)
    tree keys

let check label tree expected_value =
  if List.length (S.elements tree) <> profile_size then
    failwith (label ^ ": wrong cardinality");
  Array.iter
    (fun name ->
       if S.get name tree <> Some (expected_value name) then
         failwith (label ^ ": lookup mismatch"))
    keys

let print_row workload name measurement =
  Printf.printf "  %-10s %-16s %12.0f %12d\n"
    workload name measurement.allocated_words measurement.retained_words

let profile workload operation expected_value =
  let result, measurement = measure operation in
  check workload result expected_value;
  measurement

let () =
  let public_set = S.set in
  let descent = S.set_one_descent in
  let shared = S.set_one_descent_shared in
  let two_descent = S.set_two_descent in
  Printf.printf "String set profile (%d bindings)\n" profile_size;
  Printf.printf "  %-10s %-16s %12s %12s\n"
    "workload" "worker" "allocated" "retained";
  Printf.printf "  %-10s %-16s %12s %12s\n"
    "" "" "words" "words";
  let build_public = profile "build public" (fun () -> build public_set)
      Stdlib.String.length in
  let build_descent = profile "build descent" (fun () -> build descent)
      Stdlib.String.length in
  let build_shared = profile "build shared" (fun () -> build shared)
      Stdlib.String.length in
  let build_two_descent = profile "build two descent" (fun () -> build two_descent)
      Stdlib.String.length in
  print_row "build" "public set" build_public;
  print_row "build" "descent" build_descent;
  print_row "build" "shared" build_shared;
  print_row "build" "two descent" build_two_descent;
  let input = build public_set in
  let update_public = profile "update public" (fun () -> update public_set input)
      (fun name -> 1 + Stdlib.String.length name) in
  let update_descent = profile "update descent" (fun () -> update descent input)
      (fun name -> 1 + Stdlib.String.length name) in
  let update_shared = profile "update shared" (fun () -> update shared input)
      (fun name -> 1 + Stdlib.String.length name) in
  let update_two_descent =
    profile "update two descent" (fun () -> update two_descent input)
      (fun name -> 1 + Stdlib.String.length name) in
  print_row "update" "public set" update_public;
  print_row "update" "descent" update_descent;
  print_row "update" "shared" update_shared
  ; print_row "update" "two descent" update_two_descent
