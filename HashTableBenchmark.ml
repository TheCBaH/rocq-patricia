(* Checked, workload-specific benchmark for the source-reference and
   experimental fresh-array backends, plus OCaml's imperative [Hashtbl].
   Every timed result is checked against the association-list oracle; timings
   are not proof or portable performance claims. *)

module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key = key lxor seed
end

module Hash_map = HashMap.Make (Key)
module Native_hash_map = HashMapNative.Make (Key)
module Ordered_map = Map.Make (Int)

let size =
  match Sys.getenv_opt "HASHTABLE_BENCH_SIZE" with
  | None -> 2_000
  | Some value -> int_of_string value

let fail message = failwith ("HashTable benchmark: " ^ message)

let time name run =
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  let result = run () in
  let elapsed = Unix.gettimeofday () -. started in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "%s: %.6fs, %.0f allocated bytes\n%!" name elapsed allocated;
  result

let oracle_get key bindings =
  match Stdlib.List.find_opt (fun (stored, _) -> stored = key) bindings with
  | None -> None
  | Some (_, value) -> Some value

let retained_versions name empty set get bindings =
  Gc.compact ();
  let before = (Gc.stat ()).live_words in
  (* Keep every prefix root: this is the version-retention policy reported by
     the benchmark, rather than an implementation-dependent snapshot count. *)
  let roots =
    Stdlib.List.fold_left
      (fun roots (key, value) -> set key value (Stdlib.List.hd roots) :: roots)
      [ empty ] bindings
  in
  Gc.compact ();
  let roots = Sys.opaque_identity roots in
  let after = (Gc.stat ()).live_words in
  let newest = Stdlib.List.hd roots in
  let oldest = Stdlib.List.hd (Stdlib.List.rev roots) in
  if Stdlib.List.length roots <> Stdlib.List.length bindings + 1 then
    fail (name ^ " retained-root count mismatch");
  if get 0 newest <> Some "0" || get 0 oldest <> None then
    fail (name ^ " retained-root lookup mismatch");
  let bytes = (after - before) * (Sys.word_size / 8) in
  Printf.printf "%s retained heap: %d bytes (%d prefix roots)\n%!"
    name bytes (Stdlib.List.length roots);
  Sys.opaque_identity roots

let () =
  if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive";
  let bindings = Stdlib.List.init size (fun key -> (key, string_of_int key)) in
  let oracle = Stdlib.List.rev bindings in
  let hashed = time "HashMap.Make build" (fun () -> Hash_map.of_list ~seed:31 bindings) in
  let native_hashed = time "HashMapNative.Make build"
      (fun () -> Native_hash_map.of_list ~seed:31 bindings)
  in
  let ordered = time "Map.Make build"
      (fun () -> Stdlib.List.fold_left (fun map (key, value) -> Ordered_map.add key value map)
               Ordered_map.empty bindings)
  in
  let standard = time "OCaml Hashtbl (imperative) build" (fun () ->
      let table = Hashtbl.create size in
      Stdlib.List.iter (fun (key, value) -> Hashtbl.replace table key value) bindings;
      table)
  in
  ignore (retained_versions "HashMap.Make" (Hash_map.empty ~seed:31)
            Hash_map.set Hash_map.get bindings);
  ignore (retained_versions "HashMapNative.Make" (Native_hash_map.empty ~seed:31)
            Native_hash_map.set Native_hash_map.get bindings);
  ignore (retained_versions "Map.Make" Ordered_map.empty Ordered_map.add
            Ordered_map.find_opt bindings);
  let check name get =
    Stdlib.List.iter (fun (key, _) ->
      if get key <> oracle_get key oracle then fail (name ^ " lookup mismatch")) bindings;
    if get (-1) <> None then fail (name ^ " missing lookup mismatch")
  in
  time "HashMap.Make checked lookup" (fun () -> check "HashMap.Make" (fun key -> Hash_map.get key hashed));
  time "HashMapNative.Make checked lookup"
    (fun () -> check "HashMapNative.Make" (fun key -> Native_hash_map.get key native_hashed));
  time "Map.Make checked lookup" (fun () -> check "Map.Make" (fun key -> Ordered_map.find_opt key ordered));
  time "OCaml Hashtbl (imperative) checked lookup"
    (fun () -> check "Hashtbl" (fun key -> Hashtbl.find_opt standard key));
  Printf.printf "HashTable checked benchmark passed (%d bindings)\n%!" size
