(* Checked string-key comparison for the public source-reference and private
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

let size =
  match Sys.getenv_opt "HASHTABLE_BENCH_SIZE" with
  | None -> 2_000
  | Some value -> int_of_string value

let seed =
  match Sys.getenv_opt "HASHTABLE_BENCH_SEED" with
  | None -> 31
  | Some value -> int_of_string value

let fail message = failwith ("HashTable string benchmark: " ^ message)

let time name run =
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  let result = run () in
  let elapsed = Unix.gettimeofday () -. started in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "%s: %.6fs, %.0f allocated bytes\n%!" name elapsed allocated;
  result

let retained_versions name empty set get bindings first_key first_value =
  Gc.compact ();
  let before = (Gc.stat ()).live_words in
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
  if get first_key newest <> Some first_value || get first_key oldest <> None then
    fail (name ^ " retained-root lookup mismatch");
  let bytes = (after - before) * (Sys.word_size / 8) in
  Printf.printf "%s retained heap: %d bytes (%d prefix roots)\n%!"
    name bytes (Stdlib.List.length roots);
  Sys.opaque_identity roots

let () =
  if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive";
  Printf.printf
    "HashTable string benchmark workload: fixed-width decimal keys [0,%d), seed %d; \
     retained policy: every prefix root for persistent maps\n%!"
    size seed;
  let bindings =
    Stdlib.List.init size (fun index ->
        let key = Printf.sprintf "key-%08d" index in
        (key, string_of_int index))
  in
  let first_key, first_value = Stdlib.List.hd bindings in
  let hashed = time "HashMap.Make string build"
      (fun () -> Hash_map.of_list ~seed bindings)
  in
  let native_hashed = time "HashMapNative.Make string build"
      (fun () -> Native_hash_map.of_list ~seed bindings)
  in
  let ordered = time "Map.Make(String) build" (fun () ->
      Stdlib.List.fold_left
        (fun map (key, value) -> Ordered_map.add key value map)
        Ordered_map.empty bindings)
  in
  let standard = time "OCaml Hashtbl (imperative) string build" (fun () ->
      let table = Hashtbl.create size in
      Stdlib.List.iter (fun (key, value) -> Hashtbl.replace table key value) bindings;
      table)
  in
  ignore (retained_versions "HashMap.Make string" (Hash_map.empty ~seed)
            Hash_map.set Hash_map.get bindings first_key first_value);
  ignore (retained_versions "HashMapNative.Make string" (Native_hash_map.empty ~seed)
            Native_hash_map.set Native_hash_map.get bindings first_key first_value);
  ignore (retained_versions "Map.Make(String)" Ordered_map.empty Ordered_map.add
            Ordered_map.find_opt bindings first_key first_value);
  let check name get =
    Stdlib.List.iter
      (fun (key, value) ->
         if get key <> Some value then fail (name ^ " lookup mismatch"))
      bindings;
    if get "not-present" <> None then fail (name ^ " missing lookup mismatch")
  in
  time "HashMap.Make checked string lookup"
    (fun () -> check "HashMap.Make" (fun key -> Hash_map.get key hashed));
  time "HashMapNative.Make checked string lookup"
    (fun () -> check "HashMapNative.Make" (fun key -> Native_hash_map.get key native_hashed));
  time "Map.Make(String) checked lookup"
    (fun () -> check "Map.Make(String)" (fun key -> Ordered_map.find_opt key ordered));
  time "OCaml Hashtbl (imperative) checked string lookup"
    (fun () -> check "Hashtbl" (fun key -> Hashtbl.find_opt standard key));
  let updated_value key = "updated-" ^ key in
  let updated = time "HashMap.Make string update" (fun () ->
      Stdlib.List.fold_left
        (fun map (key, _) -> Hash_map.set key (updated_value key) map)
        hashed bindings)
  in
  let native_updated = time "HashMapNative.Make string update" (fun () ->
      Stdlib.List.fold_left
        (fun map (key, _) -> Native_hash_map.set key (updated_value key) map)
        native_hashed bindings)
  in
  let ordered_updated = time "Map.Make(String) update" (fun () ->
      Stdlib.List.fold_left
        (fun map (key, _) -> Ordered_map.add key (updated_value key) map)
        ordered bindings)
  in
  let standard_updated = time "OCaml Hashtbl (imperative) string update" (fun () ->
      Stdlib.List.iter
        (fun (key, _) -> Hashtbl.replace standard key (updated_value key)) bindings;
      standard)
  in
  Stdlib.List.iter (fun (key, _) ->
      let expected = Some (updated_value key) in
      if Hash_map.get key updated <> expected
         || Native_hash_map.get key native_updated <> expected
         || Ordered_map.find_opt key ordered_updated <> expected
         || Hashtbl.find_opt standard_updated key <> expected then
        fail "update lookup mismatch") bindings;
  let removed = time "HashMap.Make string remove" (fun () ->
      Stdlib.List.fold_left (fun map (key, _) -> Hash_map.remove key map) updated bindings)
  in
  let native_removed = time "HashMapNative.Make string remove" (fun () ->
      Stdlib.List.fold_left (fun map (key, _) -> Native_hash_map.remove key map)
        native_updated bindings)
  in
  let ordered_removed = time "Map.Make(String) remove" (fun () ->
      Stdlib.List.fold_left (fun map (key, _) -> Ordered_map.remove key map)
        ordered_updated bindings)
  in
  let standard_removed = time "OCaml Hashtbl (imperative) string remove" (fun () ->
      Stdlib.List.iter (fun (key, _) -> Hashtbl.remove standard_updated key) bindings;
      standard_updated)
  in
  Stdlib.List.iter (fun (key, _) ->
      if Hash_map.get key removed <> None
         || Native_hash_map.get key native_removed <> None
         || Ordered_map.find_opt key ordered_removed <> None
         || Hashtbl.find_opt standard_removed key <> None then
        fail "remove lookup mismatch") bindings;
  Printf.printf "HashTable checked string benchmark passed (%d bindings)\n%!" size
