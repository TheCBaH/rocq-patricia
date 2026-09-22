let fail message = failwith ("HashTable native-model test: " ^ message)
let check message condition = if not condition then fail message

let equal (left : int) right = left = right
let hash key = key land 0x3fffffff

let check_agreement message source native =
  let probes = min_int :: max_int :: Stdlib.List.init 257 (fun index -> index - 128) in
  Stdlib.List.iter
    (fun key ->
       let source_value = HashTable.get_tree equal 6 0 (hash key) key source in
       let native_value = HashTableNative.native_get equal 6 0 (hash key) key native in
       check (message ^ " key " ^ string_of_int key) (source_value = native_value))
    probes

let () =
  let collision_entries =
    Stdlib.List.init 40 (fun key -> (key, "collision-" ^ string_of_int key))
  in
  let collision_source = HashTable.Collision (0, collision_entries) in
  let collision_native =
    HashTableNative.NativeCollision (0, HashTableNative.pseq_of_list collision_entries)
  in
  Stdlib.List.iter
    (fun key ->
       check ("collision key " ^ string_of_int key)
         (HashTableNative.native_get equal 6 0 0 key collision_native =
          HashTable.get_tree equal 6 0 0 key collision_source))
    (Stdlib.List.init 40 Fun.id);
  check "collision miss"
    (HashTableNative.native_get equal 6 0 0 41 collision_native = None);
  let collision_source_updated =
    HashTable.set_tree equal 6 0 0 17 "collision-updated" collision_source
  in
  let collision_native_updated =
    HashTableNative.native_set equal 6 0 0 17 "collision-updated" collision_native
  in
  check "collision update preserves old version"
    (HashTableNative.native_get equal 6 0 0 17 collision_native = Some "collision-17");
  Stdlib.List.iter
    (fun key ->
       check ("collision update key " ^ string_of_int key)
         (HashTableNative.native_get equal 6 0 0 key collision_native_updated =
          HashTable.get_tree equal 6 0 0 key collision_source_updated))
    (Stdlib.List.init 40 Fun.id);
  let collision_source_appended =
    HashTable.set_tree equal 6 0 0 40 "collision-40" collision_source_updated
  in
  let collision_native_appended =
    HashTableNative.native_set equal 6 0 0 40 "collision-40" collision_native_updated
  in
  Stdlib.List.iter
    (fun key ->
       check ("collision append key " ^ string_of_int key)
         (HashTableNative.native_get equal 6 0 0 key collision_native_appended =
          HashTable.get_tree equal 6 0 0 key collision_source_appended))
    (Stdlib.List.init 41 Fun.id);
  let collision_source_removed =
    HashTable.remove_tree equal 6 0 0 17 collision_source_appended
  in
  let collision_native_removed =
    HashTableNative.native_remove equal 6 0 0 17 collision_native_appended
  in
  check "collision removal preserves old version"
    (HashTableNative.native_get equal 6 0 0 17 collision_native_appended =
     Some "collision-updated");
  Stdlib.List.iter
    (fun key ->
       check ("collision remove key " ^ string_of_int key)
         (HashTableNative.native_get equal 6 0 0 key collision_native_removed =
          HashTable.get_tree equal 6 0 0 key collision_source_removed))
    (Stdlib.List.init 41 Fun.id);
  let two_entries = [ 1, "one"; 2, "two" ] in
  let two_source = HashTable.Collision (0, two_entries) in
  let two_native =
    HashTableNative.NativeCollision (0, HashTableNative.pseq_of_list two_entries)
  in
  let one_source = HashTable.remove_tree equal 6 0 0 1 two_source in
  let one_native = HashTableNative.native_remove equal 6 0 0 1 two_native in
  check "collision removal normalizes to leaf"
    (match one_native with HashTableNative.NativeLeaf (0, 2, "two") -> true | _ -> false);
  check "collision leaf normalization agrees"
    (HashTableNative.native_get equal 6 0 0 2 one_native =
     HashTable.get_tree equal 6 0 0 2 one_source);
  let empty_source = HashTable.remove_tree equal 6 0 0 2 one_source in
  let empty_native = HashTableNative.native_remove equal 6 0 0 2 one_native in
  check "collision removal normalizes to empty"
    (match empty_native with HashTableNative.NativeEmpty -> true | _ -> false);
  check "collision empty normalization agrees"
    (HashTableNative.native_get equal 6 0 0 2 empty_native =
     HashTable.get_tree equal 6 0 0 2 empty_source);
  Stdlib.List.iter
    (fun depth ->
       let right_hash = 1 lsl (5 * depth) in
       let left_source = HashTable.Leaf (0, 0, "left") in
       let left_native = HashTableNative.NativeLeaf (0, 0, "left") in
       let source =
         HashTable.set_tree equal 6 0 right_hash (depth + 1) "right" left_source
       in
       let native =
         HashTableNative.native_set equal 6 0 right_hash (depth + 1) "right" left_native
       in
       check ("distinct-hash join depth " ^ string_of_int depth ^ " left")
         (HashTableNative.native_get equal 6 0 0 0 native =
          HashTable.get_tree equal 6 0 0 0 source);
       check ("distinct-hash join depth " ^ string_of_int depth ^ " right")
         (HashTableNative.native_get equal 6 0 right_hash (depth + 1) native =
          HashTable.get_tree equal 6 0 right_hash (depth + 1) source))
    (Stdlib.List.init 6 Fun.id);
  let random = Random.State.make [| 0x4e415449; 0x56454d4f |] in
  let rec loop step source native retained =
    if step = 750 then ()
    else begin
      let key =
        match Random.State.int random 16 with
        | 0 -> min_int
        | 1 -> max_int
        | _ -> Random.State.int random 257 - 128
      in
      let source, native =
        if Random.State.bool random then begin
          let value = string_of_int step in
          (HashTable.set_tree equal 6 0 (hash key) key value source,
           HashTableNative.native_set equal 6 0 (hash key) key value native)
        end else
          (HashTable.remove_tree equal 6 0 (hash key) key source,
           HashTableNative.native_remove equal 6 0 (hash key) key native)
      in
      check_agreement "current" source native;
      let retained = (source, native) :: retained in
      let old_source, old_native =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_agreement "retained" old_source old_native;
      loop (step + 1) source native retained
    end
  in
  let source = HashTable.Empty in
  let native = HashTableNative.native_of_source source in
  loop 0 source native [ (source, native) ];
  print_endline "HashTable native-model differential test passed"
