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
