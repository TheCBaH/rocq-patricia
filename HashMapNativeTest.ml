module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key =
    if key land 7 = 0 then seed else key lxor seed
end

module Reference = HashMap.Make (Key)
module Native = HashMapNative.Make (Key)

module Slot_key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key = seed lxor key
end

module Slot_reference = HashMap.Make (Slot_key)
module Slot_native = HashMapNative.Make (Slot_key)

module Folded_key = struct
  type t = string
  let canonical = String.lowercase_ascii
  let equal left right = String.equal (canonical left) (canonical right)
  (* Deliberately collision-heavy, while remaining compatible with [equal]. *)
  let hash ~seed key = seed lxor String.length (canonical key)
end

module Folded_reference = HashMap.Make (Folded_key)
module Folded_native = HashMapNative.Make (Folded_key)

let fail message = failwith ("HashMap native test: " ^ message)
let check message condition = if not condition then fail message

let check_agreement message reference native =
  let probes = min_int :: max_int :: Stdlib.List.init 257 (fun index -> index - 128) in
  Stdlib.List.iter
    (fun key ->
       check (message ^ " key " ^ string_of_int key)
         (Reference.get key reference = Native.get key native))
    probes;
  check (message ^ " empty") (Reference.is_empty reference = Native.is_empty native)

let functional_value map key =
  Option.map (fun value -> value 10) (Folded_reference.get key map)

let functional_native_value map key =
  Option.map (fun value -> value 10) (Folded_native.get key map)

let check_functional message reference native key expected =
  check (message ^ " reference") (functional_value reference key = expected);
  check (message ^ " native") (functional_native_value native key = expected);
  check (message ^ " agreement")
    (functional_value reference key = functional_native_value native key)

let check_custom_key_and_payload () =
  let base_reference = Folded_reference.empty ~seed:23 in
  let base_native = Folded_native.empty ~seed:23 in
  let first_reference = Folded_reference.set "Alpha" (fun x -> x + 1) base_reference in
  let first_native = Folded_native.set "Alpha" (fun x -> x + 1) base_native in
  let collision_reference = Folded_reference.set "Gamma" (fun x -> x + 2) first_reference in
  let collision_native = Folded_native.set "Gamma" (fun x -> x + 2) first_native in
  let replaced_reference = Folded_reference.set "ALPHA" (fun x -> x + 3) collision_reference in
  let replaced_native = Folded_native.set "ALPHA" (fun x -> x + 3) collision_native in
  let removed_reference = Folded_reference.remove "gAmMa" replaced_reference in
  let removed_native = Folded_native.remove "gAmMa" replaced_native in
  check_functional "custom retained alpha" first_reference first_native "alpha" (Some 11);
  check_functional "custom retained collision" collision_reference collision_native "GAMMA" (Some 12);
  check_functional "custom replacement" replaced_reference replaced_native "aLpHa" (Some 13);
  check_functional "custom removal" removed_reference removed_native "gamma" None;
  check_functional "custom retained replacement" replaced_reference replaced_native "gamma" (Some 12)

let check_random_custom_key_and_payload () =
  let random = Random.State.make [| 0x43555354; 0x4f4d4b45 |] in
  let canonical_keys =
    [| "alpha"; "bravo"; "charl"; "delta"; "echoo"; "foxtt";
       "golfy"; "hotel"; "india"; "julie"; "kappa"; "limaa" |]
  in
  let spelling key =
    match Random.State.int random 4 with
    | 0 -> String.uppercase_ascii key
    | 1 -> String.capitalize_ascii key
    | 2 -> String.lowercase_ascii key
    | _ ->
        String.mapi (fun index character ->
          if index land 1 = 0 then Char.uppercase_ascii character else character) key
  in
  let probes =
    Array.to_list canonical_keys
    |> Stdlib.List.map (fun key -> [ key; String.uppercase_ascii key ])
    |> Stdlib.List.flatten
  in
  let check_maps message reference native =
    Stdlib.List.iter
      (fun key ->
         check (message ^ " reference " ^ key)
           (functional_value reference key = functional_native_value native key))
      probes;
    check (message ^ " empty")
      (Folded_reference.is_empty reference = Folded_native.is_empty native)
  in
  let rec loop step reference native retained =
    if step = 750 then ()
    else
      let key = spelling canonical_keys.(Random.State.int random (Array.length canonical_keys)) in
      let reference, native =
        if Random.State.bool random then
          let offset = step in
          ( Folded_reference.set key (fun input -> input + offset) reference,
            Folded_native.set key (fun input -> input + offset) native )
        else
          (Folded_reference.remove key reference, Folded_native.remove key native)
      in
      check_maps ("custom current " ^ string_of_int step) reference native;
      let retained = (reference, native) :: retained in
      let old_reference, old_native =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_maps ("custom retained " ^ string_of_int step) old_reference old_native;
      loop (step + 1) reference native retained
  in
  let reference = Folded_reference.empty ~seed:41 in
  let native = Folded_native.empty ~seed:41 in
  loop 0 reference native [ (reference, native) ]

let check_every_root_slot () =
  let reference = Slot_reference.empty ~seed:0 in
  let native = Slot_native.empty ~seed:0 in
  let reference, native =
    Stdlib.List.fold_left
      (fun (reference, native) slot ->
         (Slot_reference.set slot (string_of_int slot) reference,
          Slot_native.set slot (string_of_int slot) native))
      (reference, native) (Stdlib.List.init 32 Fun.id)
  in
  Stdlib.List.iter
    (fun slot ->
       let expected = Some (string_of_int slot) in
       check ("all slots reference " ^ string_of_int slot)
         (Slot_reference.get slot reference = expected);
       check ("all slots native " ^ string_of_int slot)
         (Slot_native.get slot native = expected))
    (Stdlib.List.init 32 Fun.id);
  let deleted_reference = Slot_reference.remove 31 reference in
  let deleted_native = Slot_native.remove 31 native in
  check "slot 31 removed from reference" (Slot_reference.get 31 deleted_reference = None);
  check "slot 31 removed from native" (Slot_native.get 31 deleted_native = None);
  Stdlib.List.iter
    (fun slot ->
       if slot <> 31 then begin
         let expected = Some (string_of_int slot) in
         check ("slot delete reference " ^ string_of_int slot)
           (Slot_reference.get slot deleted_reference = expected);
         check ("slot delete native " ^ string_of_int slot)
           (Slot_native.get slot deleted_native = expected)
       end)
    (Stdlib.List.init 32 Fun.id);
  let reinserted_reference = Slot_reference.set 31 "reinserted" deleted_reference in
  let reinserted_native = Slot_native.set 31 "reinserted" deleted_native in
  check "slot 31 reinserted into reference"
    (Slot_reference.get 31 reinserted_reference = Some "reinserted");
  check "slot 31 reinserted into native"
    (Slot_native.get 31 reinserted_native = Some "reinserted");
  check "all-slot reference retained"
    (Slot_reference.get 31 reference = Some "31");
  check "all-slot native retained" (Slot_native.get 31 native = Some "31")

let () =
  let random = Random.State.make [| 0x41525241; 0x59544553 |] in
  let rec loop step reference native retained =
    if step = 1000 then ()
    else begin
      let key =
        match Random.State.int random 16 with
        | 0 -> min_int
        | 1 -> max_int
        | _ -> Random.State.int random 257 - 128
      in
      let reference, native =
        if Random.State.bool random then begin
          let value = string_of_int step in
          (Reference.set key value reference, Native.set key value native)
        end else
          (Reference.remove key reference, Native.remove key native)
      in
      check_agreement "current" reference native;
      let retained = (reference, native) :: retained in
      let old_reference, old_native =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_agreement "retained" old_reference old_native;
      loop (step + 1) reference native retained
    end
  in
  let reference = Reference.of_list ~seed:19 [ (0, "first"); (0, "later"); (8, "collision") ] in
  let native = Native.of_list ~seed:19 [ (0, "first"); (0, "later"); (8, "collision") ] in
  check "first-wins reference" (Reference.get 0 reference = Some "first");
  check "first-wins native" (Native.get 0 native = Some "first");
  check_agreement "bulk load" reference native;
  loop 0 reference native [ (reference, native) ];
  check_custom_key_and_payload ();
  check_random_custom_key_and_payload ();
  check_every_root_slot ();
  print_endline "HashMap native array differential test passed"
