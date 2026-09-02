module I = PatriciaInternal
module IU = PatriciaUnion
module S = StringPatriciaInternal
module SU = StringPatriciaUnion

let check_integer () =
  let rec build select value key tree =
    if key = 0 then tree
    else
      build select value (key - 1)
        (if select key then I.set key (value key) tree else tree)
  in
  let left = build (fun key -> key mod 2 = 0) (fun key -> key * 10) 64 I.empty in
  let right = build (fun key -> key mod 3 = 0) (fun key -> -key) 64 I.empty in
  let expected_left = I.union_left left right in
  let expected_right = I.union_right left right in
  let actual_left = IU.union_left_specialized left right in
  let actual_right = IU.union_right_specialized left right in
  let changed_left = IU.union_left_specialized_changed left right in
  let changed_result =
    match changed_left with I.Empty -> left | changed -> changed
  in
  let fuel_result = IU.union_left_specialized_changed_fuel_result left right in
  let native_result = IU.union_left_native_default left right in
  let native_fuel_result = IU.union_left_native_fuel_default left right in
  let native_inline_result = IU.union_left_native_fuel_inline_default left right in
  if native_result <> expected_left || native_fuel_result <> expected_left
     || native_inline_result <> expected_left then
    failwith "integer native-shaped worker differs structurally from legacy union";
  for key = 1 to 64 do
    if I.get key actual_left <> I.get key expected_left then
      failwith "integer specialized left union mismatch";
    if I.get key actual_right <> I.get key expected_right then
      failwith "integer specialized right union mismatch";
    if I.get key changed_result <> I.get key expected_left then
      failwith "integer changed-worker union mismatch";
    if I.get key fuel_result <> I.get key expected_left then
      failwith "integer closure-free changed-worker union mismatch";
    if I.get key native_result <> I.get key expected_left then
      failwith "integer native-shaped worker union mismatch";
    if I.get key native_fuel_result <> I.get key expected_left then
      failwith "integer native-shaped fuel-worker union mismatch";
    if I.get key native_inline_result <> I.get key expected_left then
      failwith "integer inline native-worker union mismatch"
  done;
  let subset = build (fun key -> key mod 2 = 0) (fun key -> -key) 64 I.empty in
  if IU.union_left_specialized_changed left subset <> I.Empty then
    failwith "integer changed worker missed unchanged certificate";
  List.iter
    (fun (name, union) ->
      if union left I.empty != left then
        failwith ("integer " ^ name ^ " lost empty-right root reuse");
      if union left subset != left then
        failwith ("integer " ^ name ^ " lost subset root reuse");
      if union left left != left then
        failwith ("integer " ^ name ^ " lost equal root reuse"))
    [ "native-shaped", IU.union_left_native_default;
      "native-shaped fuel", IU.union_left_native_fuel_default;
      "inline native-shaped fuel", IU.union_left_native_fuel_inline_default ];
  if changed_left = I.Empty then
    failwith "integer changed worker missed fresh right bindings";
  let nested = I.set 3 30 (I.set 1 10 I.empty) in
  let enclosing = I.set 8 80 nested in
  let nested_changed = IU.union_left_specialized_changed nested enclosing in
  let nested_result =
    match nested_changed with I.Empty -> nested | changed -> changed
  in
  if nested_changed = I.Empty || I.get 8 nested_result <> Some 80 then
    failwith "integer changed worker dropped an outer sibling";
  for seed = 1 to 32 do
    let state = ref seed in
    let next () =
      state := ((!state * 1103515245) + 12345) land 0x3fffffff;
      !state
    in
    let rec add count tree =
      if count = 0 then tree
      else
        let key = 1 + (next () mod 127) in
        add (count - 1) (I.set key (next ()) tree)
    in
    let random_left = add 48 I.empty in
    let random_right = add 48 I.empty in
    let random_changed = IU.union_left_specialized_changed random_left random_right in
    let random_result =
      match random_changed with I.Empty -> random_left | changed -> changed
    in
    let random_fuel_result =
      IU.union_left_specialized_changed_fuel_result random_left random_right
    in
    let random_native_result = IU.union_left_native_default random_left random_right in
    let random_native_fuel_result =
      IU.union_left_native_fuel_default random_left random_right
    in
    let random_native_inline_result =
      IU.union_left_native_fuel_inline_default random_left random_right
    in
    let random_expected = I.union_left random_left random_right in
    if random_native_result <> random_expected
       || random_native_fuel_result <> random_expected
       || random_native_inline_result <> random_expected then
      failwith "integer randomized native-shaped worker differs structurally from legacy union";
    for key = 1 to 127 do
      if I.get key random_result <> I.get key random_expected then
        failwith "integer randomized changed-worker union mismatch";
      if I.get key random_fuel_result <> I.get key random_expected then
        failwith "integer randomized closure-free changed-worker union mismatch";
      if I.get key random_native_result <> I.get key random_expected then
        failwith "integer randomized native-shaped worker union mismatch";
      if I.get key random_native_fuel_result <> I.get key random_expected then
        failwith "integer randomized native-shaped fuel-worker union mismatch";
      if I.get key random_native_inline_result <> I.get key random_expected then
        failwith "integer randomized inline native-worker union mismatch"
    done
  done;
  if IU.union_left_specialized left I.empty != left then
    failwith "integer empty-right certificate lost sharing"

let check_string () =
  let keys =
    [ ""; "a"; "ab"; "abc"; "b"; "ba"; "alphabet";
      Stdlib.String.make 1 '\000'; Stdlib.String.make 1 '\255';
      "long common prefix x";
      "long common prefix y" ]
  in
  let add_selected modulus tree =
    List.fold_left
      (fun current (index, key) ->
        if index mod modulus = 0 then S.set key index current else current)
      tree (List.mapi (fun index key -> index, key) keys)
  in
  let left = add_selected 2 S.empty in
  let right = add_selected 3 S.empty in
  let expected_left = S.union_left left right in
  let expected_right = S.union_right left right in
  let actual_left = SU.union_left_specialized left right in
  let actual_right = SU.union_right_specialized left right in
  let changed_left = SU.union_left_specialized_changed left right in
  let changed_result =
    match changed_left with S.Empty -> left | changed -> changed
  in
  let fuel_result = SU.union_left_specialized_changed_fuel_result left right in
  let native_result = SU.union_left_native_default left right in
  let native_fuel_result = SU.union_left_native_fuel_default left right in
  let native_inline_result = SU.union_left_native_fuel_inline_default left right in
  if native_result <> expected_left || native_fuel_result <> expected_left
     || native_inline_result <> expected_left then
    failwith "string native-shaped worker differs structurally from legacy union";
  List.iter
    (fun key ->
      if S.get key actual_left <> S.get key expected_left then
        failwith "string specialized left union mismatch";
      if S.get key actual_right <> S.get key expected_right then
        failwith "string specialized right union mismatch";
      if S.get key changed_result <> S.get key expected_left then
        failwith "string changed-worker union mismatch";
      if S.get key fuel_result <> S.get key expected_left then
        failwith "string closure-free changed-worker union mismatch";
      if S.get key native_result <> S.get key expected_left then
        failwith "string native-shaped worker union mismatch";
      if S.get key native_fuel_result <> S.get key expected_left then
        failwith "string native-shaped fuel-worker union mismatch";
      if S.get key native_inline_result <> S.get key expected_left then
        failwith "string inline native-worker union mismatch")
    keys;
  let subset = add_selected 2 S.empty in
  if SU.union_left_specialized_changed left subset <> S.Empty then
    failwith "string changed worker missed unchanged certificate";
  List.iter
    (fun (name, union) ->
      if union left S.empty != left then
        failwith ("string " ^ name ^ " lost empty-right root reuse");
      if union left subset != left then
        failwith ("string " ^ name ^ " lost subset root reuse");
      if union left left != left then
        failwith ("string " ^ name ^ " lost equal root reuse"))
    [ "native-shaped", SU.union_left_native_default;
      "native-shaped fuel", SU.union_left_native_fuel_default;
      "inline native-shaped fuel", SU.union_left_native_fuel_inline_default ];
  if changed_left = S.Empty then
    failwith "string changed worker missed fresh right bindings";
  let nested = S.set "ab" 2 (S.set "aa" 1 S.empty) in
  let enclosing = S.set "z" 3 nested in
  let nested_changed = SU.union_left_specialized_changed nested enclosing in
  let nested_result =
    match nested_changed with S.Empty -> nested | changed -> changed
  in
  if nested_changed = S.Empty || S.get "z" nested_result <> Some 3 then
    failwith "string changed worker dropped an outer sibling";
  for seed = 1 to 32 do
    let state = ref seed in
    let next () =
      state := ((!state * 1103515245) + 12345) land 0x3fffffff;
      !state
    in
    let rec add count tree =
      if count = 0 then tree
      else
        let key = Printf.sprintf "%03d" (next () mod 127) in
        add (count - 1) (S.set key (next ()) tree)
    in
    let random_left = add 48 S.empty in
    let random_right = add 48 S.empty in
    let random_changed = SU.union_left_specialized_changed random_left random_right in
    let random_result =
      match random_changed with S.Empty -> random_left | changed -> changed
    in
    let random_fuel_result =
      SU.union_left_specialized_changed_fuel_result random_left random_right
    in
    let random_native_result = SU.union_left_native_default random_left random_right in
    let random_native_fuel_result =
      SU.union_left_native_fuel_default random_left random_right
    in
    let random_native_inline_result =
      SU.union_left_native_fuel_inline_default random_left random_right
    in
    let random_expected = S.union_left random_left random_right in
    if random_native_result <> random_expected
       || random_native_fuel_result <> random_expected
       || random_native_inline_result <> random_expected then
      failwith "string randomized native-shaped worker differs structurally from legacy union";
    for key = 0 to 126 do
      let key = Printf.sprintf "%03d" key in
      if S.get key random_result <> S.get key random_expected then
        failwith "string randomized changed-worker union mismatch";
      if S.get key random_fuel_result <> S.get key random_expected then
        failwith "string randomized closure-free changed-worker union mismatch";
      if S.get key random_native_result <> S.get key random_expected then
        failwith "string randomized native-shaped worker union mismatch";
      if S.get key random_native_fuel_result <> S.get key random_expected then
        failwith "string randomized native-shaped fuel-worker union mismatch";
      if S.get key random_native_inline_result <> S.get key random_expected then
        failwith "string randomized inline native-worker union mismatch"
    done
  done;
  if SU.union_left_specialized left S.empty != left then
    failwith "string empty-right certificate lost sharing"

let check_native_payload_identity () =
  let integer_workers =
    [ "native-shaped", IU.union_left_native_default;
      "native-shaped fuel", IU.union_left_native_fuel_default;
      "inline native-shaped fuel", IU.union_left_native_fuel_inline_default ]
  in
  List.iter
    (fun (name, union) ->
      let preferred = ref 10 in
      let one_sided = ref 20 in
      let left = I.set 1 preferred I.empty in
      let right = I.set 2 one_sided (I.set 1 (ref 30) I.empty) in
      let result = union left right in
      let selected = match I.get 1 result with Some value -> value | None ->
        failwith ("integer " ^ name ^ " lost preferred binding") in
      let retained = match I.get 2 result with Some value -> value | None ->
        failwith ("integer " ^ name ^ " lost one-sided binding") in
      if selected != preferred || retained != one_sided then
        failwith ("integer " ^ name ^ " replaced mutable payloads");
      selected := 11;
      retained := 21;
      if !preferred <> 11 || !one_sided <> 21 then
        failwith ("integer " ^ name ^ " lost payload aliasing"))
    integer_workers;
  let string_workers =
    [ "native-shaped", SU.union_left_native_default;
      "native-shaped fuel", SU.union_left_native_fuel_default;
      "inline native-shaped fuel", SU.union_left_native_fuel_inline_default ]
  in
  List.iter
    (fun (name, union) ->
      let preferred = ref 10 in
      let one_sided = ref 20 in
      let left = S.set "a" preferred S.empty in
      let right = S.set "b" one_sided (S.set "a" (ref 30) S.empty) in
      let result = union left right in
      let selected = match S.get "a" result with Some value -> value | None ->
        failwith ("string " ^ name ^ " lost preferred binding") in
      let retained = match S.get "b" result with Some value -> value | None ->
        failwith ("string " ^ name ^ " lost one-sided binding") in
      if selected != preferred || retained != one_sided then
        failwith ("string " ^ name ^ " replaced mutable payloads");
      selected := 11;
      retained := 21;
      if !preferred <> 11 || !one_sided <> 21 then
        failwith ("string " ^ name ^ " lost payload aliasing"))
    string_workers

let () =
  check_integer ();
  check_string ();
  check_native_payload_identity ();
  print_endline "Patricia specialized-union oracle test: ok"
