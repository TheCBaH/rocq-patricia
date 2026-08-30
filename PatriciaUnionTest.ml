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
    match changed_left with None -> left | Some changed -> changed
  in
  for key = 1 to 64 do
    if I.get key actual_left <> I.get key expected_left then
      failwith "integer specialized left union mismatch";
    if I.get key actual_right <> I.get key expected_right then
      failwith "integer specialized right union mismatch";
    if I.get key changed_result <> I.get key expected_left then
      failwith "integer changed-worker union mismatch"
  done;
  let subset = build (fun key -> key mod 2 = 0) (fun key -> -key) 64 I.empty in
  if IU.union_left_specialized_changed left subset <> None then
    failwith "integer changed worker missed unchanged certificate";
  if changed_left = None then
    failwith "integer changed worker missed fresh right bindings";
  let nested = I.set 3 30 (I.set 1 10 I.empty) in
  let enclosing = I.set 8 80 nested in
  let nested_changed = IU.union_left_specialized_changed nested enclosing in
  let nested_result =
    match nested_changed with None -> nested | Some changed -> changed
  in
  if nested_changed = None || I.get 8 nested_result <> Some 80 then
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
      match random_changed with None -> random_left | Some changed -> changed
    in
    let random_expected = I.union_left random_left random_right in
    for key = 1 to 127 do
      if I.get key random_result <> I.get key random_expected then
        failwith "integer randomized changed-worker union mismatch"
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
    match changed_left with None -> left | Some changed -> changed
  in
  List.iter
    (fun key ->
      if S.get key actual_left <> S.get key expected_left then
        failwith "string specialized left union mismatch";
      if S.get key actual_right <> S.get key expected_right then
        failwith "string specialized right union mismatch";
      if S.get key changed_result <> S.get key expected_left then
        failwith "string changed-worker union mismatch")
    keys;
  let subset = add_selected 2 S.empty in
  if SU.union_left_specialized_changed left subset <> None then
    failwith "string changed worker missed unchanged certificate";
  if changed_left = None then
    failwith "string changed worker missed fresh right bindings";
  let nested = S.set "ab" 2 (S.set "aa" 1 S.empty) in
  let enclosing = S.set "z" 3 nested in
  let nested_changed = SU.union_left_specialized_changed nested enclosing in
  let nested_result =
    match nested_changed with None -> nested | Some changed -> changed
  in
  if nested_changed = None || S.get "z" nested_result <> Some 3 then
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
      match random_changed with None -> random_left | Some changed -> changed
    in
    let random_expected = S.union_left random_left random_right in
    for key = 0 to 126 do
      let key = Printf.sprintf "%03d" key in
      if S.get key random_result <> S.get key random_expected then
        failwith "string randomized changed-worker union mismatch"
    done
  done;
  if SU.union_left_specialized left S.empty != left then
    failwith "string empty-right certificate lost sharing"

let () =
  check_integer ();
  check_string ();
  print_endline "Patricia specialized-union oracle test: ok"
