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
  for key = 1 to 64 do
    if I.get key actual_left <> I.get key expected_left then
      failwith "integer specialized left union mismatch";
    if I.get key actual_right <> I.get key expected_right then
      failwith "integer specialized right union mismatch"
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
  List.iter
    (fun key ->
      if S.get key actual_left <> S.get key expected_left then
        failwith "string specialized left union mismatch";
      if S.get key actual_right <> S.get key expected_right then
        failwith "string specialized right union mismatch")
    keys;
  if SU.union_left_specialized left S.empty != left then
    failwith "string empty-right certificate lost sharing"

let () =
  check_integer ();
  check_string ();
  print_endline "Patricia specialized-union oracle test: ok"
