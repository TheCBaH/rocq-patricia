open Patricia

let positive_of_int n =
  if n <= 0 then invalid_arg "positive_of_int" else n

let fail round operation key expected actual =
  failwith
    (Printf.sprintf
       "round %d, %s, key %d: expected %s, got %s"
       round operation key
       (match expected with None -> "None" | Some v -> string_of_int v)
       (match actual with None -> "None" | Some v -> string_of_int v))

let lookup table key = Hashtbl.find_opt table key

let merge_options left right =
  match left, right with
  | None, None -> None
  | Some x, None -> Some x
  | None, Some y -> Some y
  | Some x, Some y -> Some (x + y)

let merge_filtering left right =
  match left, right with
  | None, None -> None
  | Some x, None -> if x mod 3 = 0 then None else Some (x + 1)
  | None, Some y -> if y mod 5 = 0 then None else Some (y - 1)
  | Some x, Some y -> if (x + y) mod 7 = 0 then None else Some (x - y)

let check_array_get round operation reference tree =
  for key = 1 to Array.length reference - 1 do
    let actual = get (positive_of_int key) tree in
    if actual <> reference.(key) then
      fail round operation key reference.(key) actual
  done

let check_int_structure round tree =
  let rec check parent_mask = function
    | Empty -> []
    | Leaf (key, _) -> [key]
    | Branch (prefix, mask, left, right) ->
        if mask < 0 then
          failwith (Printf.sprintf "round %d: negative integer mask" round);
        (match parent_mask with
         | Some parent when mask >= parent ->
             failwith
               (Printf.sprintf "round %d: integer masks do not decrease" round)
         | _ -> ());
        let left_keys = check (Some mask) left in
        let right_keys = check (Some mask) right in
        if left_keys = [] || right_keys = [] then
          failwith (Printf.sprintf "round %d: empty child below Branch" round);
        List.iter
          (fun key ->
             if not (PatriciaBits.matches_prefix key prefix mask)
                || not (PatriciaBits.zero_bit key mask) then
               failwith
                 (Printf.sprintf "round %d: invalid integer left route" round))
          left_keys;
        List.iter
          (fun key ->
             if not (PatriciaBits.matches_prefix key prefix mask)
                || PatriciaBits.zero_bit key mask then
               failwith
                 (Printf.sprintf "round %d: invalid integer right route" round))
          right_keys;
        left_keys @ right_keys
  in
  ignore (check None tree)

let check_array_elements round reference tree =
  let bindings = elements tree in
  let keys = List.map fst bindings in
  if keys <> List.sort_uniq compare keys then
    failwith (Printf.sprintf "round %d: elements are not strictly ordered" round);
  List.iter
    (fun (key, value) ->
       if reference.(key) <> Some value then
         fail round "elements" key reference.(key) (Some value))
    bindings

let check_int_table round operation keys reference tree =
  List.iter
    (fun key ->
       let actual = get (positive_of_int key) tree in
       let expected = lookup reference key in
       if actual <> expected then fail round operation key expected actual)
    keys;
  let actual = elements tree in
  let actual_keys = List.map fst actual in
  if actual_keys <> List.sort_uniq compare actual_keys then
    failwith (Printf.sprintf "round %d: wide elements are not strictly ordered" round);
  if List.length actual <> Hashtbl.length reference then
    failwith (Printf.sprintf "round %d: wide elements have the wrong size" round);
  List.iter
    (fun (key, value) ->
       match lookup reference key with
       | Some expected when expected = value -> ()
       | expected -> fail round (operation ^ " elements") key expected (Some value))
    actual;
  check_int_structure round tree

let check_int_wide_keys () =
  let high_bit = Sys.int_size - 2 in
  let powers = List.init (high_bit + 1) (fun bit -> 1 lsl bit) in
  let keys = List.sort_uniq compare
      (max_int :: (max_int - 1) :: (max_int - 2) :: powers) in
  for round = 1 to 80 do
    let left_ref = Hashtbl.create 128 in
    let right_ref = Hashtbl.create 128 in
    let left = ref empty in
    let right = ref empty in
    for _ = 1 to 160 do
      let update tree reference =
        let key = List.nth keys (Random.int (List.length keys)) in
        if Random.bool () then begin
          let value = Random.int 10_000 in
          Hashtbl.replace reference key value;
          tree := set (positive_of_int key) value !tree
        end else begin
          Hashtbl.remove reference key;
          tree := remove (positive_of_int key) !tree
        end
      in
      update left left_ref;
      update right right_ref
    done;
    check_int_table round "wide left" keys left_ref !left;
    check_int_table round "wide right" keys right_ref !right;
    let check_merge operation f =
      let expected = Hashtbl.create 128 in
      List.iter
        (fun key ->
           match f (lookup left_ref key) (lookup right_ref key) with
           | None -> ()
           | Some value -> Hashtbl.replace expected key value)
        keys;
      check_int_table round operation keys expected (combine f !left !right)
    in
    check_merge "wide combine" merge_options;
    check_merge "wide filtering combine" merge_filtering;
    let expected_left = Hashtbl.copy right_ref in
    Hashtbl.iter (Hashtbl.replace expected_left) left_ref;
    check_int_table round "wide union_left" keys expected_left (union_left !left !right);
    let expected_right = Hashtbl.copy left_ref in
    Hashtbl.iter (Hashtbl.replace expected_right) right_ref;
    check_int_table round "wide union_right" keys expected_right (union_right !left !right)
  done

module S = StringPatricia

let string_of_bytes bytes =
  Bytes.init (Array.length bytes) (fun i -> Char.chr bytes.(i))
  |> Bytes.unsafe_to_string

let check_string_bits () =
  let pack position =
    ((position / 9) lsl 4) lor (position mod 9)
  in
  let reference_bit string position =
    let byte = position / 9 and tag = position mod 9 in
    if byte >= Stdlib.String.length string then false
    else if tag = 0 then true
    else (Char.code (Stdlib.String.unsafe_get string byte) land (1 lsl (8 - tag))) <> 0
  in
  let reference_first_diff left right =
    let limit = 9 * max (Stdlib.String.length left) (Stdlib.String.length right) + 1 in
    let rec scan position =
      if position = limit then None
      else if reference_bit left position <> reference_bit right position
      then Some (pack position)
      else scan (position + 1)
    in
    scan 0
  in
  let reference_agrees_before left right split =
    let rec scan position =
      position = split
      || (reference_bit left position = reference_bit right position
          && scan (position + 1))
    in
    scan 0
  in
  let check left right =
    let expected = reference_first_diff left right in
    let actual = StringBits.first_diff left right in
    if actual <> expected then
      failwith
        (Printf.sprintf "first_diff %S %S: expected %s, got %s"
           left right
           (match expected with None -> "None" | Some split -> string_of_int split)
           (match actual with None -> "None" | Some split -> string_of_int split));
    let limit = 9 * max (Stdlib.String.length left) (Stdlib.String.length right) + 1 in
    for split = 0 to limit do
      let expected = reference_agrees_before left right split in
      let packed_split = pack split in
      let actual = StringBits.agrees_before_bounded left right packed_split in
      if actual <> expected then
        failwith
          (Printf.sprintf
             "agrees_before_bounded %S %S %d: expected %b, got %b"
             left right packed_split expected actual)
    done
  in
  for left = 0 to 255 do
    for right = 0 to 255 do
      check (Stdlib.String.make 1 (Char.chr left)) (Stdlib.String.make 1 (Char.chr right))
    done
  done;
  List.iter
    (fun (left, right) -> check left right; check right left)
    ["", ""; "", "\000"; "a", "a\000"; "prefix", "prefix\255";
     Stdlib.String.make 192 'p', Stdlib.String.make 192 'p' ^ "\128"]

let check_string_structure round tree =
  let next_token token =
    if token land 15 = 8 then ((token lsr 4) + 1) lsl 4 else token + 1
  in
  let rec agrees sample key split bit =
    if bit = split then true
    else if StringBits.bit_at sample bit <> StringBits.bit_at key bit then false
    else agrees sample key split (next_token bit)
  in
  let rec check parent_split = function
    | S.Empty -> []
    | S.Leaf (key, _) -> [key]
    | S.Branch (sample, split, left, right) ->
        if split < 0 then
          failwith (Printf.sprintf "round %d: negative string split" round);
        (match parent_split with
         | Some parent when split <= parent ->
             failwith
               (Printf.sprintf "round %d: string splits do not increase" round)
         | _ -> ());
        let left_keys = check (Some split) left in
        let right_keys = check (Some split) right in
        if left_keys = [] || right_keys = [] then
          failwith (Printf.sprintf "round %d: empty child below string Branch" round);
        if not (List.mem sample (left_keys @ right_keys)) then
          failwith (Printf.sprintf "round %d: string sample is not a binding" round);
        List.iter
          (fun key ->
             if not (agrees sample key split 0)
                || StringBits.bit_at key split then
               failwith
                 (Printf.sprintf "round %d: invalid string left route" round))
          left_keys;
        List.iter
          (fun key ->
             if not (agrees sample key split 0)
                || not (StringBits.bit_at key split) then
               failwith
                 (Printf.sprintf "round %d: invalid string right route" round))
          right_keys;
        left_keys @ right_keys
  in
  ignore (check None tree)

let check_string_table round operation keys reference tree =
  List.iter
    (fun key ->
       let actual = S.get key tree in
       let expected = lookup reference key in
       if actual <> expected then
         failwith (Printf.sprintf "string round %d, %s, key %S" round operation key))
    keys;
  let actual = S.elements tree in
  let actual_keys = List.map fst actual in
  if actual_keys <> List.sort_uniq Stdlib.String.compare actual_keys then
    failwith (Printf.sprintf "string round %d: elements are not byte-lexicographic" round);
  if List.length actual_keys <> List.length (List.sort_uniq compare actual_keys) then
    failwith (Printf.sprintf "string round %d: duplicate element key" round);
  if List.length actual <> Hashtbl.length reference then
    failwith (Printf.sprintf "string round %d: wrong element count" round);
  List.iter
    (fun (key, value) ->
       if lookup reference key <> Some value then
         failwith (Printf.sprintf "string round %d: wrong element binding" round))
    actual;
  check_string_structure round tree

let check_string_keys () =
  let random_bytes length =
    Bytes.init length (fun _ -> Char.chr (Random.int 256)) |> Bytes.unsafe_to_string
  in
  let prefix = Stdlib.String.make 192 'p' in
  let keys = List.sort_uniq compare
      ([ ""; "a"; "alpha"; "alphabet"; "beta"; "z"; "\000"; "a\000b";
         string_of_bytes [| 0x80 |]; string_of_bytes [| 0xff |];
         string_of_bytes [| 0; 0xff; 0x80; 1 |];
         prefix; prefix ^ "\000"; prefix ^ "\255" ]
       @ List.init 96 (fun i -> random_bytes (i mod 24))) in
  for round = 1 to 300 do
    let left_ref = Hashtbl.create 128 in
    let right_ref = Hashtbl.create 128 in
    let left = ref S.empty in
    let right = ref S.empty in
    for _ = 1 to 120 do
      let update tree reference =
        let key = List.nth keys (Random.int (List.length keys)) in
        if Random.bool () then begin
          let value = Random.int 10_000 in
          Hashtbl.replace reference key value;
          tree := S.set key value !tree
        end else begin
          Hashtbl.remove reference key;
          tree := S.remove key !tree
        end
      in
      update left left_ref;
      update right right_ref
    done;
    check_string_table round "left updates" keys left_ref !left;
    check_string_table round "right updates" keys right_ref !right;
    let rebuilt_left =
      List.fold_left
        (fun tree (key, value) -> S.set key value tree)
        S.empty (List.rev (S.elements !left))
    in
    if not (S.beq ( = ) !left rebuilt_left) then
      failwith
        (Printf.sprintf
           "string round %d: beq rejected extensionally equal trees" round);
    let expected_equal =
      List.for_all
        (fun key -> lookup left_ref key = lookup right_ref key)
        keys
    in
    if S.beq ( = ) !left !right <> expected_equal then
      failwith
        (Printf.sprintf "string round %d: beq disagrees with lookup" round);
    let check_merge operation f =
      let expected = Hashtbl.create 128 in
      List.iter
        (fun key ->
           match f (lookup left_ref key) (lookup right_ref key) with
           | None -> ()
           | Some value -> Hashtbl.replace expected key value)
        keys;
      check_string_table round operation keys expected (S.combine f !left !right)
    in
    check_merge "combine" merge_options;
    check_merge "filtering combine" merge_filtering;
    let expected_left = Hashtbl.copy right_ref in
    Hashtbl.iter (Hashtbl.replace expected_left) left_ref;
    check_string_table round "union_left" keys expected_left (S.union_left !left !right);
    let expected_right = Hashtbl.copy left_ref in
    Hashtbl.iter (Hashtbl.replace expected_right) right_ref;
    check_string_table round "union_right" keys expected_right (S.union_right !left !right)
  done

let () =
  Random.init 0x504154;
  check_string_bits ();
  for round = 1 to 250 do
    let left_ref = Array.make 256 None in
    let right_ref = Array.make 256 None in
    let left = ref empty in
    let right = ref empty in
    for _ = 1 to 100 do
      let key = 1 + Random.int 255 in
      let value = Random.int 10_000 in
      if Random.bool () then begin
        left := set (positive_of_int key) value !left;
        left_ref.(key) <- Some value
      end else begin
        left := remove (positive_of_int key) !left;
        left_ref.(key) <- None
      end;
      let key = 1 + Random.int 255 in
      let value = Random.int 10_000 in
      if Random.bool () then begin
        right := set (positive_of_int key) value !right;
        right_ref.(key) <- Some value
      end else begin
        right := remove (positive_of_int key) !right;
        right_ref.(key) <- None
      end
    done;
    check_array_get round "left updates" left_ref !left;
    check_array_get round "right updates" right_ref !right;
    check_array_elements round left_ref !left;
    check_int_structure round !left;
    check_int_structure round !right;
    let merged_ref =
      Array.init 256 (fun key -> merge_options left_ref.(key) right_ref.(key))
    in
    let merged = combine merge_options !left !right in
    check_array_get round "combine" merged_ref merged;
    check_int_structure round merged;
    check_array_get round "union_left"
      (Array.init 256 (fun key ->
           match left_ref.(key) with Some _ as value -> value | None -> right_ref.(key)))
      (union_left !left !right);
    check_array_get round "union_right"
      (Array.init 256 (fun key ->
           match right_ref.(key) with Some _ as value -> value | None -> left_ref.(key)))
      (union_right !left !right)
  done;
  check_int_wide_keys ();
  check_string_keys ();
  print_endline "Patricia randomized oracle test: ok"
