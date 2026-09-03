open PatriciaInternal

let union_left_specialized = PatriciaUnion.union_left_specialized
let union_right_specialized = PatriciaUnion.union_right_specialized

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
    check_int_table round "wide specialized union_left" keys expected_left
      (union_left_specialized !left !right);
    let expected_right = Hashtbl.copy left_ref in
    Hashtbl.iter (Hashtbl.replace expected_right) right_ref;
    check_int_table round "wide union_right" keys expected_right (union_right !left !right);
    check_int_table round "wide specialized union_right" keys expected_right
      (union_right_specialized !left !right)
  done

module S = StringPatriciaInternal
module SU = StringPatriciaUnion

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
  let check_packed_bit_guards string =
    for byte = 0 to Stdlib.String.length string + 2 do
      for tag = 0 to 15 do
        let token = (byte lsl 4) lor tag in
        let expected =
          if tag <= 8 then reference_bit string ((9 * byte) + tag) else false
        in
        if StringBits.bit_at string token <> expected then
          failwith
            (Printf.sprintf "packed bit_at guard %S byte %d tag %d"
               string byte tag)
      done
    done
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
    (match actual with
     | Some token when token land 15 > 8 ->
         failwith (Printf.sprintf "first_diff returned invalid tag %d" token)
     | _ -> ());
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
    (fun (left, right) ->
       check_packed_bit_guards left;
       check_packed_bit_guards right;
       check left right; check right left)
    ["", ""; "", "\000"; "a", "a\000"; "prefix", "prefix\255";
     Stdlib.String.make 192 'p', Stdlib.String.make 192 'p' ^ "\128"]

(* The optimized [S.set] is the exception-based realizer from
   [PatriciaExtract.v], whereas [S.set_one_descent] is ordinary extraction of
   its proved source counterpart.  Random traces below exercise both, but this
   compact deterministic suite makes every byte bit and the continuation token
   a fresh-key split at byte zero and after several common-prefix lengths.
   Every insertion order and every intermediate prefix is checked structurally,
   so a misplaced exception catch or bubble rebuild is visible even when lookup
   results happen to agree. *)
let check_string_set_realizer_routes () =
  let rec permutations = function
    | [] -> [ [] ]
    | item :: rest ->
        List.concat_map
          (fun permutation ->
             let rec insert_everywhere before = function
               | [] -> [List.rev_append before [item]]
               | (head :: tail as after) ->
                   List.rev_append before (item :: after)
                   :: insert_everywhere (head :: before) tail
             in
             insert_everywhere [] permutation)
          (permutations rest)
  in
  let check_equal label native source =
    if native <> source then
      failwith ("string set realizer differs structurally: " ^ label)
  in
  List.iter
    (fun prefix_length ->
       let prefix = Stdlib.String.make prefix_length '\001' in
       for bit = 0 to 7 do
         let byte = Stdlib.String.make 1 (Char.chr (1 lsl bit)) in
         (* [prefix ^ "\\000"] and [prefix ^ byte] differ at this exact byte
            bit.  The extension of NUL differs at its continuation marker; the
            final byte makes the fresh split bubble above an already-built
            inner branch in several orders. *)
         let keys =
           [prefix ^ "\000"; prefix ^ byte; prefix ^ "\000\255"; prefix ^ "\255"]
         in
         List.iteri
           (fun order_index order ->
              let native = ref S.empty and source = ref S.empty in
              check_equal
                (Printf.sprintf "prefix %d bit %d order %d empty"
                   prefix_length bit order_index)
                !native !source;
              List.iteri
                (fun depth key ->
                   native := S.set key ((depth * 100) + bit) !native;
                   source := S.set_one_descent key ((depth * 100) + bit) !source;
                   check_equal
                     (Printf.sprintf "prefix %d bit %d order %d depth %d"
                        prefix_length bit order_index depth)
                     !native !source;
                   List.iteri
                     (fun update_index update_key ->
                        native := S.set update_key ((depth * 1000) + update_index) !native;
                        source :=
                          S.set_one_descent update_key ((depth * 1000) + update_index)
                            !source;
                        check_equal
                          (Printf.sprintf
                             "prefix %d bit %d order %d depth %d update %d"
                             prefix_length bit order_index depth update_index)
                          !native !source)
                     keys)
                order)
           (permutations keys)
       done)
    [0; 1; 2; 31]

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
    (* [set_one_descent] is extracted without a Patricia-specific OCaml
       realizer.  Keep a parallel random oracle here so its ordinary
       extraction is checked independently of the optimized [set] path. *)
    let left_one_descent = ref S.empty in
    let right_one_descent = ref S.empty in
    for _ = 1 to 120 do
      let update tree one_descent reference =
        let key = List.nth keys (Random.int (List.length keys)) in
        if Random.bool () then begin
          let value = Random.int 10_000 in
          Hashtbl.replace reference key value;
          tree := S.set key value !tree;
          one_descent := S.set_one_descent key value !one_descent
        end else begin
          Hashtbl.remove reference key;
          tree := S.remove key !tree;
          one_descent := S.remove key !one_descent
        end
      in
      update left left_one_descent left_ref;
      update right right_one_descent right_ref
    done;
    check_string_table round "left updates" keys left_ref !left;
    check_string_table round "right updates" keys right_ref !right;
    check_string_table round "left one-descent updates" keys left_ref
      !left_one_descent;
    check_string_table round "right one-descent updates" keys right_ref
      !right_one_descent;
    if !left <> !left_one_descent then
      failwith
        (Printf.sprintf
           "string round %d: native set differs structurally from one-descent worker"
           round);
    if !right <> !right_one_descent then
      failwith
        (Printf.sprintf
           "string round %d: native set differs structurally from one-descent worker"
           round);
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
    check_string_table round "specialized union_left" keys expected_left
      (SU.union_left_specialized !left !right);
    let expected_right = Hashtbl.copy left_ref in
    Hashtbl.iter (Hashtbl.replace expected_right) right_ref;
    check_string_table round "union_right" keys expected_right (S.union_right !left !right);
    check_string_table round "specialized union_right" keys expected_right
      (SU.union_right_specialized !left !right)
  done

(** Exercise every root relationship selected by the direct-string merge:
    equal roots, either tree containing the other root, and disjoint prefixes.
    Random workloads reach these cases, but these small examples make their
    coverage deterministic and guard the dispatch conditions themselves. *)
let check_string_merge_shapes () =
  let tree bindings =
    List.fold_left (fun result (key, value) -> S.set key value result) S.empty bindings
  in
  let table bindings =
    let result = Hashtbl.create 8 in
    List.iter (fun (key, value) -> Hashtbl.replace result key value) bindings;
    result
  in
  let root_shape left right =
    match left, right with
    | S.Branch (sample_left, split_left, _, _),
      S.Branch (sample_right, split_right, _, _) ->
        if split_left = split_right
           && StringBits.agrees_before_bounded sample_left sample_right split_left then
          "equal"
        else if split_left < split_right
                && StringBits.agrees_before_bounded sample_left sample_right split_left then
          "left contains right"
        else if split_right < split_left
                && StringBits.agrees_before_bounded sample_left sample_right split_right then
          "right contains left"
        else "disjoint"
    | _ -> failwith "string merge-shape fixture did not build two branches"
  in
  let cases =
    [ "equal", ["a0", 10; "b0", 20], ["a1", 30; "b1", 40];
      "left contains right", ["a0", 10; "b0", 20], ["a1", 30; "a2", 40];
      "right contains left", ["a1", 10; "a2", 20], ["a0", 30; "b0", 40];
      "disjoint", ["a0", 10; "a1", 20], ["b0", 30; "b1", 40] ]
  in
  List.iteri
    (fun round (expected_shape, left_bindings, right_bindings) ->
       let left = tree left_bindings and right = tree right_bindings in
       let actual_shape = root_shape left right in
       if actual_shape <> expected_shape then
         failwith
           (Printf.sprintf "string merge shape: expected %s, got %s"
              expected_shape actual_shape);
       let left_ref = table left_bindings and right_ref = table right_bindings in
       let keys = List.sort_uniq compare
           (List.map fst left_bindings @ List.map fst right_bindings) in
       let expected = table [] in
       List.iter
         (fun key ->
            match merge_options (lookup left_ref key) (lookup right_ref key) with
            | None -> ()
            | Some value -> Hashtbl.replace expected key value)
         keys;
       check_string_table (-100 - round) (expected_shape ^ " combine") keys expected
         (S.combine merge_options left right);
       let expected_filtered = table [] in
       List.iter
         (fun key ->
            match merge_filtering (lookup left_ref key) (lookup right_ref key) with
            | None -> ()
            | Some value -> Hashtbl.replace expected_filtered key value)
         keys;
       check_string_table (-100 - round) (expected_shape ^ " filtering combine") keys
         expected_filtered (S.combine merge_filtering left right);
       let expected_left = Hashtbl.copy right_ref in
       Hashtbl.iter (Hashtbl.replace expected_left) left_ref;
       check_string_table (-100 - round) (expected_shape ^ " union_left") keys
         expected_left (S.union_left left right);
       check_string_table (-100 - round) (expected_shape ^ " specialized union_left")
         keys expected_left (SU.union_left_specialized left right);
       let expected_right = Hashtbl.copy left_ref in
       Hashtbl.iter (Hashtbl.replace expected_right) right_ref;
       check_string_table (-100 - round) (expected_shape ^ " union_right") keys
         expected_right (S.union_right left right);
       check_string_table (-100 - round) (expected_shape ^ " specialized union_right")
         keys expected_right (SU.union_right_specialized left right))
    cases

let check_abstract_interfaces () =
  let module I = PatriciaMap in
  if I.Key.of_int min_int <> None || I.Key.of_int (-1) <> None
     || I.Key.of_int 0 <> None then
    failwith "abstract integer interface accepted a non-positive key";
  let key = I.Key.of_int_exn in
  let one = key 1 and largest = key max_int in
  if I.Key.to_int one <> 1 || I.Key.to_int largest <> max_int
     || not (I.Key.equal one (key 1))
     || I.Key.compare one largest >= 0 then
    failwith "abstract integer key conversion failed";
  let raised =
    try
      ignore (key 0);
      false
    with Invalid_argument _ -> true
  in
  if not raised then
    failwith "abstract integer exception conversion accepted zero";
  let integers : int I.t =
    I.empty
    |> I.set (key 7) 70
    |> I.set (key 3) 30
    |> I.set (key 7) 71
  in
  if I.is_empty integers || not (I.mem (key 7) integers)
     || I.get (key 7) integers <> Some 71
     || I.get largest (I.singleton largest 99) <> Some 99 then
    failwith "abstract integer interface update failed";
  let bulk = I.of_list [key 7, 70; key 3, 30; key 7, 71] in
  if I.get (key 7) bulk <> Some 70 || I.get (key 3) bulk <> Some 30
     || I.get largest bulk <> None then
    failwith "abstract integer bulk loading failed";
  let mapped = I.map (fun key value -> I.Key.to_int key + value) integers in
  let filtered = I.map_filter
      (fun current value -> if I.Key.equal current (key 3) then None else Some value)
      mapped in
  let elements =
    List.map (fun (current, value) -> I.Key.to_int current, value)
      (I.elements filtered)
  in
  if elements <> [7, 78]
     || I.fold (fun count _ _ -> count + 1) filtered 0 <> 1 then
    failwith "abstract integer interface traversal failed";
  let combiner : (int, int, int) I.combiner = {
    left_only = (fun value -> Some (value + 1));
    right_only = (fun value -> Some (-value));
    both = (fun _ _ -> None);
  } in
  let right =
    I.empty
    |> I.set (key 7) 700
    |> I.set (key 9) 90
  in
  let combined = I.combine combiner filtered right in
  let elements =
    List.map (fun (current, value) -> I.Key.to_int current, value)
      (I.elements combined)
  in
  if elements <> [9, -90]
     || not (I.beq ( = ) combined (I.singleton (key 9) (-90)))
     || not (I.is_empty (I.remove (key 9) combined)) then
    failwith "abstract integer interface combiner contract failed";
  let module S = StringPatriciaMap in
  let strings : int S.t =
    S.empty
    |> S.set "" 0
    |> S.set "a\000b" 1
    |> S.set "\255" 2
    |> S.set "a\000b" 3
  in
  if S.is_empty strings || not (S.mem "" strings)
     || S.get "a\000b" strings <> Some 3 then
    failwith "abstract string interface update failed";
  let bulk = S.of_list ["a\000b", 10; "", 0; "a\000b", 11] in
  if S.get "a\000b" bulk <> Some 10 || S.get "" bulk <> Some 0
     || S.get "missing" bulk <> None then
    failwith "abstract string bulk loading failed";
  let mapped = S.map (fun key value -> Stdlib.String.length key + value) strings in
  let filtered = S.map_filter
      (fun key value -> if key = "" then None else Some value) mapped in
  if S.fold (fun count _ _ -> count + 1) filtered 0 <> 2 then
    failwith "abstract string interface traversal failed";
  let combiner : (int, int, int) S.combiner = {
    left_only = (fun value -> Some (value + 1));
    right_only = (fun value -> Some (-value));
    both = (fun _ _ -> None);
  } in
  let right = S.empty |> S.set "a\000b" 10 |> S.set "z" 9 in
  let combined = S.combine combiner filtered right in
  if S.get "z" combined <> Some (-9)
     || S.get "a\000b" combined <> None
     || S.get "\255" combined <> Some 4
     || S.fold (fun count _ _ -> count + 1) combined 0 <> 2
     || S.get "z" (S.remove "z" combined) <> None then
    failwith "abstract string interface combiner contract failed"

(* Values are intentionally opaque to the Patricia algorithms.  Exercise
   biased union with mutable payloads so this test cannot accidentally rely
   on polymorphic value equality: overlapping bindings must select the exact
   preferred payload object, while one-sided bindings retain their object. *)
let check_mutable_union_payloads () =
  let require_same label expected = function
    | Some actual when actual == expected -> ()
    | _ -> failwith (label ^ ": selected the wrong payload object")
  in
  let integer_left = ref 10 and integer_right = ref 20 and integer_only = ref 30 in
  let integer_left_tree = empty |> set 1 integer_left |> set 3 integer_only in
  let integer_right_tree = empty |> set 1 integer_right |> set 2 integer_right in
  let integer_left_union = union_left integer_left_tree integer_right_tree in
  let integer_right_union = union_right integer_left_tree integer_right_tree in
  require_same "integer union_left overlap" integer_left (get 1 integer_left_union);
  require_same "integer union_left one-sided" integer_right (get 2 integer_left_union);
  require_same "integer union_right overlap" integer_right (get 1 integer_right_union);
  require_same "integer union_right one-sided" integer_only (get 3 integer_right_union);
  integer_left := 11;
  (match get 1 integer_left_union with
   | Some cell when !cell = 11 -> ()
   | _ -> failwith "integer union_left lost mutable payload identity");
  let string_left = ref 40 and string_right = ref 50 and string_only = ref 60 in
  let string_left_tree = S.empty |> S.set "a" string_left |> S.set "c" string_only in
  let string_right_tree = S.empty |> S.set "a" string_right |> S.set "b" string_right in
  let string_left_union = S.union_left string_left_tree string_right_tree in
  let string_right_union = S.union_right string_left_tree string_right_tree in
  require_same "string union_left overlap" string_left (S.get "a" string_left_union);
  require_same "string union_left one-sided" string_right (S.get "b" string_left_union);
  require_same "string union_right overlap" string_right (S.get "a" string_right_union);
  require_same "string union_right one-sided" string_only (S.get "c" string_right_union);
  string_right := 51;
  match S.get "a" string_right_union with
  | Some cell when !cell = 51 -> ()
  | _ -> failwith "string union_right lost mutable payload identity"

(* The public native unions intentionally retain the first argument's root
   whenever the second input adds no binding.  Keep this allocation/sharing
   behavior under the ordinary deterministic test gate, separately from the
   semantic tests above. *)
let check_union_root_reuse () =
  let integer_tree = empty |> set 1 10 |> set 3 30 in
  let integer_subset = empty |> set 1 99 in
  if union_left integer_tree empty != integer_tree then
    failwith "integer union_left did not reuse its empty-right root";
  if union_left integer_tree integer_subset != integer_tree then
    failwith "integer union_left did not reuse its subset root";
  let string_tree = S.empty |> S.set "a" 10 |> S.set "c" 30 in
  let string_subset = S.empty |> S.set "a" 99 in
  if S.union_left string_tree S.empty != string_tree then
    failwith "string union_left did not reuse its empty-right root";
  if S.union_left string_tree string_subset != string_tree then
    failwith "string union_left did not reuse its subset root"

let () =
  Random.init 0x504154;
  check_abstract_interfaces ();
  check_mutable_union_payloads ();
  check_union_root_reuse ();
  check_string_bits ();
  check_string_set_realizer_routes ();
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
    check_array_get round "specialized union_left"
      (Array.init 256 (fun key ->
           match left_ref.(key) with Some _ as value -> value | None -> right_ref.(key)))
      (union_left_specialized !left !right);
    check_array_get round "union_right"
      (Array.init 256 (fun key ->
           match right_ref.(key) with Some _ as value -> value | None -> left_ref.(key)))
      (union_right !left !right);
    check_array_get round "specialized union_right"
      (Array.init 256 (fun key ->
           match right_ref.(key) with Some _ as value -> value | None -> left_ref.(key)))
      (union_right_specialized !left !right)
  done;
  check_int_wide_keys ();
  check_string_merge_shapes ();
  check_string_keys ();
  print_endline "Patricia randomized oracle test: ok"
