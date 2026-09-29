(* Differential checks between the optimized native extraction and a backend
   generated directly from the executable Rocq definitions. *)

module Integer_native = PatriciaInternal
module Integer_reference = Patricia_reference.Patricia
module String_native = StringPatriciaInternal
module String_reference = Patricia_reference.StringPatricia
module String_bits_native = StringBits
module String_bits_reference = Patricia_reference.StringBits

let fail context =
  failwith ("Patricia extraction differential mismatch: " ^ context)

let sorted_bindings bindings = List.sort Stdlib.compare bindings

let check_integer_map context native reference =
  if sorted_bindings (Integer_native.elements native)
     <> sorted_bindings (Integer_reference.elements reference) then
    fail (context ^ " integer bindings");
  for key = 1 to 192 do
    if Integer_native.get key native <> Integer_reference.get key reference then
      fail (context ^ " integer lookup");
    if Integer_native.mem key native <> Integer_reference.mem key reference then
      fail (context ^ " integer membership")
  done

let check_string_map context keys native reference =
  if sorted_bindings (String_native.elements native)
     <> sorted_bindings (String_reference.elements reference) then
    fail (context ^ " string bindings");
  List.iter
    (fun key ->
       if String_native.get key native <> String_reference.get key reference then
         fail (context ^ " string lookup");
       if String_native.mem key native <> String_reference.mem key reference then
         fail (context ^ " string membership"))
    keys

let combine_values left right =
  match left, right with
  | None, None -> None
  | Some value, None -> if value mod 3 = 0 then None else Some (value + 1)
  | None, Some value -> if value mod 5 = 0 then None else Some (value - 1)
  | Some left_value, Some right_value ->
      if (left_value + right_value) mod 7 = 0
      then None
      else Some (left_value - right_value)

let check_integer_operations () =
  for round = 1 to 100 do
    let native_left = ref Integer_native.empty in
    let reference_left = ref Integer_reference.empty in
    let native_right = ref Integer_native.empty in
    let reference_right = ref Integer_reference.empty in
    for step = 1 to 100 do
      let key = 1 + Random.int 191 in
      let value = Random.int 10_000 in
      if Random.bool () then begin
        native_left := Integer_native.set key value !native_left;
        reference_left := Integer_reference.set key value !reference_left
      end else begin
        native_right := Integer_native.set key value !native_right;
        reference_right := Integer_reference.set key value !reference_right
      end;
      if step mod 7 = 0 then begin
        let removed = 1 + Random.int 191 in
        native_left := Integer_native.remove removed !native_left;
        reference_left := Integer_reference.remove removed !reference_left
      end
    done;
    let context = Printf.sprintf "round %d" round in
    check_integer_map (context ^ " left") !native_left !reference_left;
    check_integer_map (context ^ " right") !native_right !reference_right;
    check_integer_map (context ^ " combine")
      (Integer_native.combine combine_values !native_left !native_right)
      (Integer_reference.combine combine_values !reference_left !reference_right);
    check_integer_map (context ^ " union-left")
      (Integer_native.union_left !native_left !native_right)
      (Integer_reference.union_left !reference_left !reference_right);
    check_integer_map (context ^ " union-right")
      (Integer_native.union_right !native_left !native_right)
      (Integer_reference.union_right !reference_left !reference_right);
    check_integer_map (context ^ " map-filter")
      (Integer_native.map_filter
         (fun key value -> if key mod 4 = 0 then None else Some (value + key))
         !native_left)
      (Integer_reference.map_filter
         (fun key value -> if key mod 4 = 0 then None else Some (value + key))
         !reference_left);
    if Integer_native.fold (fun total _ value -> total + value) !native_left 0
       <> Integer_reference.fold
            (fun total _ value -> total + value) !reference_left 0 then
      fail (context ^ " integer fold");
    if Integer_native.beq ( = ) !native_left !native_left
       <> Integer_reference.beq ( = ) !reference_left !reference_left then
      fail (context ^ " integer beq")
  done

let encode_position logical =
  ((logical / 9) lsl 4) lor (logical mod 9)

let decode_position packed =
  let byte = packed lsr 4 and tag = packed land 15 in
  if tag > 8 then fail "invalid packed string position";
  (9 * byte) + tag

let option_map f = function None -> None | Some value -> Some (f value)

let random_string () =
  Stdlib.String.init (Random.int 7) (fun _ -> Char.chr (Random.int 256))

let targeted_strings =
  [""; "\000"; "\255"; "a"; "ab"; "a\000b"; "a\255b";
   "prefix"; "prefix\000"; "prefix\255"]

let check_string_bits () =
  let strings =
    targeted_strings @ List.init 100 (fun _ -> random_string ())
  in
  List.iter
    (fun left ->
       List.iter
         (fun right ->
            let limit =
              9 * max (Stdlib.String.length left) (Stdlib.String.length right) + 2
            in
            for position = 0 to limit do
              if String_bits_native.bit_at left (encode_position position)
                 <> String_bits_reference.bit_at left position then
                fail "string bit_at"
            done;
            if option_map decode_position
                 (String_bits_native.first_diff left right)
               <> String_bits_reference.first_diff left right then
              fail "string first_diff";
            for split = 0 to limit do
              let packed = encode_position split in
              if String_bits_native.agrees_before left right packed
                 <> String_bits_reference.agrees_before left right split then
                fail "string agrees_before";
              if String_bits_native.agrees_before_bounded left right packed
                 <> String_bits_reference.agrees_before_bounded left right split then
                fail "string agrees_before_bounded"
            done)
         strings)
    strings

let check_string_operations () =
  let key_pool = targeted_strings @ List.init 100 (fun _ -> random_string ()) in
  for round = 1 to 75 do
    let native_left = ref String_native.empty in
    let reference_left = ref String_reference.empty in
    let native_right = ref String_native.empty in
    let reference_right = ref String_reference.empty in
    for step = 1 to 80 do
      let key = List.nth key_pool (Random.int (List.length key_pool)) in
      let value = Random.int 10_000 in
      if Random.bool () then begin
        native_left := String_native.set key value !native_left;
        reference_left := String_reference.set key value !reference_left
      end else begin
        native_right := String_native.set key value !native_right;
        reference_right := String_reference.set key value !reference_right
      end;
      if step mod 7 = 0 then begin
        let removed = List.nth key_pool (Random.int (List.length key_pool)) in
        native_right := String_native.remove removed !native_right;
        reference_right := String_reference.remove removed !reference_right
      end
    done;
    let context = Printf.sprintf "round %d" round in
    check_string_map (context ^ " left") key_pool !native_left !reference_left;
    check_string_map (context ^ " right") key_pool !native_right !reference_right;
    check_string_map (context ^ " combine") key_pool
      (String_native.combine combine_values !native_left !native_right)
      (String_reference.combine combine_values !reference_left !reference_right);
    check_string_map (context ^ " union-left") key_pool
      (String_native.union_left !native_left !native_right)
      (String_reference.union_left !reference_left !reference_right);
    check_string_map (context ^ " union-right") key_pool
      (String_native.union_right !native_left !native_right)
      (String_reference.union_right !reference_left !reference_right);
    check_string_map (context ^ " map-filter") key_pool
      (String_native.map_filter
         (fun key value ->
            if Stdlib.String.length key mod 4 = 0 then None
            else Some (value + Stdlib.String.length key))
         !native_left)
      (String_reference.map_filter
         (fun key value ->
            if Stdlib.String.length key mod 4 = 0 then None
            else Some (value + Stdlib.String.length key))
         !reference_left);
    if String_native.fold (fun total _ value -> total + value) !native_left 0
       <> String_reference.fold
            (fun total _ value -> total + value) !reference_left 0 then
      fail (context ^ " string fold");
    if String_native.beq ( = ) !native_left !native_left
       <> String_reference.beq ( = ) !reference_left !reference_left then
      fail (context ^ " string beq")
  done

let () =
  Random.init 0x524546;
  check_string_bits ();
  check_integer_operations ();
  check_string_operations ();
  print_endline "Patricia optimized/reference differential test: ok"
