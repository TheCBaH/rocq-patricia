(* Finite target checks for the bounded scalar extraction adapter. *)

module Scalar = HashTableScalarPrimitives

let fail message = failwith ("HashTable scalar primitives: " ^ message)

let reference_popcount word =
  let rec loop bits count =
    if bits = 0 then count else loop (bits lsr 1) (count + (bits land 1))
  in
  loop word 0

let check_bitmap bitmap =
  for slot = 0 to 31 do
    let bit = 1 lsl slot in
    if Scalar.bitmap_bit slot <> bit then fail "bitmap_bit mismatch";
    if Scalar.bitmap_has bitmap slot <> (bitmap land bit <> 0) then
      fail "bitmap_has mismatch";
    let lower = if slot = 0 then 0 else (1 lsl slot) - 1 in
    if Scalar.rank bitmap slot <> reference_popcount (bitmap land lower) then
      fail "rank mismatch";
    if Scalar.bitmap_insert bitmap slot <> bitmap lor bit then
      fail "bitmap_insert mismatch";
    if Scalar.bitmap_remove bitmap slot <> bitmap land lnot bit then
      fail "bitmap_remove mismatch"
  done

let () =
  if Sys.word_size <> 64 then fail "test requires the documented 64-bit target";
  let hashes = [ 0; 1; 31; 32; (1 lsl 30) - 1 ] in
  Stdlib.List.iter (fun hash ->
      for depth = 0 to 6 do
        if Scalar.chunk hash depth <> ((hash lsr (5 * depth)) land 31) then
          fail "chunk mismatch"
      done;
      Stdlib.List.iter (fun other ->
          if Scalar.bounded_eq hash other <> (hash = other) then
            fail "bounded_eq mismatch") hashes) hashes;
  for left = 0 to 31 do
    for right = 0 to 31 do
      if Scalar.slot_lt left right <> (left < right) then
        fail "slot_lt mismatch"
    done
  done;
  for word = 0 to 65_535 do check_bitmap word done;
  let random = Random.State.make [| 0x5ca1a2 |] in
  for _ = 1 to 10_000 do
    let word = Random.State.int random 65_536 lor (Random.State.int random 65_536 lsl 16) in
    check_bitmap word
  done;
  check_bitmap 4_294_967_295;
  let rejects thunk =
    try ignore (thunk ()); false with Invalid_argument _ -> true
  in
  if not (rejects (fun () -> Scalar.bitmap_has (-1) 0)) then
    fail "negative bitmap was accepted";
  if not (rejects (fun () -> Scalar.rank (1 lsl 32) 0)) then
    fail "wide bitmap was accepted";
  if not (rejects (fun () -> Scalar.chunk (1 lsl 30) 0)) then
    fail "wide hash was accepted";
  if not (rejects (fun () -> Scalar.bounded_eq (-1) 0)) then
    fail "negative equality input was accepted";
  if not (rejects (fun () -> Scalar.bounded_eq 0 (1 lsl 30))) then
    fail "wide equality input was accepted";
  if not (rejects (fun () -> Scalar.slot_lt 0 32)) then
    fail "wide slot-order input was accepted";
  print_endline "HashTable scalar primitive test passed"
