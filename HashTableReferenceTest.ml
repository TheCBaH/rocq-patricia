(* Finite executable evidence for the source-extracted reference HAMT.
   The eventual HashMap.Make wrapper will run this same behavior through its
   abstract interface; this early test intentionally calls the extracted map
   directly while H2 proofs and H3 packaging are under construction. *)

module M = HashTable
module Test_hash = HashTableTestHash

let fail message = failwith ("HashTable reference test: " ^ message)
let check message condition = if not condition then fail message

let equal (left : int) right = left = right
let hash seed key = Test_hash.int ~seed key
let constant_hash seed key = Test_hash.constant ~seed key

let expect_get hash key expected table =
  check ("lookup " ^ string_of_int key)
    (M.get equal hash key table = expected)

let () =
  check "test hash lower bound" (Test_hash.normalize min_int >= 0);
  check "test hash upper bound"
    (Test_hash.normalize max_int < Test_hash.bound);
  check "test hash string determinism"
    (Test_hash.string ~seed:17 "reference\000hash" =
     Test_hash.string ~seed:17 "reference\000hash");
  let empty = M.empty 17 in
  expect_get hash 1 None empty;
  check "empty" (M.is_empty empty);

  let one = M.set equal hash 1 "one" empty in
  expect_get hash 1 (Some "one") one;
  expect_get hash 2 None one;
  check "singleton elements" (M.elements one = [ (1, "one") ]);

  let collision =
    empty |> M.set equal constant_hash 10 "ten"
          |> M.set equal constant_hash 20 "twenty"
          |> M.set equal constant_hash 30 "thirty"
  in
  expect_get constant_hash 10 (Some "ten") collision;
  expect_get constant_hash 20 (Some "twenty") collision;
  let replaced = M.set equal constant_hash 20 "updated" collision in
  expect_get constant_hash 20 (Some "updated") replaced;
  expect_get constant_hash 10 (Some "ten") replaced;
  expect_get constant_hash 20 (Some "twenty") collision;
  let after_remove = M.remove equal constant_hash 20 replaced in
  expect_get constant_hash 20 None after_remove;
  expect_get constant_hash 10 (Some "ten") after_remove;
  expect_get constant_hash 30 (Some "thirty") after_remove;

  let routed =
    Stdlib.List.fold_left (fun map key -> M.set equal hash key (string_of_int key) map)
      empty [ 0; 1; 32; 1024; 32768; 1048576; 33554432 ]
  in
  Stdlib.List.iter (fun key -> expect_get hash key (Some (string_of_int key)) routed)
    [ 0; 1; 32; 1024; 32768; 1048576; 33554432 ];
  let routed' = M.remove equal hash 32768 routed in
  expect_get hash 32768 None routed';
  expect_get hash 32768 (Some "32768") routed;

  (* [0] and [32] share the root slot but diverge at the next level.  Removing
     one then inserting it again exercises a retained unary branch path. *)
  let unary = empty |> M.set equal hash 0 "zero" |> M.set equal hash 32 "thirty-two" in
  let unary_after_remove = M.remove equal hash 32 unary in
  expect_get hash 0 (Some "zero") unary_after_remove;
  expect_get hash 32 None unary_after_remove;
  let unary_reinserted = M.set equal hash 32 "again" unary_after_remove in
  expect_get hash 0 (Some "zero") unary_reinserted;
  expect_get hash 32 (Some "again") unary_reinserted;

  let every_slot =
    Stdlib.List.fold_left (fun map slot -> M.set equal hash slot slot map)
      empty (Stdlib.List.init 32 Fun.id)
  in
  Stdlib.List.iter (fun slot -> expect_get hash slot (Some slot) every_slot)
    (Stdlib.List.init 32 Fun.id);
  let every_slot = M.remove equal hash 31 every_slot in
  expect_get hash 31 None every_slot;
  Stdlib.List.iter (fun slot -> if slot <> 31 then expect_get hash slot (Some slot) every_slot)
    (Stdlib.List.init 32 Fun.id);

  let bulk = M.of_list equal hash 9 [ (7, "first"); (7, "second"); (8, "eight") ] in
  expect_get hash 7 (Some "first") bulk;
  expect_get hash 8 (Some "eight") bulk;
  check "first representative and value retained"
    (Stdlib.List.mem (7, "first") (M.elements bulk) &&
     not (Stdlib.List.mem (7, "second") (M.elements bulk)));
  print_endline "HashTable reference test passed"
