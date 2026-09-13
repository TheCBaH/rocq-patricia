module Int_key = struct
  type t = int
  let equal (left : int) right = left = right
  (* Deliberately returns negative values for half the domain. *)
  let hash ~seed key = key lxor seed
end

module Case_key = struct
  type t = string
  let normalize = String.lowercase_ascii
  let equal left right = String.equal (normalize left) (normalize right)
  let hash ~seed key = Hashtbl.seeded_hash seed (normalize key)
end

module Int_map = HashMap.Make (Int_key)
module Case_map = HashMap.Make (Case_key)

let fail message = failwith ("HashMap test: " ^ message)
let check message condition = if not condition then fail message

let () =
  let numbers = Int_map.empty ~seed:17 in
  let numbers = Int_map.set (-7) "negative" numbers in
  let numbers = Int_map.set 0 "zero" numbers in
  let numbers = Int_map.set max_int "max" numbers in
  let numbers = Int_map.set min_int "min" numbers in
  check "negative key" (Int_map.get (-7) numbers = Some "negative");
  check "zero key" (Int_map.get 0 numbers = Some "zero");
  check "native bounds" (Int_map.get max_int numbers = Some "max" &&
                         Int_map.get min_int numbers = Some "min");
  let retained = numbers in
  let numbers = Int_map.remove 0 numbers in
  check "removed" (Int_map.get 0 numbers = None);
  check "retained version" (Int_map.get 0 retained = Some "zero");

  let names = Case_map.empty ~seed:3 in
  let names = Case_map.set "Alice" 1 names in
  let names = Case_map.set "ALICE" 2 names in
  check "equivalent query" (Case_map.get "aLiCe" names = Some 2);
  check "stored representative retained"
    (Case_map.elements names = [ ("Alice", 2) ]);
  let first = Case_map.of_list ~seed:8 [ ("Bob", 1); ("BOB", 2) ] in
  check "first value wins" (Case_map.get "bob" first = Some 1);
  check "first representative wins" (Case_map.elements first = [ ("Bob", 1) ]);
  (* Separate functor instances must retain their own callbacks. *)
  check "callback instance isolation" (Int_map.get 0 retained = Some "zero");
  print_endline "HashMap public wrapper test passed"
