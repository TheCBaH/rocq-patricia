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

module Record_key = struct
  type t = { id : int; label : string }
  let equal left right = left.id = right.id
  let hash ~seed key = Hashtbl.seeded_hash seed key.id
end

module Record_map = HashMap.Make (Record_key)

let fail message = failwith ("HashMap test: " ^ message)
let check message condition = if not condition then fail message

type model = (int * string) list

let model_get key model =
  match Stdlib.List.find_opt (fun (stored, _) -> stored = key) model with
  | None -> None
  | Some (_, value) -> Some value

let model_set key value model =
  (key, value) :: Stdlib.List.filter (fun (stored, _) -> stored <> key) model

let model_remove key model =
  Stdlib.List.filter (fun (stored, _) -> stored <> key) model

let check_model message map model =
  let bounded_keys = Stdlib.List.init 129 (fun index -> index - 64) in
  Stdlib.List.iter
    (fun key -> check (message ^ " key " ^ string_of_int key)
       (Int_map.get key map = model_get key model))
    (min_int :: max_int :: bounded_keys)

let run_history () =
  let random = Random.State.make [| 0x48414d54 |] in
  let rec loop step map model retained =
    if step = 500 then ()
    else
      let key =
        match Random.State.int random 12 with
        | 0 -> min_int | 1 -> max_int
        | _ -> Random.State.int random 129 - 64
      in
      let map, model =
        if Random.State.bool random then
          let value = string_of_int step in
          (Int_map.set key value map, model_set key value model)
        else
          (Int_map.remove key map, model_remove key model)
      in
      check_model "history current" map model;
      let retained = (map, model) :: retained in
      let old_map, old_model = Stdlib.List.nth retained (Random.State.int random (Stdlib.List.length retained)) in
      check_model "history retained" old_map old_model;
      loop (step + 1) map model retained
  in
  let empty = Int_map.empty ~seed:91 in
  loop 0 empty [] [ (empty, []) ]

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
  let original = { Record_key.id = 4; label = "original" } in
  let equivalent = { Record_key.id = 4; label = "later spelling" } in
  let records = Record_map.singleton ~seed:5 original (fun x -> x + 1) in
  let records = Record_map.set equivalent (fun x -> x + 2) records in
  check "record-ID lookup" (Option.map (fun f -> f 40) (Record_map.get original records) = Some 42);
  check "record representative retained"
    (match Record_map.elements records with
     | [ (stored, _) ] -> stored.label = "original"
     | _ -> false);
  let payload = ref 1 in
  let payloads = Int_map.singleton ~seed:1 99 payload in
  let retrieved = match Int_map.get 99 payloads with Some value -> value | None -> fail "payload" in
  retrieved := 2;
  check "mutable payload preserved" (!payload = 2);
  (* Separate functor instances must retain their own callbacks. *)
  check "callback instance isolation" (Int_map.get 0 retained = Some "zero");
  run_history ();
  print_endline "HashMap public wrapper test passed"
