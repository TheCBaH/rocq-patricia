(* Allocation and root-sharing profile for legacy, cached, and public string
   deletion.  This checks exact bindings; it is not a formal cost theorem. *)

module S = StringPatriciaInternal
module Public = StringPatriciaMap

let positive_env name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some value ->
      (try
         let parsed = int_of_string value in
         if parsed <= 0 then invalid_arg (name ^ " must be positive");
         parsed
       with Failure _ -> invalid_arg (name ^ " must be an integer"))

let profile_size = positive_env "PATRICIA_REMOVE_PROFILE_SIZE" 10_000
let key index = Printf.sprintf "%08x" index
let keys = Array.init profile_size key
let value name = int_of_string ("0x" ^ name)

let input = Array.fold_left (fun tree name -> S.set name (value name) tree) S.empty keys
let public_input =
  Array.fold_left (fun tree name -> Public.set name (value name) tree) Public.empty keys

type measurement = { allocated_words : float; retained_words : int }

let words () =
  let stats = Gc.quick_stat () in stats.Gc.minor_words +. stats.Gc.major_words

let measure operation =
  Gc.full_major (); Gc.compact ();
  let before_live = (Gc.stat ()).Gc.live_words in
  let before_words = words () in
  let result = operation () in
  let allocated_words = words () -. before_words in
  ignore (Sys.opaque_identity result);
  Gc.full_major (); Gc.compact ();
  result, { allocated_words; retained_words = (Gc.stat ()).Gc.live_words - before_live }

let check label removed tree =
  let expected = if removed = None then profile_size else profile_size - 1 in
  if List.length (S.elements tree) <> expected then failwith (label ^ ": cardinality");
  Array.iter (fun name ->
    if S.get name tree <> (if Some name = removed then None else Some (value name)) then
      failwith (label ^ ": lookup")) keys

let check_public label removed tree =
  let expected = if removed = None then profile_size else profile_size - 1 in
  if List.length (Public.elements tree) <> expected then failwith (label ^ ": public cardinality");
  Array.iter (fun name ->
    if Public.get name tree <> (if Some name = removed then None else Some (value name)) then
      failwith (label ^ ": public lookup")) keys

let print label worker m =
  Printf.printf "  %-10s %-10s %12.0f %12d\n" label worker m.allocated_words m.retained_words

let profile label removed worker =
  let result, m = measure (fun () -> worker removed input) in
  check label removed result; m

let profile_public label removed =
  let result, m = measure (fun () -> Public.remove removed public_input) in
  check_public label (if removed = "missing" then None else Some removed) result; m

let legacy removed tree = S.remove removed tree
let cached removed tree = S.remove_cached removed tree

let () =
  let present = keys.(profile_size / 2) in
  let workloads = ["absent", "missing", None; "present", present, Some present] in
  Printf.printf "String remove profile (%d bindings)\n" profile_size;
  Printf.printf "  %-10s %-10s %12s %12s\n" "workload" "worker" "allocated" "retained";
  Printf.printf "  %-10s %-10s %12s %12s\n" "" "" "words" "words";
  List.iter (fun (label, removed, expected) ->
    print label "legacy" (profile label expected (fun _ tree -> legacy removed tree));
    print label "cached" (profile label expected (fun _ tree -> cached removed tree));
    print label "public" (profile_public label removed)) workloads
