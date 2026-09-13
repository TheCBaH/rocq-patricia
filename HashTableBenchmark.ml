(* Checked, workload-specific benchmark for the current source-reference
   backend.  Every timed result is checked against the association-list
   oracle; timings are not proof or portable performance claims. *)

module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key = key lxor seed
end

module Hash_map = HashMap.Make (Key)
module Ordered_map = Map.Make (Int)

let size =
  match Sys.getenv_opt "HASHTABLE_BENCH_SIZE" with
  | None -> 2_000
  | Some value -> int_of_string value

let fail message = failwith ("HashTable benchmark: " ^ message)

let time name run =
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let started = Unix.gettimeofday () in
  let result = run () in
  let elapsed = Unix.gettimeofday () -. started in
  let allocated = Gc.allocated_bytes () -. before in
  Printf.printf "%s: %.6fs, %.0f allocated bytes\n%!" name elapsed allocated;
  result

let oracle_get key bindings =
  match Stdlib.List.find_opt (fun (stored, _) -> stored = key) bindings with
  | None -> None
  | Some (_, value) -> Some value

let () =
  if size < 1 then fail "HASHTABLE_BENCH_SIZE must be positive";
  let bindings = Stdlib.List.init size (fun key -> (key, string_of_int key)) in
  let oracle = Stdlib.List.rev bindings in
  let hashed = time "HashMap.Make build" (fun () -> Hash_map.of_list ~seed:31 bindings) in
  let ordered = time "Map.Make build"
      (fun () -> Stdlib.List.fold_left (fun map (key, value) -> Ordered_map.add key value map)
               Ordered_map.empty bindings)
  in
  let standard = time "Hashtbl build" (fun () ->
      let table = Hashtbl.create size in
      Stdlib.List.iter (fun (key, value) -> Hashtbl.replace table key value) bindings;
      table)
  in
  let check name get =
    Stdlib.List.iter (fun (key, _) ->
      if get key <> oracle_get key oracle then fail (name ^ " lookup mismatch")) bindings;
    if get (-1) <> None then fail (name ^ " missing lookup mismatch")
  in
  time "HashMap.Make checked lookup" (fun () -> check "HashMap.Make" (fun key -> Hash_map.get key hashed));
  time "Map.Make checked lookup" (fun () -> check "Map.Make" (fun key -> Ordered_map.find_opt key ordered));
  time "Hashtbl checked lookup" (fun () -> check "Hashtbl" (fun key -> Hashtbl.find_opt standard key));
  Printf.printf "HashTable checked benchmark passed (%d bindings)\n%!" size
