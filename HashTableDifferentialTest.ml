module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key = key lxor seed
end

module Subject = HashMap.Make (Key)
module Oracle = Stdlib.Map.Make (Int)

module Folded_key = struct
  type t = string
  let canonical = String.lowercase_ascii
  let equal left right = String.equal (canonical left) (canonical right)
  (* Equal-length names deliberately collide after canonicalization. *)
  let hash ~seed key = seed lxor String.length (canonical key)
end

module Folded_subject = HashMap.Make (Folded_key)
module Folded_oracle = Stdlib.Map.Make (struct
  type t = string
  let compare left right = String.compare (Folded_key.canonical left) (Folded_key.canonical right)
end)

let fail message = failwith ("HashTable differential test: " ^ message)
let check message condition = if not condition then fail message

let check_agreement message subject oracle =
  let probes = min_int :: max_int :: Stdlib.List.init 257 (fun index -> index - 128) in
  Stdlib.List.iter
    (fun key ->
       let expected = Oracle.find_opt key oracle in
       check (message ^ " key " ^ string_of_int key)
         (Subject.get key subject = expected))
    probes

let check_folded_agreement message subject oracle =
  let probes = [ "ALPHA"; "alpha"; "Beta"; "BETA"; "gamma"; "GAMMA"; "missing" ] in
  Stdlib.List.iter
    (fun key ->
       let subject_value = Option.map (fun value -> value 17) (Folded_subject.get key subject) in
       let oracle_value = Option.map (fun value -> value 17) (Folded_oracle.find_opt key oracle) in
       check (message ^ " key " ^ key) (subject_value = oracle_value))
    probes

let run_folded_history () =
  let random = Random.State.make [| 0x464f4c44; 0x45444b59 |] in
  let keys = [| "Alpha"; "ALPHA"; "Beta"; "BETA"; "Gamma"; "GAMMA" |] in
  let rec loop step subject oracle retained =
    if step = 500 then ()
    else begin
      let key = keys.(Random.State.int random (Array.length keys)) in
      let subject, oracle =
        if Random.State.bool random then
          let value = fun input -> input + step in
          (Folded_subject.set key value subject, Folded_oracle.add key value oracle)
        else
          (Folded_subject.remove key subject, Folded_oracle.remove key oracle)
      in
      check_folded_agreement "folded current" subject oracle;
      let retained = (subject, oracle) :: retained in
      let old_subject, old_oracle =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_folded_agreement "folded retained" old_subject old_oracle;
      loop (step + 1) subject oracle retained
    end
  in
  let empty = Folded_subject.empty ~seed:0x5eed in
  loop 0 empty Folded_oracle.empty [ (empty, Folded_oracle.empty) ]

let () =
  let random = Random.State.make [| 0x48414d54; 0x44494646 |] in
  let rec loop step subject oracle retained =
    if step = 1000 then ()
    else begin
      let key =
        match Random.State.int random 16 with
        | 0 -> min_int
        | 1 -> max_int
        | _ -> Random.State.int random 257 - 128
      in
      let subject, oracle =
        if Random.State.bool random then
          let value = string_of_int step in
          (Subject.set key value subject, Oracle.add key value oracle)
        else
          (Subject.remove key subject, Oracle.remove key oracle)
      in
      check_agreement "current" subject oracle;
      let retained = (subject, oracle) :: retained in
      let old_subject, old_oracle =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_agreement "retained" old_subject old_oracle;
      loop (step + 1) subject oracle retained
    end
  in
  let empty = Subject.empty ~seed:0x51ed in
  loop 0 empty Oracle.empty [ (empty, Oracle.empty) ];
  run_folded_history ();
  print_endline "HashTable public differential test passed"
