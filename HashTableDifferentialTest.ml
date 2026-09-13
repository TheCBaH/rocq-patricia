module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key = key lxor seed
end

module Subject = HashMap.Make (Key)
module Oracle = Stdlib.Map.Make (Int)

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
  print_endline "HashTable public differential test passed"
