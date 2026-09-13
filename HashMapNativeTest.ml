module Key = struct
  type t = int
  let equal (left : int) right = left = right
  let hash ~seed key =
    if key land 7 = 0 then seed else key lxor seed
end

module Reference = HashMap.Make (Key)
module Native = HashMapNative.Make (Key)

let fail message = failwith ("HashMap native test: " ^ message)
let check message condition = if not condition then fail message

let check_agreement message reference native =
  let probes = min_int :: max_int :: Stdlib.List.init 257 (fun index -> index - 128) in
  Stdlib.List.iter
    (fun key ->
       check (message ^ " key " ^ string_of_int key)
         (Reference.get key reference = Native.get key native))
    probes;
  check (message ^ " empty") (Reference.is_empty reference = Native.is_empty native)

let () =
  let random = Random.State.make [| 0x41525241; 0x59544553 |] in
  let rec loop step reference native retained =
    if step = 1000 then ()
    else begin
      let key =
        match Random.State.int random 16 with
        | 0 -> min_int
        | 1 -> max_int
        | _ -> Random.State.int random 257 - 128
      in
      let reference, native =
        if Random.State.bool random then begin
          let value = string_of_int step in
          (Reference.set key value reference, Native.set key value native)
        end else
          (Reference.remove key reference, Native.remove key native)
      in
      check_agreement "current" reference native;
      let retained = (reference, native) :: retained in
      let old_reference, old_native =
        Stdlib.List.nth retained
          (Random.State.int random (Stdlib.List.length retained))
      in
      check_agreement "retained" old_reference old_native;
      loop (step + 1) reference native retained
    end
  in
  let reference = Reference.of_list ~seed:19 [ (0, "first"); (0, "later"); (8, "collision") ] in
  let native = Native.of_list ~seed:19 [ (0, "first"); (0, "later"); (8, "collision") ] in
  check "first-wins reference" (Reference.get 0 reference = Some "first");
  check "first-wins native" (Native.get 0 native = Some "first");
  check_agreement "bulk load" reference native;
  loop 0 reference native [ (reference, native) ];
  print_endline "HashMap native array differential test passed"
