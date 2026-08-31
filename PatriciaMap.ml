module Key = struct
  type t = int

  let of_int value =
    if value > 0 then Some value else None

  let of_int_exn value =
    if value > 0 then value
    else invalid_arg "PatriciaMap.Key.of_int_exn: key must be positive"

  let to_int value = value
  let equal = Int.equal
  let compare = Int.compare
end

type key = Key.t
type 'a t = 'a PatriciaInternal.t

let empty = PatriciaInternal.empty
let is_empty = PatriciaInternal.is_empty
let singleton = PatriciaInternal.singleton
let get = PatriciaInternal.get
let mem = PatriciaInternal.mem
let set = PatriciaInternal.set
let remove = PatriciaInternal.remove
let map = PatriciaInternal.map
let map_filter = PatriciaInternal.map_filter

type ('a, 'b, 'c) combiner = {
  left_only : 'a -> 'c option;
  right_only : 'b -> 'c option;
  both : 'a -> 'b -> 'c option;
}

let combine combiner =
  PatriciaInternal.combine
    (fun left right ->
       match left, right with
       | Some left_value, None -> combiner.left_only left_value
       | None, Some right_value -> combiner.right_only right_value
       | Some left_value, Some right_value ->
           combiner.both left_value right_value
       | None, None -> None)

(* The generated native-shaped worker remains a refinement candidate, but its
   closure/helper allocation currently loses to this fully inlined worker. *)
let union_left = PatriciaInternal.union_left
let union_right = PatriciaInternal.union_right
let elements = PatriciaInternal.elements
let fold = PatriciaInternal.fold
let beq = PatriciaInternal.beq
