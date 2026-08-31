type key = string
type 'a t = 'a StringPatriciaInternal.t

let empty = StringPatriciaInternal.empty
let is_empty = StringPatriciaInternal.is_empty
let singleton = StringPatriciaInternal.singleton
let get = StringPatriciaInternal.get
let mem = StringPatriciaInternal.mem
let set = StringPatriciaInternal.set
let remove = StringPatriciaInternal.remove
let map = StringPatriciaInternal.map
let map_filter = StringPatriciaInternal.map_filter

type ('a, 'b, 'c) combiner = {
  left_only : 'a -> 'c option;
  right_only : 'b -> 'c option;
  both : 'a -> 'b -> 'c option;
}

let combine combiner =
  StringPatriciaInternal.combine
    (fun left right ->
       match left, right with
       | Some left_value, None -> combiner.left_only left_value
       | None, Some right_value -> combiner.right_only right_value
       | Some left_value, Some right_value ->
           combiner.both left_value right_value
       | None, None -> None)

(* The companion worker is proved against the pure left-/right-biased union.
   [Empty] is its allocation-free certificate that the original first input
   can be reused. *)
let union_left = StringPatriciaUnion.union_left_specialized_changed_result
let union_right = StringPatriciaUnion.union_right_specialized_changed_result
let elements = StringPatriciaInternal.elements
let fold = StringPatriciaInternal.fold
let beq = StringPatriciaInternal.beq
