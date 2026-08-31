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

(* This native realization uses physical identity to preserve unchanged input
   branches. The proved changed-result worker remains its source-level oracle;
   a heap-aware refinement is still required for the [==] decisions. *)
let union_left = StringPatriciaInternal.union_left
let union_right = StringPatriciaInternal.union_right
let elements = StringPatriciaInternal.elements
let fold = StringPatriciaInternal.fold
let beq = StringPatriciaInternal.beq
