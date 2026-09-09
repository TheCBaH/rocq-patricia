type key = string
type 'a t = 'a StringPatriciaInternal.t

let empty = StringPatriciaInternal.empty
let is_empty = StringPatriciaInternal.is_empty
let singleton = StringPatriciaInternal.singleton
let get = StringPatriciaInternal.get
let mem = StringPatriciaInternal.mem
let set = StringPatriciaInternal.set
(* Like public [map_filter], deletion uses the source-extracted cached-sample
   worker while retaining the exact no-op root when the key is absent. *)
let remove = StringPatriciaInternal.remove_cached
let of_list = StringPatriciaInternal.of_list
let map = StringPatriciaInternal.map
(* This source-extracted variant uses the resident branch sample instead of
   rescanning the left subtree after filtering.  Its well-formed lookup
   refinement is proved in [get_map_filter_cached_wf]. *)
let map_filter = StringPatriciaInternal.map_filter_cached

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

(* The direct [Acc]-recursive source worker extracts without a fuel prepass or
   branch-local closure; packed routing and cached-sample obligations remain
   explicitly tracked at the primitive boundary. *)
let union_left = StringPatriciaUnion.union_left_native_acc_default
let union_right = StringPatriciaUnion.union_right_native_acc_default
let elements = StringPatriciaInternal.elements
let fold = StringPatriciaInternal.fold
let beq = StringPatriciaInternal.beq
