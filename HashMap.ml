module type KEY = sig
  type t
  val equal : t -> t -> bool
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) = struct
  type key = Key.t
  type 'a t = (key, int, 'a) HashTableReference.table

  let normalize_hash raw = raw land 0x3fffffff
  let hash seed key = normalize_hash (Key.hash ~seed key)

  let empty ~seed = HashTableReference.empty seed
  let singleton ~seed key value = HashTableReference.singleton Key.equal hash seed key value
  let is_empty = HashTableReference.is_empty
  let get key map = HashTableReference.get Key.equal hash key map
  let mem key map = HashTableReference.mem Key.equal hash key map
  let set key value map = HashTableReference.set Key.equal hash key value map
  let remove key map = HashTableReference.remove Key.equal hash key map
  let of_list ~seed entries = HashTableReference.of_list Key.equal hash seed entries
  let elements = HashTableReference.elements
end
