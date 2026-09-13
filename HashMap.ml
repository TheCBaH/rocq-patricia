module type KEY = sig
  type t
  val equal : t -> t -> bool
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) = struct
  type key = Key.t
  type 'a t = (key, int, 'a) HashTable.table

  let normalize_hash raw = raw land 0x3fffffff
  let hash seed key = normalize_hash (Key.hash ~seed key)

  let empty ~seed = HashTable.empty seed
  let singleton ~seed key value = HashTable.singleton Key.equal hash seed key value
  let is_empty = HashTable.is_empty
  let get key map = HashTable.get Key.equal hash key map
  let mem key map = HashTable.mem Key.equal hash key map
  let set key value map = HashTable.set Key.equal hash key value map
  let remove key map = HashTable.remove Key.equal hash key map
  let of_list ~seed entries = HashTable.of_list Key.equal hash seed entries
  let elements = HashTable.elements
end
