module type KEY = sig
  type t
  val equal : t -> t -> bool
  val hash : seed:int -> t -> int
end

module Make (Key : KEY) = struct
  type key = Key.t
  type 'a t = (key, int, 'a) HashTableNative.native_table

  let normalize_hash raw = raw land 0x3fffffff
  let hash seed key = normalize_hash (Key.hash ~seed key)

  let empty ~seed = HashTableNative.native_empty seed
  let singleton ~seed key value =
    HashTableNative.native_table_set Key.equal hash key value (empty ~seed)
  let is_empty = HashTableNative.native_table_is_empty
  let get key map = HashTableNative.native_table_get Key.equal hash key map
  let mem key map = HashTableNative.native_table_mem Key.equal hash key map
  let set key value map = HashTableNative.native_table_set Key.equal hash key value map
  let remove key map = HashTableNative.native_table_remove Key.equal hash key map
  let of_list ~seed entries = HashTableNative.native_table_of_list Key.equal hash seed entries
  let elements = HashTableNative.native_table_elements
end
