module type KEY = HashMap.KEY

module Make (Key : KEY) = struct
  type key = Key.t

  type 'a tree =
    | Empty
    | Leaf of int * key * 'a
    | Collision of int * (key * 'a) list
    | Branch of int * 'a tree HashTablePrimitives.t

  type 'a t = { seed : int; root : 'a tree }

  let branch_levels = 6
  let normalize_hash raw = raw land 0x3fffffff
  let hash seed key = normalize_hash (Key.hash ~seed key)
  let chunk full_hash depth = (full_hash lsr (5 * depth)) land 31
  let bit slot = 1 lsl slot
  let has_slot bitmap slot = bitmap land bit slot <> 0

  let rec popcount word =
    if word = 0 then 0 else popcount (word land (word - 1)) + 1

  let rank bitmap slot =
    if slot = 0 then 0 else popcount (bitmap land (bit slot - 1))

  let bucket_get key entries =
    let rec loop = function
      | [] -> None
      | (stored, value) :: rest ->
          if Key.equal key stored then Some value else loop rest
    in
    loop entries

  let bucket_set key value entries =
    let rec loop = function
      | [] -> [ (key, value) ]
      | (stored, old_value) :: rest ->
          if Key.equal key stored then (stored, value) :: rest
          else (stored, old_value) :: loop rest
    in
    loop entries

  let bucket_remove key entries =
    let rec loop = function
      | [] -> []
      | (stored, value) :: rest ->
          if Key.equal key stored then rest else (stored, value) :: loop rest
    in
    loop entries

  let normalize_collision full_hash = function
    | [] -> Empty
    | [ (key, value) ] -> Leaf (full_hash, key, value)
    | entries -> Collision (full_hash, entries)

  let join_two left_hash left right_hash right depth =
    let left_slot = chunk left_hash depth in
    let right_slot = chunk right_hash depth in
    let bitmap = bit left_slot lor bit right_slot in
    if left_slot < right_slot then
      Branch (bitmap, HashTablePrimitives.of_list [ left; right ])
    else
      Branch (bitmap, HashTablePrimitives.of_list [ right; left ])

  let rec join_worker fuel depth left_hash left right_hash right =
    if fuel = 0 then join_two left_hash left right_hash right depth
    else if chunk left_hash depth = chunk right_hash depth then
      Branch (bit (chunk left_hash depth),
        HashTablePrimitives.of_list
          [ join_worker (fuel - 1) (depth + 1) left_hash left right_hash right ])
    else
      join_two left_hash left right_hash right depth

  let rec get_tree fuel depth full_hash key = function
    | Empty -> None
    | Leaf (stored_hash, stored, value) ->
        if full_hash = stored_hash && Key.equal key stored then Some value else None
    | Collision (stored_hash, entries) ->
        if full_hash = stored_hash then bucket_get key entries else None
    | Branch (bitmap, children) ->
        if fuel = 0 then None
        else
          let slot = chunk full_hash depth in
          if not (has_slot bitmap slot) then None
          else
            match HashTablePrimitives.get (rank bitmap slot) children with
            | None -> None
            | Some child -> get_tree (fuel - 1) (depth + 1) full_hash key child

  let branch_insert bitmap slot child children =
    Branch (bitmap lor bit slot,
      HashTablePrimitives.insert (rank bitmap slot) child children)

  let branch_replace bitmap slot child children =
    Branch (bitmap, HashTablePrimitives.replace (rank bitmap slot) child children)

  let rec set_tree fuel depth full_hash key value = function
    | Empty -> Leaf (full_hash, key, value)
    | Leaf (stored_hash, stored, old_value) ->
        if Key.equal key stored then Leaf (stored_hash, stored, value)
        else if full_hash = stored_hash then
          Collision (stored_hash, [ (stored, old_value); (key, value) ])
        else
          join_worker fuel depth full_hash (Leaf (full_hash, key, value))
            stored_hash (Leaf (stored_hash, stored, old_value))
    | Collision (stored_hash, entries) ->
        if full_hash = stored_hash then
          normalize_collision stored_hash (bucket_set key value entries)
        else
          join_worker fuel depth full_hash (Leaf (full_hash, key, value))
            stored_hash (Collision (stored_hash, entries))
    | Branch (bitmap, children) as branch ->
        if fuel = 0 then branch
        else
          let slot = chunk full_hash depth in
          if has_slot bitmap slot then
            match HashTablePrimitives.get (rank bitmap slot) children with
            | None -> branch_insert bitmap slot (Leaf (full_hash, key, value)) children
            | Some child ->
                branch_replace bitmap slot
                  (set_tree (fuel - 1) (depth + 1) full_hash key value child) children
          else branch_insert bitmap slot (Leaf (full_hash, key, value)) children

  let branch_remove bitmap slot children =
    let remaining = HashTablePrimitives.remove (rank bitmap slot) children in
    if HashTablePrimitives.length remaining = 0 then Empty
    else Branch (bitmap land (lnot (bit slot)), remaining)

  let rec remove_tree fuel depth full_hash key = function
    | Empty -> Empty
    | Leaf (stored_hash, stored, value) as leaf ->
        if full_hash = stored_hash && Key.equal key stored then Empty else leaf
    | Collision (stored_hash, entries) as collision ->
        if full_hash = stored_hash then
          normalize_collision stored_hash (bucket_remove key entries)
        else collision
    | Branch (bitmap, children) as branch ->
        if fuel = 0 then branch
        else
          let slot = chunk full_hash depth in
          if not (has_slot bitmap slot) then branch
          else
            match HashTablePrimitives.get (rank bitmap slot) children with
            | None -> branch
            | Some child ->
                match remove_tree (fuel - 1) (depth + 1) full_hash key child with
                | Empty -> branch_remove bitmap slot children
                | child' -> branch_replace bitmap slot child' children

  let empty ~seed = { seed; root = Empty }
  let singleton ~seed key value =
    { seed; root = Leaf (hash seed key, key, value) }
  let is_empty map = match map.root with Empty -> true | _ -> false
  let get key map = get_tree branch_levels 0 (hash map.seed key) key map.root
  let mem key map = match get key map with Some _ -> true | None -> false
  let set key value map =
    { map with root = set_tree branch_levels 0 (hash map.seed key) key value map.root }
  let remove key map =
    { map with root = remove_tree branch_levels 0 (hash map.seed key) key map.root }

  let rec bindings = function
    | Empty -> []
    | Leaf (_, key, value) -> [ (key, value) ]
    | Collision (_, entries) -> entries
    | Branch (_, children) ->
        Stdlib.List.concat_map bindings (HashTablePrimitives.to_list children)

  let elements map = bindings map.root

  let of_list ~seed entries =
    Stdlib.List.fold_left
      (fun map (key, value) -> match get key map with Some _ -> map | None -> set key value map)
      (empty ~seed) entries
end
