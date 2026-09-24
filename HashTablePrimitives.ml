type 'a t = 'a array

let empty () = [||]
let of_list = Array.of_list
let to_list = Array.to_list
let length = Array.length
let is_empty items = Array.length items = 0

let get index items =
  if index < 0 || index >= Array.length items then None else Some items.(index)

(* The list source workers append when [index] exceeds the current length. *)
let insertion_index index items =
  if index <= 0 then 0 else min index (Array.length items)

let insert index item items =
  let before = insertion_index index items in
  let result = Array.make (Array.length items + 1) item in
  Array.blit items 0 result 0 before;
  Array.blit items before result (before + 1) (Array.length items - before);
  result

let replace index item items =
  let result = Array.copy items in
  if index >= 0 && index < Array.length result then result.(index) <- item;
  result

let remove index items =
  let size = Array.length items in
  if index < 0 || index >= size then Array.copy items
  else begin
    let result = Array.make (size - 1) items.(0) in
    Array.blit items 0 result 0 index;
    Array.blit items (index + 1) result index (size - index - 1);
    result
  end

(* The source bucket workers inspect at most [remaining] entries, stopping at
   the first missing index.  Keep the scan inside the private array adapter so
   extracted nat cases and checked [get] options are not allocated per entry. *)
let bucket_scan eqb query entries index remaining =
  let size = Array.length entries in
  if index < 0 || remaining <= 0 then (None, index)
  else begin
    let position = ref index in
    let left = ref remaining in
    let found = ref None in
    while !position < size && !left > 0 && !found = None do
      let stored, _ = entries.(!position) in
      if eqb query stored then found := Some !position
      else begin incr position; decr left end
    done;
    (!found, !position)
  end

let bucket_get eqb query entries index remaining =
  match bucket_scan eqb query entries index remaining with
  | Some position, _ -> let _, value = entries.(position) in Some value
  | None, _ -> None

let bucket_set eqb key value entries index remaining =
  match bucket_scan eqb key entries index remaining with
  | Some position, _ ->
      let stored, _ = entries.(position) in
      replace position (stored, value) entries
  | None, insertion -> insert insertion (key, value) entries

let rec bucket_remove_short eqb key entries index remaining =
  if remaining <= 0 then entries
  else match get index entries with
    | None -> entries
    | Some (stored, _) ->
        if eqb key stored then remove index entries
        else bucket_remove_short eqb key entries (index + 1) (remaining - 1)

let bucket_remove eqb key entries index remaining =
  (* Small collision buckets avoid the mutable-loop setup on the common
     short-removal path. Long buckets keep the low-allocation scan. *)
  if Array.length entries <= 8 then
    bucket_remove_short eqb key entries index remaining
  else match bucket_scan eqb key entries index remaining with
    | Some position, _ -> remove position entries
    | None, _ -> entries
