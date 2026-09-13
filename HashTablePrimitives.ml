type 'a t = 'a array

let empty () = [||]
let of_list = Array.of_list
let to_list = Array.to_list
let length = Array.length

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
