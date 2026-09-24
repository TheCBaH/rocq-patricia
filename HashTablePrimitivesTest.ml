let fail message = failwith ("HashTable primitive test: " ^ message)
let check message condition = if not condition then fail message

let rec insert_at index item = function
  | [] -> [item]
  | items when index = 0 -> item :: items
  | head :: tail -> head :: insert_at (index - 1) item tail

let rec replace_at index item = function
  | [] -> []
  | _ :: tail when index = 0 -> item :: tail
  | head :: tail -> head :: replace_at (index - 1) item tail

let rec remove_at index = function
  | [] -> []
  | _ :: tail when index = 0 -> tail
  | head :: tail -> head :: remove_at (index - 1) tail

let rec source_bucket_get eqb query entries index remaining =
  if remaining = 0 then None
  else match List.nth_opt entries index with
    | None -> None
    | Some (stored, value) ->
        if eqb query stored then Some value
        else source_bucket_get eqb query entries (index + 1) (remaining - 1)

let rec source_bucket_set eqb key value entries index remaining =
  if remaining = 0 then insert_at index (key, value) entries
  else match List.nth_opt entries index with
    | None -> insert_at index (key, value) entries
    | Some (stored, _) ->
        if eqb key stored then replace_at index (stored, value) entries
        else source_bucket_set eqb key value entries (index + 1) (remaining - 1)

let rec source_bucket_remove eqb key entries index remaining =
  if remaining = 0 then entries
  else match List.nth_opt entries index with
    | None -> entries
    | Some (stored, _) ->
        if eqb key stored then remove_at index entries
        else source_bucket_remove eqb key entries (index + 1) (remaining - 1)

let check_bucket_contract () =
  let shapes =
    [ []; [1, 11]; [1, 11; 2, 22]; [1, 11; 2, 22; 1, 33];
      [1, 11; 1, 22; 1, 33; 3, 44];
      List.init 12 (fun i -> (i mod 3, i)) ]
  in
  let equalities = [ (=); (fun a b -> a mod 2 = b mod 2) ] in
  List.iter (fun entries ->
    let array = HashTablePrimitives.of_list entries in
    List.iter (fun eqb ->
      for index = 0 to List.length entries + 1 do
        for remaining = 0 to List.length entries + 2 do
          for key = 0 to 4 do
            let target_get = HashTablePrimitives.bucket_get eqb key array index remaining in
            let target_set = HashTablePrimitives.bucket_set eqb key 99 array index remaining in
            let target_remove = HashTablePrimitives.bucket_remove eqb key array index remaining in
            check "bucket get source view"
              (target_get = source_bucket_get eqb key entries index remaining);
            check "bucket set source view"
              (HashTablePrimitives.to_list target_set =
               source_bucket_set eqb key 99 entries index remaining);
            check "bucket remove source view"
              (HashTablePrimitives.to_list target_remove =
               source_bucket_remove eqb key entries index remaining);
            check "bucket input unchanged" (HashTablePrimitives.to_list array = entries);
            check "bucket set fresh" (array != target_set);
            if HashTablePrimitives.to_list target_remove <> entries then
              check "bucket changed remove fresh" (array != target_remove)
          done
        done
      done) equalities) shapes

let () =
  let items = HashTablePrimitives.of_list [ 10; 20; 30 ] in
  check "length" (HashTablePrimitives.length items = 3);
  check "nonempty" (not (HashTablePrimitives.is_empty items));
  check "get" (HashTablePrimitives.get 1 items = Some 20);
  check "missing get" (HashTablePrimitives.get 3 items = None);
  let inserted = HashTablePrimitives.insert 1 15 items in
  check "insert view" (HashTablePrimitives.to_list inserted = [ 10; 15; 20; 30 ]);
  let appended = HashTablePrimitives.insert 999 40 items in
  check "out-of-range insert appends" (HashTablePrimitives.to_list appended = [ 10; 20; 30; 40 ]);
  let prepended = HashTablePrimitives.insert (-1) 5 items in
  check "negative insert prepends" (HashTablePrimitives.to_list prepended = [ 5; 10; 20; 30 ]);
  let replaced = HashTablePrimitives.replace 1 25 items in
  check "replace view" (HashTablePrimitives.to_list replaced = [ 10; 25; 30 ]);
  let unchanged = HashTablePrimitives.replace 99 0 items in
  check "out-of-range replace view" (HashTablePrimitives.to_list unchanged = [ 10; 20; 30 ]);
  let negative_replace = HashTablePrimitives.replace (-1) 0 items in
  check "negative replace view"
    (HashTablePrimitives.to_list negative_replace = [ 10; 20; 30 ]);
  let removed = HashTablePrimitives.remove 1 items in
  check "remove view" (HashTablePrimitives.to_list removed = [ 10; 30 ]);
  let missing_remove = HashTablePrimitives.remove 99 items in
  check "out-of-range remove view" (HashTablePrimitives.to_list missing_remove = [ 10; 20; 30 ]);
  let negative_remove = HashTablePrimitives.remove (-1) items in
  check "negative remove view"
    (HashTablePrimitives.to_list negative_remove = [ 10; 20; 30 ]);
  let empty = HashTablePrimitives.empty () in
  check "empty length" (HashTablePrimitives.length empty = 0);
  check "empty" (HashTablePrimitives.is_empty empty);
  let empty_remove = HashTablePrimitives.remove 0 empty in
  check "removed is empty" (HashTablePrimitives.is_empty empty_remove);
  check "empty remove view" (HashTablePrimitives.to_list empty_remove = []);
  check "insert storage fresh" (not (items == inserted));
  check "negative insert storage fresh" (not (items == prepended));
  check "replace storage fresh" (not (items == replaced));
  check "remove storage fresh" (not (items == removed));
  check "no-op update storage fresh"
    (not (items == unchanged) && not (items == negative_replace) &&
     not (items == missing_remove) && not (items == negative_remove));
  check "empty no-op storage fresh" (not (empty == empty_remove));
  check "old storage unchanged" (HashTablePrimitives.to_list items = [ 10; 20; 30 ]);
  check_bucket_contract ();
  print_endline "HashTable primitive test passed"
