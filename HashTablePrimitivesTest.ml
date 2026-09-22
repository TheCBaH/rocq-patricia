let fail message = failwith ("HashTable primitive test: " ^ message)
let check message condition = if not condition then fail message

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
  print_endline "HashTable primitive test passed"
