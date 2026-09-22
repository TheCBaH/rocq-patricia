let require_64_bit () =
  if Sys.word_size <> 64 then
    failwith "HashTable native scalar extraction requires 64-bit OCaml integers"

let checked_slot slot =
  if slot < 0 || slot > 31 then invalid_arg "HashTable scalar slot"

let chunk hash depth =
  require_64_bit ();
  if hash < 0 || hash >= (1 lsl 30) || depth < 0 || depth > 6 then
    invalid_arg "HashTable scalar chunk domain";
  (hash lsr (5 * depth)) land 31

let bitmap_bit slot =
  require_64_bit ();
  checked_slot slot;
  1 lsl slot

let bitmap_has bitmap slot =
  require_64_bit ();
  checked_slot slot;
  bitmap land (1 lsl slot) <> 0

let popcount32 word =
  let rec loop fuel bits count =
    if fuel = 0 then count
    else loop (fuel - 1) (bits lsr 1) (count + (bits land 1))
  in
  loop 32 word 0

let rank bitmap slot =
  require_64_bit ();
  checked_slot slot;
  let lower_bits = if slot = 0 then 0 else (1 lsl slot) - 1 in
  popcount32 (bitmap land lower_bits)

let bitmap_insert bitmap slot =
  require_64_bit ();
  checked_slot slot;
  bitmap lor (1 lsl slot)

let bitmap_remove bitmap slot =
  require_64_bit ();
  checked_slot slot;
  bitmap land lnot (1 lsl slot)
