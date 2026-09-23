#!/bin/sh
set -eu

scalar_file=${1:-HashTableScalarPrimitives.ml}
[ -f "$scalar_file" ] || { echo "missing scalar primitive module" >&2; exit 1; }

for binding in require_64_bit checked_slot checked_bitmap checked_hash chunk bounded_eq slot_lt bitmap_bit bitmap_has rank bitmap_insert bitmap_remove; do
  grep -Eq "^let $binding" "$scalar_file" || {
    echo "missing scalar binding $binding" >&2; exit 1;
  }
done

grep -Fq 'Sys.word_size <> 64' "$scalar_file" || {
  echo "scalar module lacks the 64-bit platform guard" >&2; exit 1;
}
grep -Fq 'slot < 0 || slot > 31' "$scalar_file" || {
  echo "scalar module lacks the slot-domain guard" >&2; exit 1;
}
grep -Fq 'bitmap < 0 || bitmap >= (1 lsl 32)' "$scalar_file" || {
  echo "scalar module lacks the bitmap-domain guard" >&2; exit 1;
}
grep -Fq 'hash < 0 || hash >= (1 lsl 30) || depth < 0 || depth > 6' "$scalar_file" || {
  echo "scalar module lacks the hash/depth-domain guard" >&2; exit 1;
}
grep -Fq 'hash < 0 || hash >= (1 lsl 30)' "$scalar_file" || {
  echo "scalar module lacks the comparison hash-domain guard" >&2; exit 1;
}
for checked_input in 'checked_hash left' 'checked_hash right' 'checked_slot left' 'checked_slot right'; do
  grep -Fq "$checked_input" "$scalar_file" || {
    echo "scalar comparison lacks a guarded input: $checked_input" >&2; exit 1;
  }
done
grep -Fq 'loop 32 word 0' "$scalar_file" || {
  echo "scalar rank does not use the bounded 32-step popcount" >&2; exit 1;
}

if grep -Eq 'Obj\.|Marshal\.|external |unsafe' "$scalar_file"; then
  echo "scalar module contains an unapproved unsafe escape" >&2; exit 1
fi

echo "Hash-table scalar primitive inventory: guarded 64-bit bounded routing and bitmap realizers"
