#!/bin/sh
set -eu

model_file=${1:-hashtable_native_array_extracted/HashTableNative.ml}
[ -f "$model_file" ] || { echo "missing extracted native array model" >&2; exit 1; }
scalar_file=$(dirname "$model_file")/HashTableNativeBits.ml
grep -Fq 'HashTablePrimitives.t' "$model_file" || { echo "pseq was not bound to private arrays" >&2; exit 1; }
for operation in get insert replace remove to_list of_list is_empty length; do
  grep -Fq "HashTablePrimitives.$operation" "$model_file" || { echo "missing primitive $operation" >&2; exit 1; }
done
grep -Eq '^let rec native_bucket_get' "$model_file" || {
  echo "missing indexed native collision lookup worker" >&2; exit 1;
}
grep -Eq '^let rec native_bucket_set' "$model_file" || {
  echo "missing indexed native collision update worker" >&2; exit 1;
}
grep -Eq '^let rec native_bucket_remove' "$model_file" || {
  echo "missing indexed native collision removal worker" >&2; exit 1;
}
grep -Fq 'native_bucket_get eqb0 key entries 0 (pseq_length entries)' "$model_file" || {
  echo "native collision lookup does not use the bounded indexed worker" >&2; exit 1;
}
grep -Fq 'native_collision_set eqb0 fuel depth full_hash key value stored_hash entries' "$model_file" || {
  echo "native collision update does not use the bounded indexed worker" >&2; exit 1;
}
grep -Fq 'native_collision_remove eqb0 full_hash key stored_hash entries' "$model_file" || {
  echo "native collision removal does not use the bounded indexed worker" >&2; exit 1;
}
for worker in native_get native_set native_remove; do
  grep -Eq "^let( rec)? $worker" "$model_file" || { echo "missing $worker" >&2; exit 1; }
done
for operation in native_empty native_table_is_empty native_table_get native_table_mem native_table_set native_table_remove native_table_elements native_table_of_list; do
  grep -Eq "^let( rec)? $operation" "$model_file" || { echo "missing native table API $operation" >&2; exit 1; }
done
if [ -f "$scalar_file" ]; then
  for binding in chunk bitmap_has rank bitmap_insert bitmap_remove; do
    grep -Fq "HashTableScalarPrimitives.$binding" "$scalar_file" || {
      echo "missing scalar binding $binding" >&2; exit 1;
    }
  done
  for worker in native_get native_set native_remove; do
    grep -Eq "^let( rec)? $worker" "$model_file" || {
      echo "missing extracted $worker worker" >&2; exit 1;
    }
  done
  scalar_routes=$(grep -Fc 'native_chunk full_hash depth' "$model_file" || true)
  if [ "$scalar_routes" -lt 3 ]; then
    echo "native get/set/remove do not all route through scalar chunk" >&2; exit 1
  fi
fi
echo "Hash-table native-array extraction audit: pseq alone binds to private arrays; recursive native workers remain extracted"
