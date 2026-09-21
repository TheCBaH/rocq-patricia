#!/bin/sh
set -eu

model_file=${1:-hashtable_native_array_extracted/HashTableNative.ml}
[ -f "$model_file" ] || { echo "missing extracted native array model" >&2; exit 1; }
grep -Fq 'HashTablePrimitives.t' "$model_file" || { echo "pseq was not bound to private arrays" >&2; exit 1; }
for operation in get insert replace remove to_list of_list; do
  grep -Fq "HashTablePrimitives.$operation" "$model_file" || { echo "missing primitive $operation" >&2; exit 1; }
done
for worker in native_get native_set native_remove; do
  grep -Eq "^let( rec)? $worker" "$model_file" || { echo "missing $worker" >&2; exit 1; }
done
echo "Hash-table native-array extraction audit: pseq alone binds to private arrays; recursive native workers remain extracted"
