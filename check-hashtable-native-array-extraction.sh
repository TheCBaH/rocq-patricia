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
for operation in get set remove; do
  grep -Fq "let rec native_bucket_$operation = HashTablePrimitives.bucket_$operation" "$model_file" || {
    echo "native bucket $operation is not bound to the checked array adapter" >&2; exit 1;
  }
done
grep -Eq 'native_bucket_get eqb[0-9]* key entries 0 \(pseq_length entries\)' "$model_file" || {
  echo "native collision lookup does not use the bounded indexed worker" >&2; exit 1;
}
grep -Eq 'native_collision_set eqb[0-9]* fuel depth full_hash key value stored_hash entries' "$model_file" || {
  echo "native collision update does not use the bounded indexed worker" >&2; exit 1;
}
grep -Eq 'native_collision_remove eqb[0-9]* full_hash key stored_hash entries' "$model_file" || {
  echo "native collision removal does not use the bounded indexed worker" >&2; exit 1;
}
for worker in native_get native_set native_remove; do
  grep -Eq "^let rec $worker" "$model_file" || {
    echo "missing extracted recursive $worker worker" >&2; exit 1;
  }
done
for depth in 0 1 2 3 4 5 6; do
  grep -Eq "^let native_get_depth$depth " "$model_file" || {
    echo "missing source-defined lookup depth $depth" >&2; exit 1;
  }
done
for depth in 0 1 2 3 4 5; do
  next=$((depth + 1))
  grep -Fq "native_get_depth$next eqb full_hash key child" "$model_file" || {
    echo "lookup depth $depth does not call the next direct worker" >&2; exit 1;
  }
done
grep -Fq 'native_get_depth0 eqb (hash native.native_table_seed key) key' "$model_file" || {
  echo "public lookup does not use the direct depth worker" >&2; exit 1;
}
for worker in native_join_two native_join_worker; do
  grep -Eq "^let( rec)? $worker" "$model_file" || {
    echo "missing direct native join worker $worker" >&2; exit 1;
  }
done
grep -Fq 'else native_join_worker fuel depth full_hash (NativeLeaf' "$model_file" || {
  echo "distinct-hash leaf/collision updates still use a source join fallback" >&2; exit 1;
}
for worker in native_get native_get_depth0 native_get_depth1 native_get_depth2 native_get_depth3 native_get_depth4 native_get_depth5 native_get_depth6 native_set native_remove native_table_add_first native_table_of_list; do
  if ! awk -v worker="$worker" '
    $0 ~ "^let( rec)? " worker " " { in_worker = 1; next }
    in_worker && /^\(\*\*/ { exit bad }
    in_worker && /source_of_native|native_of_source|pseq_view|HashTablePrimitives\.to_list/ { bad = 1 }
    END { exit bad }
  ' "$model_file"; then
    echo "$worker still contains a source-tree or sequence-view conversion" >&2; exit 1;
  fi
done
for operation in native_empty native_table_is_empty native_table_get native_table_mem native_table_set native_table_remove native_table_elements native_table_of_list; do
  grep -Eq "^let( rec)? $operation" "$model_file" || { echo "missing native table API $operation" >&2; exit 1; }
done
if [ -f "$scalar_file" ]; then
  for binding in chunk bounded_eq slot_lt bitmap_has rank bitmap_insert bitmap_remove; do
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
  grep -Fq 'native_bounded_eq full_hash stored_hash' "$model_file" || {
    echo "native hash comparison still bypasses bounded equality" >&2; exit 1;
  }
  grep -Fq 'native_slot_lt left_slot right_slot' "$model_file" || {
    echo "native join order still bypasses bounded comparison" >&2; exit 1;
  }
fi
echo "Hash-table native-array extraction audit: pseq alone binds to private arrays; recursive native workers remain extracted"
