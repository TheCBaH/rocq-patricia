#!/bin/sh
# Negative fixtures for the public native-array extraction shape audit.
set -eu

model_file=${1:-hashtable_native_array_extracted/HashTableNative.ml}
audit=${2:-./check-hashtable-native-array-extraction.sh}
[ -f "$model_file" ] || { echo "missing extracted native array model" >&2; exit 1; }
[ -f "$audit" ] || { echo "missing extraction audit" >&2; exit 1; }

fixture_dir=$(mktemp -d "${TMPDIR:-/tmp}/hashtable-native-audit.XXXXXX")
trap 'rm -rf "$fixture_dir"' EXIT HUP INT TERM

hot_view="$fixture_dir/hot-view.ml"
sed '/^let rec native_get /a\
  let _ = HashTablePrimitives.to_list entries in' "$model_file" > "$hot_view"
if sh "$audit" "$hot_view" >/dev/null 2>&1; then
  echo "extraction audit accepted a hot sequence-view conversion" >&2
  exit 1
fi

hot_depth_view="$fixture_dir/hot-depth-view.ml"
sed '/^let native_get_depth0 /a\
  let _ = HashTablePrimitives.to_list entries in' "$model_file" > "$hot_depth_view"
if sh "$audit" "$hot_depth_view" >/dev/null 2>&1; then
  echo "extraction audit accepted a direct-depth sequence-view conversion" >&2
  exit 1
fi

whole_override="$fixture_dir/whole-override.ml"
sed 's/^let rec native_set /let native_set /' "$model_file" > "$whole_override"
if sh "$audit" "$whole_override" >/dev/null 2>&1; then
  echo "extraction audit accepted a non-recursive native_set override" >&2
  exit 1
fi

bucket_override="$fixture_dir/bucket-override.ml"
sed 's/^let rec native_bucket_get = HashTablePrimitives.bucket_get$/let rec native_bucket_get = HashTablePrimitives.bucket_remove/' "$model_file" > "$bucket_override"
if sh "$audit" "$bucket_override" >/dev/null 2>&1; then
  echo "extraction audit accepted a wrong bucket primitive binding" >&2
  exit 1
fi

echo "Hash-table native-array extraction audit negative fixtures passed"
