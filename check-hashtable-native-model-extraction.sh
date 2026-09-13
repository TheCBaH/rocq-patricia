#!/bin/sh

set -eu

model_file=${1:-hashtable_extracted/HashTableNative.ml}

fail() {
  echo "Hash-table native-model extraction audit failed: $1" >&2
  exit 1
}

[ -f "$model_file" ] || fail "missing extracted native model $model_file"

grep -Fq "type 'a pseq =" "$model_file" ||
  fail "extracted persistent sequence type is missing"
grep -Fq "'a list" "$model_file" ||
  fail "modeled sequence is not visibly list-backed"

for operation in pseq_get pseq_insert pseq_replace pseq_remove; do
  grep -Fq "let $operation" "$model_file" ||
    fail "extracted persistent sequence operation $operation is missing"
done

grep -Fq 'get_tree eqb fuel depth full_hash key (source_of_native native)' "$model_file" ||
  fail "native_get does not visibly delegate through the source worker"
grep -Fq '(set_tree eqb fuel depth full_hash key value (source_of_native native))' "$model_file" ||
  fail "native_set does not visibly delegate through the source worker"
grep -Fq '(remove_tree eqb fuel depth full_hash key (source_of_native native))' "$model_file" ||
  fail "native_remove does not visibly delegate through the source worker"

echo "Hash-table native-model extraction audit: list-modeled sequence and source-worker delegation confirmed; no array binding claimed"
