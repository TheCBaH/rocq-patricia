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

grep -Eq '^let( rec)? native_get' "$model_file" ||
  fail "native_get is missing"
grep -Fq 'native_get eqb0 fuel' "$model_file" ||
  fail "native_get does not visibly recurse through compact children"
grep -Eq '^let( rec)? native_set' "$model_file" ||
  fail "native_set is missing"
grep -Fq 'native_set eqb0 fuel' "$model_file" ||
  fail "native_set does not visibly recurse through compact children"
grep -Fq 'native_branch_replace bitmap slot' "$model_file" ||
  fail "native_set does not visibly replace a compact child"
grep -Fq 'native_branch_insert bitmap slot' "$model_file" ||
  fail "native_set does not visibly insert a compact child"
grep -Fq 'set_tree eqb0 fuel depth full_hash key value' "$model_file" ||
  fail "native_set has no source fallback for non-branch nodes"
grep -Fq 'remove_tree eqb0 fuel depth full_hash key (source_of_native native)' "$model_file" ||
  fail "native_remove does not visibly delegate through the source worker"

echo "Hash-table native-model extraction audit: list-modeled sequence, recursive get/set, and source-refined removal confirmed; no array binding claimed"
