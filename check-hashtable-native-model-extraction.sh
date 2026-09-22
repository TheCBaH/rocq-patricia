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

for operation in pseq_get pseq_length pseq_is_empty pseq_insert pseq_replace pseq_remove; do
  grep -Fq "let $operation" "$model_file" ||
    fail "extracted persistent sequence operation $operation is missing"
done

grep -Eq '^let rec native_get' "$model_file" ||
  fail "native_get is missing"
grep -Fq 'native_get eqb0 fuel' "$model_file" ||
  fail "native_get does not visibly recurse through compact children"
grep -Eq '^let rec native_set' "$model_file" ||
  fail "native_set is missing"
grep -Fq 'native_set eqb0 fuel' "$model_file" ||
  fail "native_set does not visibly recurse through compact children"
grep -Fq 'native_branch_replace_at bitmap index' "$model_file" ||
  fail "native_set does not visibly replace a compact child"
grep -Fq 'native_branch_insert_at bitmap slot index' "$model_file" ||
  fail "native_set does not visibly insert a compact child"
grep -Fq 'native_join_worker fuel depth full_hash' "$model_file" ||
  fail "native_set does not visibly use the direct native join worker"
grep -Fq 'native_collision_set eqb0 fuel depth full_hash key value' "$model_file" ||
  fail "native_set does not visibly use the direct collision update worker"
grep -Eq '^let rec native_remove' "$model_file" ||
  fail "native_remove is missing"
grep -Fq 'native_remove eqb0 fuel' "$model_file" ||
  fail "native_remove does not visibly recurse through compact children"
grep -Fq 'native_branch_remove_at bitmap slot index' "$model_file" ||
  fail "native_remove does not visibly compact an empty child"
grep -Fq 'native_branch_replace_at bitmap index' "$model_file" ||
  fail "native_remove does not visibly replace a compact child"
grep -Fq 'native_collision_remove eqb0 full_hash key stored_hash entries' "$model_file" ||
  fail "native_remove does not visibly use the direct collision removal worker"

for worker in native_get native_set native_remove native_table_add_first native_table_of_list; do
  if ! awk -v worker="$worker" '
    $0 ~ "^let( rec)? " worker " " { in_worker = 1; next }
    in_worker && /^\(\*\*/ { exit bad }
    in_worker && /source_of_native|native_of_source|pseq_view/ { bad = 1 }
    END { exit bad }
  ' "$model_file"; then
    fail "$worker still contains a source-tree or sequence-view conversion"
  fi
done

echo "Hash-table native-model extraction audit: list-modeled sequence and direct recursive get/set/remove workers confirmed; no array binding claimed"
