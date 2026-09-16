#!/bin/sh

set -eu

interface_file=${1:-hashtable_reference_extracted/HashTable.mli}

fail() {
  echo "Hash-table generated-interface audit failed: $1" >&2
  exit 1
}

[ -f "$interface_file" ] || fail "missing generated interface $interface_file"

for declaration in \
  "type ('k, 'a) tree" \
  "type ('k, 'seed, 'a) table" \
  "val empty" "val is_empty" "val bindings" "val elements" \
  "val get" "val mem" "val set" "val remove" "val singleton" \
  "val of_list" "val join_worker"; do
  grep -Fq "$declaration" "$interface_file" ||
    fail "expected declaration missing: $declaration"
done

# Extraction maps Coq's bounded N values to OCaml ints.  Keep this boundary
# explicit: callbacks and the stored routing fields must not leak a foreign
# numeric representation into the generated reference package.
grep -Eq '^\| Leaf of int \*' "$interface_file" ||
  fail "leaf hash is not represented as an OCaml int"
grep -Eq '^val get :$' "$interface_file" ||
  fail "public lookup declaration missing"
grep -Fq -- "-> int)" "$interface_file" ||
  fail "seeded hash callback does not return an OCaml int"

if grep -Eqi '(^|[^[:alnum:]_])(external|Obj|Marshal|Unsafe)([^[:alnum:]_]|$)' \
    "$interface_file"; then
  fail "generated interface exposes an unsafe or foreign declaration"
fi

echo "Hash-table generated-interface audit: expected source-map surface; OCaml-int hashes; no unsafe or foreign declarations"
