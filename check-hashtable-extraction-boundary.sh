#!/bin/sh

set -eu

interface_file=${1:-HashMap.mli}
implementation_file=${2:-HashMap.ml}

fail() {
  echo "Hash-table extraction boundary audit failed: $1" >&2
  exit 1
}

[ -f "$interface_file" ] || fail "missing public interface $interface_file"
[ -f "$implementation_file" ] || fail "missing public wrapper $implementation_file"

grep -Eq '^  type '\''a t$' "$interface_file" ||
  fail "public map type is not abstract"

if sed '/^(\*/d; /^(\*\*)/d' "$interface_file" |
   grep -Eq 'HashTable\.|tree|table_seed|table_root|join_worker|set_tree|remove_tree|full_hash|fuel|depth'; then
  fail "internal representation or worker escaped through the public interface"
fi

grep -Fq 'let normalize_hash raw = raw land 0x3fffffff' "$implementation_file" ||
  fail "wrapper does not normalize raw hashes to 30 bits"

grep -Fq 'Key.hash ~seed key' "$implementation_file" ||
  fail "wrapper does not call the functor-bound hash callback"

grep -Fq 'Key.equal' "$implementation_file" ||
  fail "wrapper does not use the functor-bound equality callback"

grep -Fq 'HashTableNative.' "$implementation_file" ||
  fail "wrapper does not use the generated native table package"

if grep -Eq 'HashTableReference\.|HashTable\.' "$implementation_file"; then
  fail "wrapper depends directly on the generated HashTable module"
fi

echo "Hash-table extraction boundary audit: public type abstract; routing internals hidden; callbacks normalized and functor-bound; generated native table package used"
