#!/bin/sh

set -eu

implementation_file=${1:-HashTablePrimitives.ml}

fail() {
  echo "Hash-table primitive inventory failed: $1" >&2
  exit 1
}

[ -f "$implementation_file" ] || fail "missing primitive implementation $implementation_file"

if grep -Eq 'HashTable|HashMap|Hashtbl|Obj\.|Marshal|Unsafe|external ' "$implementation_file"; then
  fail "primitive implementation contains a whole-map override or unsafe escape"
fi

grep -Fq "type 'a t = 'a array" "$implementation_file" ||
  fail "primitive storage is not the declared private array representation"

grep -Fq 'let result = Array.make' "$implementation_file" ||
  fail "insert/remove do not visibly allocate fresh storage"

grep -Fq 'let result = Array.copy items' "$implementation_file" ||
  fail "replace does not visibly allocate fresh storage"

echo "Hash-table primitive inventory: private array sequence only; no map override or unsafe escape; fresh update allocation present"
