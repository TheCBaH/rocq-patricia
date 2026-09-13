#!/bin/sh

set -eu

backend_file=${1:-HashMapNative.ml}
public_wrapper=${2:-HashMap.ml}

fail() {
  echo "Hash-table native-array audit failed: $1" >&2
  exit 1
}

[ -f "$backend_file" ] || fail "missing native backend $backend_file"
[ -f "$public_wrapper" ] || fail "missing public wrapper $public_wrapper"

if grep -Eq 'HashTableReference\.|HashMap\.|Hashtbl|Obj\.|Marshal|Unsafe|external ' "$backend_file"; then
  fail "backend delegates to a reference map or uses an unsafe escape"
fi

for operation in get insert replace remove; do
  grep -Fq "HashTablePrimitives.$operation" "$backend_file" ||
    fail "backend does not use private sequence $operation"
done

for worker in get_tree set_tree remove_tree; do
  grep -Fq "let rec $worker" "$backend_file" ||
    fail "backend is missing native $worker worker"
done

if grep -Fq 'HashMapNative' "$public_wrapper"; then
  fail "public wrapper switched to the native backend before the gate closed"
fi

echo "Hash-table native-array audit: private sequence workers only; no reference delegation or unsafe escape; public wrapper remains reference-backed"
