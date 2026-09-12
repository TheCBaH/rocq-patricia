#!/bin/sh
# Syntactic extraction-boundary guard for the selected packed [bit_at]
# binding.  This complements, but never replaces, its source refinement proof.
set -eu

source_file=${1:-PatriciaExtract.v}
worker_file=${2:-extracted/NativeStringWorker.ml}

if ! rg -Fq 'Extract Constant StringBits.bit_at => "NativeStringWorker.packed_bit_at".' "$source_file"; then
  echo "expected StringBits.bit_at to bind to NativeStringWorker.packed_bit_at" >&2
  exit 1
fi

if rg -q '^open String$|String\.get|String\.sub|native_ascii_prefix_equal' "$worker_file"; then
  echo "native string worker unexpectedly depends on a structural string helper" >&2
  exit 1
fi

if ! rg -q '^let packed_bit_at ' "$worker_file"; then
  echo "missing extracted packed_bit_at worker" >&2
  exit 1
fi

if ! rg -q 'Stdlib\.String\.unsafe_get' "$worker_file"; then
  echo "missing guarded native byte access in packed worker" >&2
  exit 1
fi

if ! rg -q '^let rec first_diff_scan_acc ' "$worker_file"; then
  echo "missing extracted indexed first-difference loop" >&2
  exit 1
fi

if rg -q 'first_diff_scan_fuel|String\.sub|String\.get' "$worker_file"; then
  echo "candidate string worker unexpectedly contains fuel or structural access" >&2
  exit 1
fi

echo "Patricia native-string audit: selected bit and candidate diff workers have direct primitive shape"
