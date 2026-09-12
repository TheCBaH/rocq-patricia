#!/bin/sh
# Syntactic extraction-boundary guard for source-defined native workers.
# This complements, but never replaces, their source refinement proofs.
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

if rg -q '^Extract (Inlined )?Constant NativeStringWorker\.(native_byte_diff_tag|difference_tag(_acc)?|first_diff_scan_acc|bounded_prefix_scan_acc) ' "$source_file"; then
  echo "a string-worker algorithm has become a handwritten extraction primitive" >&2
  exit 1
fi

for signature in \
  'let rec difference_tag_acc difference offset =' \
  'let rec first_diff_scan_acc left right left_length right_length common byte =' \
  'let rec bounded_prefix_scan_acc left right split_byte split_tag common byte ='; do
  if ! rg -Fq "$signature" "$worker_file"; then
    echo "unexpected native worker recursion/arity: $signature" >&2
    exit 1
  fi
done

if rg -q 'first_diff_scan_fuel|native_xor_diff_tag_from|String\.sub|String\.get|encode_position|decode_position' "$worker_file"; then
  echo "candidate string worker unexpectedly contains fuel or structural access" >&2
  exit 1
fi

echo "Patricia native-string audit: bit, prefix, difference and tag workers have direct primitive shape"
