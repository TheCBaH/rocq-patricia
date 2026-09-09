#!/bin/sh
# Keep the trusted high-level extraction boundary intentional and small. Low
# level primitive realizers are audited separately in SPECIFICATION.md.
set -eu

source_file=${1:-PatriciaExtract.v}

if rg -n '^Extract Constant (Patricia|StringPatricia)\.(set|combine) =>' \
    "$source_file"; then
  echo "unexpected handwritten high-level set/combine realizer" >&2
  exit 1
fi

union_count=$(rg -c '^Extract Constant (Patricia|StringPatricia)\.union_(left|right) =>' \
  "$source_file" || true)
union_count=${union_count:-0}

if [ "$union_count" -ne 0 ]; then
  echo "expected no handwritten high-level union realizers, found $union_count" >&2
  exit 1
fi

echo "Patricia extraction-boundary audit: no handwritten high-level union realizer"
