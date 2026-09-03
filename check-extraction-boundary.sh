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

if [ "$union_count" -ne 4 ]; then
  echo "expected exactly four specialized high-level union realizers, found $union_count" >&2
  exit 1
fi

echo "Patricia extraction-boundary audit: only specialized unions remain handwritten"
