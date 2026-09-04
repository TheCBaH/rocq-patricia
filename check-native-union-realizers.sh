#!/bin/sh
# Check the generated high-level union overrides after extraction.  These
# overrides are intentionally handwritten, so keep their sole physical-
# equality use narrow and reviewable: every [(==)] test must compare a
# recursively produced tree with the original child whose enclosing branch may
# be reused.  This is a source-level boundary audit, not a proof of OCaml heap
# or compiler semantics.
set -eu

integer_file=${1:?usage: check-native-union-realizers.sh INTEGER_ML STRING_ML}
string_file=${2:?usage: check-native-union-realizers.sh INTEGER_ML STRING_ML}

for file in "$integer_file" "$string_file"; do
  if [ ! -f "$file" ]; then
    echo "missing extracted union realizer: $file" >&2
    exit 1
  fi
done

check_realizer () {
  label=$1
  file=$2
  shift 2

  # The four one-child containment paths and the two-child equal-header path
  # give exactly six tests.  A changed count requires reviewing the proof
  # bridge and this audit together.
  physical_count=$(rg -F -o '==' "$file" | wc -l)
  if [ "$physical_count" -ne 6 ]; then
    echo "$label union audit: expected six physical child tests, found $physical_count" >&2
    exit 1
  fi

  for expression in "$@"; do
    if ! rg -F "$expression" "$file" >/dev/null; then
      echo "$label union audit: missing tree-child physical test: $expression" >&2
      exit 1
    fi
  done
}

check_realizer integer "$integer_file" \
  'merged_left == left_left && merged_right == right_left' \
  'merged == left_left' \
  'merged == right_left' \
  'merged == left_right' \
  'merged == right_right'

if ! rg -F 'let union_right = (fun first second -> union_left second first)' \
    "$integer_file" >/dev/null; then
  echo "integer union audit: union_right no longer delegates by argument swap" >&2
  exit 1
fi

check_realizer string "$string_file" \
  'merged_left == left_left && merged_right == right_left' \
  'merged == left_left' \
  'merged == right_left' \
  'merged == left_right' \
  'merged == right_right'

if ! rg -F 'let union_right = (fun first second -> union_left second first)' \
    "$string_file" >/dev/null; then
  echo "string union audit: union_right no longer delegates by argument swap" >&2
  exit 1
fi

echo "Patricia native-union audit: child-only physical equality and swapped right bias"
