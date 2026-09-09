#!/bin/sh
# Check the generated source-defined closure-free union workers.  This is a
# shape audit, not a proof of OCaml heap or compiler semantics: the one
# remaining [(==)] primitive still has the explicit refinement contract in
# [NativeHeapRefinement.v].
set -eu

integer_file=${1:?usage: check-native-union-realizers.sh INTEGER_ML STRING_ML}
string_file=${2:?usage: check-native-union-realizers.sh INTEGER_ML STRING_ML}

for file in "$integer_file" "$string_file"; do
  if [ ! -f "$file" ]; then
    echo "missing extracted union realizer: $file" >&2
    exit 1
  fi
done

check_worker () {
  label=$1
  file=$2
  if ! rg -F 'let rec union_left_native_acc same original_a original_b a b =' \
      "$file" >/dev/null; then
    echo "$label union audit: missing direct Acc-recursive worker" >&2
    exit 1
  fi
  if ! rg -F 'union_left_native_acc (==) a b a b' "$file" >/dev/null; then
    echo "$label union audit: default worker does not expose the sole physical primitive" >&2
    exit 1
  fi
  worker=$(sed -n '/let rec union_left_native_acc /,/let union_left_native_acc_default/p' "$file")
  if printf '%s\n' "$worker" | rg -F '(size ' >/dev/null ||
     printf '%s\n' "$worker" | rg -F 'let rec ' | wc -l | grep -qv '^1$'; then
    echo "$label union audit: worker retained a size prepass or nested recursion" >&2
    exit 1
  fi
}

check_worker integer "$integer_file"
check_worker string "$string_file"

echo "Patricia native-union audit: direct source-extracted Acc workers"
