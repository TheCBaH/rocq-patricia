#!/bin/sh

set -eu

if [ "$#" -lt 1 ]; then
  echo "usage: check-hashtable-assumptions.sh ROCQ [ROCQ-FLAGS...]" >&2
  exit 2
fi

rocq_command=$1
shift

modules='HashTableSpec HashTableBits HashTableBucket HashTable HashTableProof HashTableSkeleton'
audit_output=$(mktemp)
trap 'rm -f "$audit_output"' EXIT HUP INT TERM

declaration_count=0
for module in $modules; do
  source_file="$module.v"
  source_count=$(awk '
    /^(Lemma|Theorem|Corollary)[[:space:]]/ { count++ }
    END { print count + 0 }
  ' "$source_file")
  declaration_count=$((declaration_count + source_count))
done

{
  printf 'Require Import'
  for module in $modules; do printf ' %s' "$module"; done
  echo '.'
  for module in $modules; do
    awk -v module="$module" '
      /^(Lemma|Theorem|Corollary)[[:space:]]/ {
        name = $2
        sub(/:.*/, "", name)
        printf "Print Assumptions %s.%s.\n", module, name
      }
    ' "$module.v"
  done
  echo 'Quit.'
} | "$rocq_command" repl "$@" >"$audit_output" 2>&1

closed_count=$(awk '/Closed under the global context/ { count++ } END { print count + 0 }' "$audit_output")

if [ "$declaration_count" -eq 0 ] || [ "$closed_count" -ne "$declaration_count" ] ||
   grep -Eq 'Axioms:|Assumptions:|Error:|Anomaly:' "$audit_output"; then
  cat "$audit_output" >&2
  echo "Hash-table assumption audit failed: checked $closed_count of $declaration_count declarations" >&2
  exit 1
fi

echo "Hash-table assumption audit: $declaration_count declarations closed under the global context"
