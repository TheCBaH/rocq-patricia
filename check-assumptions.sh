#!/bin/sh

set -eu

if [ "$#" -lt 1 ]; then
  echo "usage: check-assumptions.sh ROCQ [ROCQ-FLAGS...]" >&2
  exit 2
fi

rocq_command=$1
shift

audit_output=$(mktemp)
trap 'rm -f "$audit_output"' EXIT HUP INT TERM

proof_sources=""
declaration_count=0
for source_file in ./*.v; do
  source_count=$(awk '
    /^(Lemma|Theorem|Corollary)[[:space:]]/ { count++ }
    END { print count + 0 }
  ' "$source_file")
  if [ "$source_count" -gt 0 ]; then
    source=${source_file#./}
    source=${source%.v}
    proof_sources="$proof_sources $source"
    declaration_count=$((declaration_count + source_count))
  fi
done

{
  printf "Require Import"
  for source in $proof_sources; do
    printf " %s" "$source"
  done
  echo "."
  for source in $proof_sources; do
    awk -v module="$source" '
      /^(Lemma|Theorem|Corollary)[[:space:]]/ {
        name = $2
        sub(/:.*/, "", name)
        printf "Print Assumptions %s.%s.\n", module, name
      }
    ' "$source.v"
  done
  echo "Quit."
} | "$rocq_command" repl "$@" >"$audit_output" 2>&1

closed_count=$(
  awk '/Closed under the global context/ { count++ } END { print count + 0 }' \
    "$audit_output"
)

if [ "$declaration_count" -eq 0 ] ||
   [ "$closed_count" -ne "$declaration_count" ] ||
   grep -Eq 'Axioms:|Assumptions:|Error:|Anomaly:' "$audit_output"; then
  cat "$audit_output" >&2
  echo "Patricia assumption audit failed: checked $closed_count of $declaration_count declarations" >&2
  exit 1
fi

echo "Patricia assumption audit: $declaration_count declarations closed under the global context"
