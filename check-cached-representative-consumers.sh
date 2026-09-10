#!/bin/sh
# Generated-code guard for the source-defined cached representative migration.
# This is a boundary audit, not a refinement proof: it prevents the public
# removal/filter/combine workers from silently returning to the total
# structural representative after extraction.
set -eu

generated=${1:?usage: $0 extracted/StringPatriciaInternal.ml extracted/StringPatriciaUnion.ml PatriciaExtract.v}
union_generated=${2:?usage: $0 extracted/StringPatriciaInternal.ml extracted/StringPatriciaUnion.ml PatriciaExtract.v}
manifest=${3:?usage: $0 extracted/StringPatriciaInternal.ml extracted/StringPatriciaUnion.ml PatriciaExtract.v}

if grep -Eq '^[[:space:]]*Extract Constant StringPatricia\.representative' "$manifest"; then
  echo "Patricia cached-consumer audit: representative override is present" >&2
  exit 1
fi

worker_body () {
  file=$1
  worker=$2
  awk -v worker="$worker" '
    $0 ~ "^let rec " worker " " || $0 ~ "^let " worker " " {
      active = 1
    }
    active && /^\(\*\* val / { exit }
    active { print }
  ' "$file"
}

require_cached () {
  file=$1
  worker=$2
  body=$(worker_body "$file" "$worker")
  if [ -z "$body" ]; then
    echo "Patricia cached-consumer audit: missing $worker" >&2
    exit 1
  fi
  case $body in
    *branch_cached*|*join_cached*) ;;
    *)
      echo "Patricia cached-consumer audit: $worker has no cached constructor" >&2
      exit 1
      ;;
  esac
  if printf '%s\n' "$body" | grep -Eq '(^|[^_[:alnum:]])(branch|join)[[:space:]]'; then
    echo "Patricia cached-consumer audit: $worker calls regular branch/join" >&2
    exit 1
  fi
}

require_cached "$generated" remove_changed_cached
require_cached "$generated" map_filter_cached
require_cached "$generated" combine_fuel
require_cached "$generated" combine_structural
require_cached "$union_generated" union_left_native_acc

echo "Patricia cached-consumer audit: public string workers use cached branch/join"
