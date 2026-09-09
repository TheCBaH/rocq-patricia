#!/bin/sh
# Generated-code guard for the source-defined cached representative migration.
# This is a boundary audit, not a refinement proof: it prevents the public
# removal/filter/combine workers from silently returning to the total
# structural representative after extraction.
set -eu

generated=${1:?usage: $0 extracted/StringPatriciaInternal.ml}

worker_body () {
  worker=$1
  awk -v worker="$worker" '
    $0 ~ "^let rec " worker " " || $0 ~ "^let " worker " " {
      active = 1
    }
    active && /^\(\*\* val / { exit }
    active { print }
  ' "$generated"
}

require_cached () {
  worker=$1
  body=$(worker_body "$worker")
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

require_cached remove_changed_cached
require_cached map_filter_cached
require_cached combine_fuel
require_cached combine_structural

echo "Patricia cached-consumer audit: public string workers use cached branch/join"
