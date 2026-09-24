#!/bin/sh
# Validate the raw JSONL evidence produced by run-hashtable-performance-matrix.
# This deliberately checks provenance and pair metadata in addition to file
# presence, so a partial or dirty multi-revision run cannot be published as a
# matched matrix.
set -eu

if [ "$#" -ne 1 ]; then
  printf 'usage: %s RECORD_DIRECTORY\n' "$0" >&2
  exit 2
fi

output=$1
sizes=${HASHTABLE_MATRIX_SIZES:-'100 2000 10000 100000'}
seeds=${HASHTABLE_MATRIX_SEEDS:-'0 31 104729'}
repetitions=${HASHTABLE_BENCH_REPETITIONS:-7}
warmups=${HASHTABLE_BENCH_WARMUPS:-1}
high_gc_policy=${HASHTABLE_MATRIX_GC_POLICY_HIGH:-minor}
expected=0

case "$high_gc_policy" in
  compact|major|minor) ;;
  *) printf 'Invalid high-size GC policy: %s\n' "$high_gc_policy" >&2; exit 2 ;;
esac

if [ ! -d "$output" ]; then
  printf 'Matrix record directory is missing: %s\n' "$output" >&2
  exit 1
fi

require_record() {
  record=$1
  size=$2
  seed=$3
  case "$size" in
    100|2000) live_heap=true; pre_sample_gc=compact ;;
    *) live_heap=false; pre_sample_gc=$high_gc_policy ;;
  esac
  if [ ! -s "$record" ]; then
    printf 'Matrix record is missing or empty: %s\n' "$record" >&2
    exit 1
  fi
  if ! jq -se --argjson size "$size" --argjson seed "$seed" \
      --argjson repetitions "$repetitions" --argjson warmups "$warmups" \
      --argjson live_heap "$live_heap" --arg pre_sample_gc "$pre_sample_gc" '
        map(select(.record == "metadata")) as $metadata |
        ($metadata | length == 1) and
        ($metadata[0].size == $size) and ($metadata[0].seed == $seed) and
        ($metadata[0].repetitions == $repetitions) and
        ($metadata[0].warmups == $warmups) and
        ($metadata[0].live_heap == $live_heap) and
        (($metadata[0].pre_sample_gc // "compact") == $pre_sample_gc) and
        ($metadata[0].revision != "unknown") and
        ($metadata[0].dirty == "false")
      ' "$record" >/dev/null; then
    printf 'Matrix metadata is invalid or not clean: %s\n' "$record" >&2
    exit 1
  fi
  if ! jq -e 'select(.record == "sample")' "$record" >/dev/null; then
    printf 'Matrix has no samples: %s\n' "$record" >&2
    exit 1
  fi
  if ! jq -e 'select(.record == "summary")' "$record" >/dev/null; then
    printf 'Matrix has no summaries: %s\n' "$record" >&2
    exit 1
  fi
  expected=$((expected + 1))
}

require_pair() {
  left=$1
  right=$2
  left_metadata=$(jq -rc 'select(.record == "metadata") | [.workload, .size, .seed, .repetitions, .warmups, .live_heap, (.pre_sample_gc // "compact"), .revision, .dirty] | @json' "$left")
  right_metadata=$(jq -rc 'select(.record == "metadata") | [.workload, .size, .seed, .repetitions, .warmups, .live_heap, (.pre_sample_gc // "compact"), .revision, .dirty] | @json' "$right")
  if [ "$left_metadata" != "$right_metadata" ]; then
    printf 'Matrix pair metadata differs: %s / %s\n' "$left" "$right" >&2
    exit 1
  fi
}

require_paired_pattern() {
  size=$1
  seed=$2
  pattern=$3
  hamt="$output/integer-size${size}-seed${seed}-${pattern}.jsonl"
  patricia="$output/patricia-integer-size${size}-seed${seed}-${pattern}.jsonl"
  require_record "$hamt" "$size" "$seed"
  require_record "$patricia" "$size" "$seed"
  require_pair "$hamt" "$patricia"
}

require_paired_string() {
  size=$1
  seed=$2
  pattern=$3
  hamt="$output/string-size${size}-seed${seed}-${pattern}.jsonl"
  patricia="$output/patricia-string-size${size}-seed${seed}-${pattern}.jsonl"
  require_record "$hamt" "$size" "$seed"
  require_record "$patricia" "$size" "$seed"
  require_pair "$hamt" "$patricia"
}

for size in $sizes; do
  for seed in $seeds; do
    for pattern in ascending shuffled root-slot-collision; do
      require_paired_pattern "$size" "$seed" "$pattern"
    done
    case "$size" in
      100|2000)
        require_paired_pattern "$size" "$seed" constant-hash
        for pattern in divergence-depth-0 divergence-depth-1 divergence-depth-2 \
          divergence-depth-3 divergence-depth-4 divergence-depth-5; do
          require_paired_pattern "$size" "$seed" "$pattern"
        done
        ;;
    esac
    for pattern in fixed-width mixed-length common-prefix; do
      require_paired_string "$size" "$seed" "$pattern"
    done
  done
done

actual=$(find "$output" -maxdepth 1 -type f -name '*.jsonl' | wc -l)
if [ "$actual" -ne "$expected" ]; then
  printf 'Matrix record count mismatch: expected %s, found %s\n' "$expected" "$actual" >&2
  exit 1
fi

revisions=$(jq -r 'select(.record == "metadata") | .revision' "$output"/*.jsonl | sort -u | wc -l)
if [ "$revisions" -ne 1 ]; then
  printf 'Matrix records span multiple revisions\n' >&2
  exit 1
fi

printf 'Validated %s clean matched matrix records in %s\n' "$actual" "$output"
