#!/bin/sh
# Run the corrected HAMT baseline matrix.  This is intentionally outside CI:
# wall-clock measurements are local evidence, while each child harness writes
# its raw samples and machine metadata to a separate JSONL file.
set -eu

output=${HASHTABLE_MATRIX_OUTPUT:-}
if [ -z "$output" ]; then
  output=$(mktemp -d /tmp/hashtable-performance-matrix.XXXXXX)
else
  mkdir -p "$output"
fi

sizes=${HASHTABLE_MATRIX_SIZES:-'100 2000 10000 100000'}
seeds=${HASHTABLE_MATRIX_SEEDS:-'0 31 104729'}
repetitions=${HASHTABLE_BENCH_REPETITIONS:-7}

run_integer() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/integer-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_RESULTS=$record make hashtable-benchmark
}

run_patricia_integer() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/patricia-integer-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_RESULTS=$record make patricia-matrix-benchmark
}

require_record() {
  record=$1
  if [ ! -s "$record" ]; then
    printf 'Expected nonempty matrix record: %s\n' "$record" >&2
    exit 1
  fi
}

run_string() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/string-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_STRING_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_RESULTS=$record make hashtable-string-benchmark
}

for size in $sizes; do
  for seed in $seeds; do
    for pattern in ascending shuffled root-slot-collision; do
      run_integer "$size" "$seed" "$pattern"
      run_patricia_integer "$size" "$seed" "$pattern"
      require_record "$output/integer-size${size}-seed${seed}-${pattern}.jsonl"
      require_record "$output/patricia-integer-size${size}-seed${seed}-${pattern}.jsonl"
    done
    case "$size" in
      100|2000)
        run_integer "$size" "$seed" constant-hash
        run_patricia_integer "$size" "$seed" constant-hash
        require_record "$output/integer-size${size}-seed${seed}-constant-hash.jsonl"
        require_record "$output/patricia-integer-size${size}-seed${seed}-constant-hash.jsonl"
        ;;
      *) printf 'Skipping constant-hash size %s (planned cap: 100/2000)\n' "$size" ;;
    esac
    for pattern in fixed-width mixed-length common-prefix; do
      run_string "$size" "$seed" "$pattern"
      require_record "$output/string-size${size}-seed${seed}-${pattern}.jsonl"
    done
  done
done

printf 'HAMT performance matrix JSONL records: %s\n' "$output"
