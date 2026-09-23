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
warmups=${HASHTABLE_BENCH_WARMUPS:-1}

# Each Make target extracts, compiles, links, and then runs its benchmark.  A
# matrix has many records, so invoking those targets per record would make the
# build dominate the measurement campaign.  Establish a clean provenance once,
# bootstrap each isolated executable once, and execute the linked binary for
# every measured record below.  The benchmark support reads all record-specific
# configuration from its environment.
if ! git diff --quiet --ignore-submodules -- || \
   ! git diff --cached --quiet --ignore-submodules -- || \
   [ -n "$(git status --porcelain --untracked-files=all --ignored=no)" ]; then
  printf 'Refusing to run a matrix from a dirty worktree\n' >&2
  exit 1
fi
revision=$(git rev-parse HEAD)
bootstrap=$(mktemp -d /tmp/hashtable-performance-bootstrap.XXXXXX)
trap 'rm -rf "$bootstrap"' EXIT HUP INT TERM

bootstrap_integer() {
  record=$1
  shift
  HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_SEED=0 \
  HASHTABLE_BENCH_PATTERN=ascending HASHTABLE_BENCH_REPETITIONS=1 \
  HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false "$@"
}

bootstrap_string() {
  record=$1
  shift
  HASHTABLE_BENCH_SIZE=100 HASHTABLE_BENCH_SEED=0 \
  HASHTABLE_BENCH_STRING_PATTERN=fixed-width HASHTABLE_BENCH_REPETITIONS=1 \
  HASHTABLE_BENCH_WARMUPS=1 HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false "$@"
}

bootstrap_integer "$bootstrap/hashtable.jsonl" make hashtable-benchmark
bootstrap_string "$bootstrap/hashtable-string.jsonl" make hashtable-string-benchmark
bootstrap_integer "$bootstrap/patricia.jsonl" make patricia-matrix-benchmark
bootstrap_string "$bootstrap/patricia-string.jsonl" make patricia-string-matrix-benchmark

run_integer() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/integer-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_WARMUPS=$warmups HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false \
  ./hashtable-benchmark
}

run_patricia_integer() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/patricia-integer-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_WARMUPS=$warmups HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false \
  ./patricia-matrix-benchmark
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
  HASHTABLE_BENCH_WARMUPS=$warmups HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false \
  ./hashtable-string-benchmark
}

run_patricia_string() {
  size=$1
  seed=$2
  pattern=$3
  record="$output/patricia-string-size${size}-seed${seed}-${pattern}.jsonl"
  HASHTABLE_BENCH_SIZE=$size HASHTABLE_BENCH_SEED=$seed \
  HASHTABLE_BENCH_STRING_PATTERN=$pattern HASHTABLE_BENCH_REPETITIONS=$repetitions \
  HASHTABLE_BENCH_WARMUPS=$warmups HASHTABLE_BENCH_RESULTS=$record \
  HASHTABLE_BENCH_REVISION=$revision HASHTABLE_BENCH_DIRTY=false \
  ./patricia-string-matrix-benchmark
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
    case "$size" in
      100|2000)
        for pattern in divergence-depth-0 divergence-depth-1 divergence-depth-2 \
          divergence-depth-3 divergence-depth-4 divergence-depth-5; do
          run_integer "$size" "$seed" "$pattern"
          run_patricia_integer "$size" "$seed" "$pattern"
          require_record "$output/integer-size${size}-seed${seed}-${pattern}.jsonl"
          require_record "$output/patricia-integer-size${size}-seed${seed}-${pattern}.jsonl"
        done
        ;;
      *) printf 'Skipping divergence-depth size %s (planned cap: 100/2000)\n' "$size" ;;
    esac
    for pattern in fixed-width mixed-length common-prefix; do
      run_string "$size" "$seed" "$pattern"
      run_patricia_string "$size" "$seed" "$pattern"
      require_record "$output/string-size${size}-seed${seed}-${pattern}.jsonl"
      require_record "$output/patricia-string-size${size}-seed${seed}-${pattern}.jsonl"
    done
  done
done

HASHTABLE_MATRIX_SIZES="$sizes" HASHTABLE_MATRIX_SEEDS="$seeds" \
HASHTABLE_BENCH_REPETITIONS="$repetitions" \
HASHTABLE_BENCH_WARMUPS="$warmups" \
  sh ./validate-hashtable-performance-matrix.sh "$output"

printf 'HAMT performance matrix JSONL records: %s\n' "$output"
