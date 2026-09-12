#!/bin/sh
# Build each binding independently, then interleave the same map workloads.
# Fixtures are benchmark-only; production extraction is never patched here.
set -eu
root=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$root"
ocamlopt=${OCAMLOPT:-/opt/opam/4.14.3/bin/ocamlopt}
ocamldep=${OCAMLDEP:-/opt/opam/4.14.3/bin/ocamldep}
rounds=${PATRICIA_STRING_ROUNDS:-3}
sizes=${PATRICIA_STRING_SIZES:-"10000 100000"}
variants=${PATRICIA_STRING_VARIANTS:-"Baseline Bit Prefix Diff All"}
results=$(mktemp -d "${TMPDIR:-/tmp}/patricia-string-acceptance.XXXXXX")
printf 'String-worker acceptance artifacts: %s\n' "$results"
benchmark_pid=""
trap 'if [ -n "$benchmark_pid" ]; then kill "$benchmark_pid" 2>/dev/null || :; fi; exit 130' INT TERM HUP
printf '%s\n' "rounds=$rounds" "sizes=$sizes" "variants=$variants" \
  "short_batch=${PATRICIA_BENCH_SHORT_BATCH:-32}" \
  "short_samples=${PATRICIA_BENCH_SHORT_SAMPLES:-5}" \
  "long_prefix_length=${PATRICIA_BENCH_LONG_PREFIX_LENGTH:-192}" \
  "fast_comparisons=1" > "$results/workload-config.log"
make extraction > "$results/extraction.log" 2>&1
make compiler-config > "$results/compiler-config.log" 2>&1
sha256sum NativeStringWorker.v PatriciaExtract.v PatriciaBenchmark.ml benchmarks/*.ml \
  > "$results/source-sha256.log"
for variant in $variants; do
  build="$results/$variant"
  mkdir "$build"
  cp extracted/*.ml extracted/*.mli "$build/"
  cp benchmarks/StringBitsBaseline.ml "$build/"
  if [ "$variant" = Baseline ]; then
    cp benchmarks/StringBitsHistorical.ml "$build/StringBits.ml"
  else
    cp "benchmarks/StringBits$variant.ml" "$build/StringBits.ml"
  fi
  cp PatriciaMap.ml PatriciaMap.mli StringPatriciaMap.ml StringPatriciaMap.mli \
    PatriciaBenchmark.ml "$build/"
  (cd "$build"
   "$ocamlopt" -c $("$ocamldep" -sort ./*.mli ./*.ml)
   objects=$("$ocamldep" -sort ./*.ml | sed 's/\.ml/.cmx/g')
   "$ocamlopt" unix.cmxa -o benchmark $objects)
done
for size in $sizes; do
  round=1
  while [ "$round" -le "$rounds" ]; do
    # Alternate order to avoid assigning warmup/drift to one implementation.
    order=$variants
    if [ $((round % 2)) -eq 0 ]; then
      order=""
      for variant in $variants; do order="$variant $order"; done
    fi
    for variant in $order; do
      log="$results/$variant-$size-$round.log"
      PATRICIA_BENCH_SIZE="$size" PATRICIA_BENCH_STRING_LENGTHS=4 \
      PATRICIA_BENCH_FAST_COMPARISONS=1 \
      PATRICIA_BENCH_VARIABLE_STRING_MAX_LENGTH=4 \
        "$results/$variant/benchmark" > "$log" &
      benchmark_pid=$!
      wait "$benchmark_pid"
      benchmark_pid=""
      rg -q 'Patricia comparison benchmark: ok' "$log"
      printf '%s size=%s round=%s: passed\n' "$variant" "$size" "$round"
    done
    round=$((round + 1))
  done
done
printf 'Completed acceptance series: %s\n' "$results"
