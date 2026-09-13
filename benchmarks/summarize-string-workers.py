#!/usr/bin/env python3
"""Summarize every string workload in the interleaved acceptance logs.

CSV retains medians, extrema, allocation and sample counts for review. The
default report flags disjoint timing ranges and allocation growth; these
are investigation prompts, not statistical or semantic proofs.
"""
import argparse
import csv
import re
import statistics
import sys
from collections import defaultdict
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("directory", type=Path)
parser.add_argument("--csv", action="store_true")
parser.add_argument("--size", type=int)
parser.add_argument("--minimum-samples", type=int, default=3)
args = parser.parse_args()
rows = defaultdict(list)
for path in sorted(args.directory.glob("*-*-*.log")):
    match = re.fullmatch(r"(Baseline|Bit|Prefix|Diff|All)-(\d+)-(\d+)\.log", path.name)
    if not match:
        continue
    variant, size, sample = match.groups()
    if args.size is not None and int(size) != args.size:
        continue
    contents = path.read_text()
    if "Patricia comparison benchmark: ok" not in contents:
        raise SystemExit(f"Incomplete benchmark: {path}")
    scenario = None
    for line in contents.splitlines():
        if line.startswith("String keys"):
            scenario = line.removesuffix(" (random insertion order)")
        if scenario is None or not line.startswith("  Patricia "):
            continue
        found = re.match(r"  Patricia\s+(.+?)\s+(?:median\s+)?([\d.]+) ms.*?allocated\s+(\d+) words", line)
        if not found:
            raise SystemExit(f"Unparsed measurement in {path}: {line}")
        operation, ms, words = found.groups()
        ns = re.search(r"([\d.]+) ns/op", line)
        # Preserve higher-resolution per-operation times when available.
        time = float(ns.group(1)) if ns else float(ms) * 1e6
        rows[(int(size), scenario, operation, variant)].append((time, int(words)))

summaries = {}
for key, values in rows.items():
    if len(values) < args.minimum_samples:
        raise SystemExit(f"Only {len(values)} samples for {key}; require {args.minimum_samples}")
    times, words = zip(*values)
    summaries[key] = (len(values), statistics.median(times), min(times), max(times),
                      statistics.median(words), min(words), max(words))

if args.csv:
    writer = csv.writer(sys.stdout)
    writer.writerow(("size", "scenario", "operation", "variant", "samples", "median_ns",
                     "min_ns", "max_ns", "median_words", "min_words", "max_words"))
    for key, values in sorted(summaries.items()):
        writer.writerow((*key, *values))
else:
    print("Timing ranges fully above baseline (investigate, do not auto-accept):")
    for key, values in sorted(summaries.items()):
        if key[-1] == "Baseline":
            continue
        baseline = summaries[(*key[:-1], "Baseline")]
        if values[2] > baseline[3]:
            ratio = values[1] / baseline[1] if baseline[1] else float("inf")
            print(key, f"{ratio:.3f}x", "ns", baseline[1:4], "->", values[1:4])
    print("Median allocation above baseline:")
    for key, values in sorted(summaries.items()):
        if key[-1] == "Baseline":
            continue
        baseline = summaries[(*key[:-1], "Baseline")]
        if values[4] > baseline[4]:
            print(key, "words", baseline[4:], "->", values[4:])
