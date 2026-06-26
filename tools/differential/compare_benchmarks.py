#!/usr/bin/env python3
"""
Compare two benchmark results directories.
Usage:
    python tools/compare_benchmarks.py <old_results_dir> <new_results_dir>
"""

import csv
import sys
from pathlib import Path
from collections import Counter

def load_results(results_dir):
    results = {}
    csv_path = Path(results_dir) / "results.csv"
    if not csv_path.exists():
        print(f"Error: {csv_path} not found")
        sys.exit(1)
    with open(csv_path) as f:
        reader = csv.DictReader(f)
        for row in reader:
            results[row['file']] = row
    return results

def compare(old_results, new_results):
    old_only = set(old_results.keys()) - set(new_results.keys())
    new_only = set(new_results.keys()) - set(old_results.keys())
    common = set(old_results.keys()) & set(new_results.keys())

    print(f"Old results: {len(old_results)} files")
    print(f"New results: {len(new_results)} files")
    print(f"Common files: {len(common)}")
    if old_only:
        print(f"Only in old: {len(old_only)}")
    if new_only:
        print(f"Only in new: {len(new_only)}")
    print()

    mismatches = []
    old_timeouts = 0
    new_timeouts = 0
    old_faster = 0
    new_faster = 0
    time_diffs = []

    for f in sorted(common):
        old = old_results[f]
        new = new_results[f]
        old_res = old['xolver_result']
        new_res = new['xolver_result']
        old_time = float(old['xolver_time'])
        new_time = float(new['xolver_time'])

        if old_res == 'timeout':
            old_timeouts += 1
        if new_res == 'timeout':
            new_timeouts += 1

        if old_res != new_res:
            mismatches.append((f, old_res, new_res, old_time, new_time))

        if old_time > 0 and new_time > 0:
            if new_time < old_time:
                new_faster += 1
            elif old_time < new_time:
                old_faster += 1
            time_diffs.append(new_time - old_time)

    print("=== Result Mismatches ===")
    if mismatches:
        for f, old_r, new_r, old_t, new_t in mismatches:
            print(f"  {f}: {old_r} -> {new_r} ({old_t:.2f}s -> {new_t:.2f}s)")
        print(f"Total mismatches: {len(mismatches)}")
    else:
        print("No mismatches!")
    print()

    print("=== Timeout Comparison ===")
    print(f"  Old timeouts: {old_timeouts}")
    print(f"  New timeouts: {new_timeouts}")
    print(f"  Improvement: {old_timeouts - new_timeouts}")
    print()

    print("=== Speed Comparison (non-timeout instances) ===")
    print(f"  Old faster: {old_faster}")
    print(f"  New faster: {new_faster}")
    if time_diffs:
        avg_diff = sum(time_diffs) / len(time_diffs)
        print(f"  Avg time diff (new - old): {avg_diff:.3f}s")
    print()

    print("=== Category Breakdown (mismatches) ===")
    cats = Counter()
    for f, _, _, _, _ in mismatches:
        cat = f.split('/')[0] if '/' in f else 'unknown'
        cats[cat] += 1
    for cat, count in cats.most_common():
        print(f"  {cat}: {count}")

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: python compare_benchmarks.py <old_dir> <new_dir>")
        sys.exit(1)
    old_results = load_results(sys.argv[1])
    new_results = load_results(sys.argv[2])
    compare(old_results, new_results)
