#!/usr/bin/env python3
"""Sample test runner: pick 50 random files per logic, run with timeout, find crashes."""

import os
import sys
import random
import subprocess
import glob
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ZOLVER_BIN = "./build/bin/zolver"
BENCHMARK_DIR = "benchmark/non-incremental"
TIMEOUT = 10
SAMPLE_SIZE = 50
MAX_WORKERS = 2

# Set seed for reproducibility
random.seed(42)


def find_files(logic: str):
    """Find all .smt2 files for a logic."""
    pattern = os.path.join(BENCHMARK_DIR, logic, "**", "*.smt2")
    files = glob.glob(pattern, recursive=True)
    return files


def run_file(filepath: str):
    """Run zolver on a single file with timeout."""
    try:
        result = subprocess.run(
            [ZOLVER_BIN, "solve", filepath],
            capture_output=True,
            timeout=TIMEOUT,
            text=True,
        )
        return result.returncode, result.stderr[:200]
    except subprocess.TimeoutExpired:
        return 124, ""
    except Exception as e:
        return -1, str(e)


def test_logic(logic: str):
    """Test a sample of files for one logic."""
    files = find_files(logic)
    total = len(files)
    if total == 0:
        return logic, 0, 0, 0, []

    # Sample 50 or all if fewer
    sample = files if total <= SAMPLE_SIZE else random.sample(files, SAMPLE_SIZE)

    timeouts = 0
    crashes = 0
    ok = 0
    crash_details = []

    for f in sample:
        code, err = run_file(f)
        if code == 0:
            ok += 1
        elif code == 124:
            timeouts += 1
        else:
            crashes += 1
            crash_details.append((f, code, err))

    return logic, total, len(sample), ok, timeouts, crashes, crash_details


def main():
    logics = sorted(d for d in os.listdir(BENCHMARK_DIR)
                    if os.path.isdir(os.path.join(BENCHMARK_DIR, d)))

    print(f"Sample testing {len(logics)} logics, {SAMPLE_SIZE} files each, timeout={TIMEOUT}s, workers={MAX_WORKERS}")
    print("=" * 70)

    all_crash_details = []

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(test_logic, logic): logic for logic in logics}
        for future in as_completed(futures):
            logic, total, sample_size, ok, timeouts, crashes, details = future.result()
            status = "OK" if crashes == 0 else f"CRASH:{crashes}"
            print(f"{logic:20s} total={total:6d} sample={sample_size:3d} ok={ok:3d} timeout={timeouts:3d} crash={crashes:3d} [{status}]")
            all_crash_details.extend((logic, *d) for d in details)

    print("=" * 70)
    if all_crash_details:
        print(f"FOUND {len(all_crash_details)} CRASHES:")
        for logic, path, code, err in all_crash_details:
            print(f"  [{logic}] exit={code} {path}")
            if err:
                print(f"    stderr: {err[:200]}")
    else:
        print("NO CRASHES FOUND. All sampled files exited cleanly (or timed out).")


if __name__ == "__main__":
    main()
