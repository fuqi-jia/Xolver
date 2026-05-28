#!/usr/bin/env python3
"""
LIA mismatch replay harness.

Usage:
    python tools/lia_mismatch_replay.py \
        --discrepancies panda-results/2026-05-21/lia/discrepancies.txt \
        --category convert \
        --zolver ./build/bin/zolver \
        --z3 z3 \
        --limit 20 \
        --dump-dir /tmp/lia_dump \
        --out report.json

This script:
1. Reads discrepancies.txt and extracts mismatch cases for a given category.
2. For each case, runs Z3, Zolver (normal), and Zolver (safe-mode).
3. Compares results and reports which mismatches disappear in safe-mode.
4. If --dump-dir is set, sets ZOLVER_LIA_DUMP_DIR so Zolver dumps state.
"""

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Optional


@dataclass
class CaseResult:
    path: str
    z3_result: str
    z3_time: float
    nl_normal_result: str
    nl_normal_time: float
    nl_safe_result: str
    nl_safe_time: float
    mismatch_fixed: bool
    note: str


def parse_discrepancies(path: str, category: Optional[str] = None):
    """Parse discrepancies.txt and yield (filepath, nl_result, compare_result) tuples."""
    with open(path, "r") as f:
        content = f.read()

    # Split by double newline (each case is a block)
    blocks = re.split(r"\n\n+", content)
    for block in blocks:
        lines = block.strip().splitlines()
        if len(lines) < 3:
            continue
        filepath = None
        nl_result = None
        compare_result = None
        for line in lines:
            m = re.match(r"^(\S+\.smt2)\s*$", line.strip())
            if m:
                filepath = m.group(1)
            m = re.match(r"^\s*zolver:\s+(\w+)\s*\(", line)
            if m:
                nl_result = m.group(1).lower()
            m = re.match(r"^\s*compare:\s+(\w+)\s*\(", line)
            if m:
                compare_result = m.group(1).lower()

        if not filepath or not nl_result or not compare_result:
            continue
        if category and f"/QF_LIA/{category}/" not in filepath:
            continue
        yield filepath, nl_result, compare_result


def run_solver(cmd: List[str], timeout: float = 30.0) -> tuple:
    """Run a solver command, return (result, time_ms)."""
    try:
        t0 = os.times()
        proc = subprocess.run(
            cmd,
            # 3.6-safe (capture_output= / text= are 3.7+).
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
        )
        t1 = os.times()
        elapsed = (t1.elapsed - t0.elapsed) * 1000.0
        stdout = proc.stdout.strip().lower()
        if "unsat" in stdout:
            return "unsat", elapsed
        if "sat" in stdout and "unknown" not in stdout:
            return "sat", elapsed
        if "timeout" in stdout or proc.returncode == 124:
            return "timeout", elapsed
        return "error", elapsed
    except subprocess.TimeoutExpired:
        return "timeout", timeout * 1000.0
    except Exception as e:
        return f"error:{e}", 0.0


def main():
    parser = argparse.ArgumentParser(description="LIA mismatch replay harness")
    parser.add_argument("--discrepancies", required=True, help="Path to discrepancies.txt")
    parser.add_argument("--category", default=None, help="Filter by category (e.g., convert)")
    parser.add_argument("--zolver", default="./build/bin/zolver", help="Path to zolver binary")
    parser.add_argument("--z3", default="z3", help="Path to z3 binary")
    parser.add_argument("--limit", type=int, default=20, help="Max cases to run")
    parser.add_argument("--timeout", type=float, default=30.0, help="Per-case timeout (seconds)")
    parser.add_argument("--dump-dir", default=None, help="Directory for LIA state dumps")
    parser.add_argument("--out", default="lia_replay_report.json", help="Output JSON report")
    parser.add_argument("--zolver-extra", default=None, help="Extra flags passed to zolver (e.g. '--lia-safe-mode')")
    parser.add_argument("--mode-name", default="safe", help="Name for the extra mode in reports")
    args = parser.parse_args()

    cases = list(parse_discrepancies(args.discrepancies, args.category))
    print(f"Found {len(cases)} mismatch cases" + (f" in category '{args.category}'" if args.category else ""))

    if args.limit > 0:
        cases = cases[:args.limit]

    results: List[CaseResult] = []
    fixed_count = 0
    still_mismatch_count = 0

    env_normal = os.environ.copy()
    env_safe = os.environ.copy()
    env_safe["ZOLVER_LIA_DUMP_DIR"] = args.dump_dir or ""

    for i, (filepath, nl_orig, cmp_orig) in enumerate(cases, 1):
        print(f"\n[{i}/{len(cases)}] {filepath}")
        print(f"  Original mismatch: NL={nl_orig}  Z3={cmp_orig}")

        # Run Z3 on original file
        z3_cmd = [args.z3, "-T:%d" % int(args.timeout), filepath]
        z3_res, z3_time = run_solver(z3_cmd, args.timeout)
        print(f"  Z3:        {z3_res}  ({z3_time:.1f}ms)")

        # Run Zolver normal mode
        nl_cmd = [args.zolver, filepath]
        nl_res, nl_time = run_solver(nl_cmd, args.timeout)
        print(f"  NL normal: {nl_res}  ({nl_time:.1f}ms)")

        # Run Zolver extra mode (safe-mode by default, or user-specified)
        extra_flags = shlex.split(args.zolver_extra) if args.zolver_extra else ["--lia-safe-mode"]
        nl_extra_cmd = [args.zolver, filepath] + extra_flags
        nl_extra_res, nl_extra_time = run_solver(nl_extra_cmd, args.timeout)
        print(f"  NL {args.mode_name}:   {nl_extra_res}  ({nl_extra_time:.1f}ms)")

        # Determine if mismatch is fixed
        mismatch_fixed = False
        note = ""
        if nl_extra_res == z3_res:
            mismatch_fixed = True
            note = f"FIXED: {args.mode_name} matches Z3"
            fixed_count += 1
        elif nl_extra_res != nl_res:
            note = f"CHANGED: {args.mode_name} changed result from {nl_res} to {nl_extra_res}"
            if nl_extra_res == z3_res:
                mismatch_fixed = True
                fixed_count += 1
        else:
            note = f"STILL_MISMATCH: {args.mode_name} still {nl_extra_res}, Z3 says {z3_res}"
            still_mismatch_count += 1

        print(f"  -> {note}")

        results.append(CaseResult(
            path=filepath,
            z3_result=z3_res,
            z3_time=z3_time,
            nl_normal_result=nl_res,
            nl_normal_time=nl_time,
            nl_safe_result=nl_extra_res,
            nl_safe_time=nl_extra_time,
            mismatch_fixed=mismatch_fixed,
            note=note,
        ))

    # Summary
    print(f"\n{'='*60}")
    print(f"SUMMARY")
    print(f"  Total cases:     {len(results)}")
    print(f"  Fixed:           {fixed_count}")
    print(f"  Still mismatch:  {still_mismatch_count}")
    print(f"  Report written:  {args.out}")

    # Write JSON report
    with open(args.out, "w") as f:
        json.dump({
            "args": vars(args),
            "summary": {
                "total": len(results),
                "fixed": fixed_count,
                "still_mismatch": still_mismatch_count,
            },
            "results": [asdict(r) for r in results],
        }, f, indent=2)


if __name__ == "__main__":
    main()
