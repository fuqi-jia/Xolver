#!/usr/bin/env python3
"""
Freeze a comparison solver baseline for later use.

Usage:
    python tools/freeze_baseline.py \
        --input /data/bench-runs/all_logics_20260519_210000 \
        --output /data/bench-baselines/z3_4.12.2_xxx_t10.json \
        --solver-name z3 \
        --solver-version "4.12.2"
"""

import argparse
import json
import hashlib
import sys
from pathlib import Path
from datetime import datetime


def main():
    parser = argparse.ArgumentParser(description="Freeze benchmark baseline")
    parser.add_argument("--input", required=True, help="Run directory with statistics.json")
    parser.add_argument("--output", required=True, help="Output frozen baseline JSON path")
    parser.add_argument("--solver-name", required=True)
    parser.add_argument("--solver-version", required=True)
    args = parser.parse_args()

    input_dir = Path(args.input)
    stats_path = input_dir / "statistics.json"
    if not stats_path.exists():
        print(f"ERROR: {stats_path} not found")
        return 1

    with open(stats_path) as f:
        data = json.load(f)

    # Compute manifest hash if manifest.txt exists
    manifest_hash = ""
    manifest_path = input_dir / "manifest.txt"
    if manifest_path.exists():
        with open(manifest_path, "rb") as f:
            manifest_hash = "sha256:" + hashlib.sha256(f.read()).hexdigest()

    # Extract per-case results
    frozen = {
        "meta": {
            "solver": args.solver_name,
            "version": args.solver_version,
            "manifest_hash": manifest_hash,
            "created_at": datetime.now().isoformat(),
            "source_run": input_dir.name,
        },
        "results": {},
    }

    for row in data.get("results", []):
        fpath = row.get("file", "")
        if not fpath:
            continue
        frozen["results"][fpath] = {
            "result": row.get("compare_result", row.get("xolver_result", "unknown")),
            "time": row.get("compare_time", row.get("xolver_time", 0.0)),
        }

    with open(args.output, "w") as f:
        json.dump(frozen, f, indent=2)

    size = Path(args.output).stat().st_size
    print(f"[DONE] Frozen baseline: {args.output} ({size} bytes, {len(frozen['results'])} cases)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
