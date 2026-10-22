#!/usr/bin/env python3
"""Positively validate the ten recovered array models against original input."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    cases = sorted(path for directory in ("alia", "alra", "auflra")
                   for path in (Path("tests/regression") / directory).glob("audit_*.smt2"))
    records = []
    for path in cases:
        run = subprocess.run([str(args.solver), "model-check", str(path)],
                             text=True, capture_output=True, timeout=30)
        records.append(dict(input=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                            rc=run.returncode, stdout=run.stdout, stderr=run.stderr,
                            positive=run.returncode == 0 and run.stdout.splitlines()[:1] == ["sat"]))
    metrics = dict(inputs=len(cases), positive=sum(r["positive"] for r in records))
    metrics["failures"] = metrics["inputs"] - metrics["positive"]
    report = dict(metrics=metrics, records=records, solver=str(args.solver),
                  solver_sha256=hashlib.sha256(args.solver.read_bytes()).hexdigest())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
    print(json.dumps(metrics))
    return int(metrics["inputs"] != 10 or metrics["failures"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
