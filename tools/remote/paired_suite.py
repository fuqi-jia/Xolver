#!/usr/bin/env python3
"""Alternating paired processes on a fixed, pre-change regression sample."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import statistics
import subprocess
import time


def invoke(binary, path, timeout):
    start = time.monotonic()
    try:
        proc = subprocess.run([binary, "solve", str(path)], capture_output=True,
                              text=True, timeout=timeout)
        answers = [s.strip() for s in proc.stdout.splitlines()
                   if s.strip() in {"sat", "unsat", "unknown"}]
        result = ",".join(answers) if proc.returncode == 0 and answers else "error"
        return dict(result=result, rc=proc.returncode, seconds=time.monotonic() - start,
                    stdout=proc.stdout, stderr=proc.stderr)
    except subprocess.TimeoutExpired:
        return dict(result="timeout", seconds=time.monotonic() - start)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("baseline", "candidate", "corpus", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=20)
    args = parser.parse_args()
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    binaries = {name: getattr(args, name) for name in ("baseline", "candidate")}
    cases = [Path(line) for line in Path(args.corpus).read_text().splitlines() if line.strip()]
    records = []
    # One unmeasured process per version loads code pages; every measured run
    # still uses a fresh process, including parse/startup time.
    for binary in binaries.values():
        invoke(binary, cases[0], args.timeout)
    for i, path in enumerate(cases):
        observations = []
        for repetition in range(args.repetitions):
            order = list(binaries)
            if (i + repetition) % 2:
                order.reverse()
            observations.append({name: invoke(binaries[name], path, args.timeout) for name in order})
        records.append(dict(path=str(path), sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                            observations=observations))
        (out / "progress.json").write_text(json.dumps({"completed": len(records), "total": len(cases)}))
    logs = []
    metrics = dict(inputs=len(cases), repetitions=args.repetitions,
                   disagreements=0, errors=0, baseline_timeouts=0, candidate_timeouts=0,
                   baseline_unknowns=0, candidate_unknowns=0, comparable=0)
    for row in records:
        runs = row["observations"]
        for pair in runs:
            for name in binaries:
                result = pair[name]["result"]
                if result == "timeout": metrics[name + "_timeouts"] += 1
                if "unknown" in result.split(","): metrics[name + "_unknowns"] += 1
                if result == "error": metrics["errors"] += 1
            a, b = (pair[name]["result"] for name in binaries)
            if set(a.split(",")) <= {"sat", "unsat"} and set(b.split(",")) <= {"sat", "unsat"} and a != b:
                metrics["disagreements"] += 1
        answers = {pair[name]["result"] for pair in runs for name in binaries}
        if len(answers) == 1 and all(set(answer.split(",")) <= {"sat", "unsat"} for answer in answers):
            medians = {name: statistics.median(pair[name]["seconds"] for pair in runs) for name in binaries}
            row["median_seconds"] = medians
            row["speedup"] = medians["baseline"] / medians["candidate"]
            logs.append(math.log(row["speedup"]))
    metrics["comparable"] = len(logs)
    if logs:
        metrics["geomean_speedup"] = math.exp(statistics.mean(logs))
        rng = random.Random(20261020)
        bootstrap = sorted(math.exp(statistics.mean(rng.choices(logs, k=len(logs)))) for _ in range(5000))
        metrics["case_bootstrap_95_low"] = bootstrap[125]
        metrics["case_bootstrap_95_high"] = bootstrap[4874]
    report = dict(metrics=metrics, records=records,
                  allowed_cpus=sorted(os.sched_getaffinity(0)),
                  binaries={name: dict(path=path, sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())
                            for name, path in binaries.items()})
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
    print(json.dumps(metrics))
    return int(metrics["errors"] or metrics["disagreements"])


if __name__ == "__main__":
    raise SystemExit(main())
