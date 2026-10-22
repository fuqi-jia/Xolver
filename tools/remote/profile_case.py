#!/usr/bin/env python3
"""Capture a bounded solver profile against a frozen binary on ExperimentOS."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--case", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--timeout", type=float, default=45)
    parser.add_argument("--verbose", action="store_true",
                        help="retain solver diagnostics, including unknown reasons")
    args = parser.parse_args()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    controls = {"XOLVER_SELFPROF": "1", "SOLVE_PHASE_PROF": "1",
                "XOLVER_DUMP_FINAL_ASSERTS": "1",
                "ARITH_STAGE_PROF": str(output / "stages.log")}
    start = time.monotonic()
    timed_out = False
    command = [args.binary, "solve", args.case]
    if args.verbose:
        command.append("--verbose")
    with (output / "stdout.log").open("wb") as stdout, \
            (output / "stderr.log").open("wb") as stderr:
        try:
            result = subprocess.run(command,
                                    stdout=stdout, stderr=stderr,
                                    env={**os.environ, **controls}, timeout=args.timeout)
            rc = result.returncode
        except subprocess.TimeoutExpired:
            rc, timed_out = None, True
    samples = (output / "stderr.log").read_text(errors="replace").split("==SELFPROF-SAMPLE==")[1:]
    frames = []
    for sample in samples:
        frames.append(re.findall(re.escape(args.binary) + r"\(\+(0x[0-9a-f]+)\)", sample))
    addresses = sorted({address for frame in frames for address in frame})
    symbols = {}
    if addresses:
        decoded = subprocess.run(["addr2line", "-Cf", "-e", args.binary, *addresses],
                                 check=True, capture_output=True, text=True).stdout.splitlines()
        symbols = {address: decoded[2 * i] for i, address in enumerate(addresses)}
    inclusive = Counter(symbol for frame in frames for symbol in {symbols[a] for a in frame})
    report = {
        "binary": {"path": args.binary, "sha256": digest(args.binary)},
        "case": {"path": args.case, "sha256": digest(args.case)},
        "controls": controls, "timeout": timed_out, "rc": rc,
        "command": command,
        "seconds": time.monotonic() - start, "samples": len(samples),
        "inclusive_frames": inclusive.most_common(), "symbols": symbols,
        "allowed_cpus": sorted(os.sched_getaffinity(0)),
    }
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    metrics = {"samples": len(samples), "profile_completed": 1,
               "solver_timeout": int(timed_out)}
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(metrics) + "\n")
    print(json.dumps(metrics))


if __name__ == "__main__":
    main()
