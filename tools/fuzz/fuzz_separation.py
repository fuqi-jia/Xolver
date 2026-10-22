#!/usr/bin/env python3
"""Check generated Boolean/spatial formulas and pinned heaps with cvc5."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

from fuzz_presburger import invoke


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generator", type=Path, required=True)
    parser.add_argument("--cvc5", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    for filename in ("fuzz_separation.py", "fuzz_presburger.py"):
        shutil.copyfile(Path(__file__).with_name(filename), args.output / filename)
    subprocess.run([str(args.generator.resolve()), str(args.output / "cases")],
                   check=True, timeout=600)
    counts = dict(cases=0, disagreements=0, unknown=0, oracle_skips=0,
                  models=0, model_rejections=0, model_skips=0)
    observations = []
    for case in json.loads((args.output / "cases/candidate.json").read_text()):
        counts["cases"] += 1
        path = args.output / "cases" / case["input"]
        oracle = invoke([str(args.cvc5), "--lang=smt2", str(path)], 10)
        if case["result"] == "unknown":
            counts["unknown"] += 1
        if oracle["result"] not in ("sat", "unsat"):
            counts["oracle_skips"] += 1
        elif case["result"] in ("sat", "unsat"):
            counts["disagreements"] += case["result"] != oracle["result"]
        row = dict(case, sha256=sha(path), oracle=oracle)
        if "model" in case:
            counts["models"] += 1
            model_path = args.output / "cases" / case["model"]
            checked = invoke([str(args.cvc5), "--lang=smt2", str(model_path)], 10)
            counts["model_rejections"] += checked["result"] == "unsat"
            counts["model_skips"] += checked["result"] not in ("sat", "unsat")
            row.update(model_sha256=sha(model_path), model_oracle=checked)
        observations.append(row)
    report = dict(metrics=counts, records=observations,
                  generator_sha256=sha(args.generator), oracle_sha256=sha(args.cvc5),
                  oracle_version=subprocess.run([str(args.cvc5), "--version"],
                      capture_output=True, text=True, check=True).stdout)
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (args.output / "metrics.json").write_text(json.dumps(counts) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(counts["cases"] != 240 or not counts["models"] or any(counts[k] for k in
                   ("disagreements", "unknown", "oracle_skips", "model_rejections", "model_skips")))


if __name__ == "__main__":
    raise SystemExit(main())
