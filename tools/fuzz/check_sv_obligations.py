#!/usr/bin/env python3
"""Independently decide exported SV certificate conditions and reachable paths."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generator", type=Path, required=True)
    parser.add_argument("--z3", type=Path, required=True)
    parser.add_argument("--cvc5", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, args.output / Path(__file__).name)
    subprocess.run([str(args.generator.resolve()), str(args.output / "cases")],
                   check=True, timeout=300)
    cases = json.loads((args.output / "cases/cases.json").read_text())
    if not cases or not any(c["heap"] for c in cases):
        raise RuntimeError("missing verification evidence")
    engines = {"z3": [str(args.z3.resolve()), "-smt2"],
               "cvc5": [str(args.cvc5.resolve()), "--lang=smt2"]}
    records = []
    checks = failures = 0
    for case in cases:
        path = args.output / "cases" / case["input"]
        record = dict(case, sha256=digest(path), engines={})
        for name, command in engines.items():
            if case["heap"] and name == "z3":
                continue  # Z3 does not implement separation-logic heap operators.
            checks += 1
            try:
                run = subprocess.run(command + [str(path)], text=True, capture_output=True,
                                     timeout=20)
                verdicts = [s.strip() for s in run.stdout.splitlines()
                            if s.strip() in ("sat", "unsat", "unknown")]
                valid = run.returncode == 0 and verdicts == [case["expected"]]
                record["engines"][name] = dict(returncode=run.returncode, stdout=run.stdout,
                                                stderr=run.stderr, accepted=valid)
            except subprocess.TimeoutExpired:
                valid = False
                record["engines"][name] = dict(timeout=True, accepted=False)
            failures += not valid
        records.append(record)
    report = dict(cases=len(cases), checks=checks, failures=failures, records=records,
                  generator_sha256=digest(args.generator),
                  oracles={name: dict(sha256=digest(command[0]),
                                     version=subprocess.run([command[0], "--version"],
                                         text=True, capture_output=True, check=True).stdout)
                           for name, command in engines.items()})
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("cases", "checks", "failures")}))
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
