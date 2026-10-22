#!/usr/bin/env python3
"""Reproducible quantified PA differential tests; keep every generated input."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import time


def numeral(value):
    return str(value) if value >= 0 else f"(- {-value})"


def problem(rng, index):
    def term():
        terms = [f"(* {numeral(rng.randint(-4, 4))} {v})" for v in ("x", "y")]
        terms.append(numeral(rng.randint(-8, 8)))
        expression = "(+ " + " ".join(terms) + ")"
        if index % 4 == 0:
            expression = f"({rng.choice(['div', 'mod'])} {expression} {numeral(rng.choice([-3, -2, 2, 3]))})"
        return expression
    atoms = [f"({rng.choice(['<=', '<', '=', 'distinct'])} {term()} {numeral(rng.randint(-5, 5))})"
             for _ in range(3)]
    body = f"({rng.choice(['and', 'or', 'xor'])} {atoms[0]} (or {atoms[1]} {atoms[2]}))"
    for var in ("y", "x"):
        quantifier = rng.choice(["forall", "exists"])
        if index % 3 == 0:
            domain = f"(and (<= (- 4) {var}) (<= {var} 4))"
            body = f"({'and' if quantifier == 'exists' else '=>'} {domain} {body})"
        body = f"({quantifier} (({var} Int)) {body})"
    return f"(set-logic LIA)\n(assert {body})\n(check-sat)\n"


def invoke(command, timeout):
    start = time.monotonic()
    try:
        run = subprocess.run(command, capture_output=True, text=True, timeout=timeout)
        lines = run.stdout.splitlines()
        verdicts = [line.strip() for line in lines if line.strip() in {"sat", "unsat", "unknown"}]
        verdict = verdicts[0] if run.returncode == 0 and len(verdicts) == 1 else "error"
        return {"result": verdict, "rc": run.returncode, "seconds": time.monotonic() - start,
                "stdout": run.stdout, "stderr": run.stderr}
    except subprocess.TimeoutExpired:
        return {"result": "timeout", "seconds": time.monotonic() - start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "z3", "cvc5", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--seed", type=int, default=20261020)
    parser.add_argument("--n", type=int, default=300)
    parser.add_argument("--timeout", type=float, default=10)
    args = parser.parse_args()
    root = Path(args.output)
    root.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    counts = dict(generated=args.n, checked=0, unsound=0, errors=0,
                  unknown=0, timeouts=0, oracle_skips=0, oracle_disagreements=0)
    records = []
    for i in range(args.n):
        path = root / f"case-{i:04}.smt2"
        path.write_text(problem(rng, i))
        observations = {
            "z3": invoke([args.z3, "-smt2", str(path)], args.timeout),
            "cvc5": invoke([args.cvc5, "--lang=smt2", str(path)], args.timeout),
            "xolver": invoke([args.solver, "solve", str(path)], args.timeout),
        }
        z3, cvc5, candidate = (observations[k]["result"] for k in ("z3", "cvc5", "xolver"))
        if z3 in {"sat", "unsat"} and cvc5 in {"sat", "unsat"} and z3 != cvc5:
            counts["oracle_disagreements"] += 1
        elif z3 == cvc5 and z3 in {"sat", "unsat"}:
            counts["checked"] += 1
            if candidate in {"sat", "unsat"} and candidate != z3: counts["unsound"] += 1
        else: counts["oracle_skips"] += 1
        if candidate == "error": counts["errors"] += 1
        if candidate == "unknown": counts["unknown"] += 1
        if candidate == "timeout": counts["timeouts"] += 1
        records.append({"input": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "observations": observations})
        (root / "progress.json").write_text(json.dumps({**counts, "completed": i + 1}) + "\n")
    report = {"seed": args.seed, "counts": counts, "records": records,
              "binaries": {name: {"path": getattr(args, name),
                                   "sha256": hashlib.sha256(Path(getattr(args, name)).read_bytes()).hexdigest()}
                           for name in ("solver", "z3", "cvc5")}}
    (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(not counts["checked"] or counts["unsound"] or counts["errors"]
               or counts["oracle_disagreements"])


if __name__ == "__main__":
    raise SystemExit(main())
