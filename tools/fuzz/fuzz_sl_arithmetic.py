#!/usr/bin/env python3
"""PA/SL CLI differential, with exact exported stacks and heaps pinned in cvc5."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import shutil
import sys


def numeral(value):
    return str(value) if value >= 0 else f"(- {-value})"


def problem(rng, index, pin_nil=False):
    a, b = rng.randint(-3, 3), rng.randint(-3, 3)
    divisor = numeral(rng.choice([-3, -2, 2, 3]))
    address = f"(+ x {numeral(a)})"
    other = f"(+ y {numeral(b)})"
    value = f"(mod (+ x y) {divisor})"
    left, right = f"(pto {address} {value})", f"(pto {other} {value})"
    patterns = [
        f"(sep {left} {right})",
        f"(and {left} {right})",
        f"(and sep.emp (wand {left} {right}))",
        f"(and sep.emp (not (wand {left} {right})))",
        f"(sep (< x y) {left})",
        f"(ite p {left} (and (>= x y) {right}))",
        f"(and (= p (< x y)) (ite p {left} {right}))",
        f"(and {left} (not (sep {left} {right})))",
        f"(and {left} (wand (> x y) false))",
        f"(pto (ite p {address} {other}) (abs (- x y)))",
        f"(pto (div (+ x y) {divisor}) {value})",
        f"(and (< x y) (>= x y) {left})",
        f"(or (and (< x y) {left}) (and (>= x y) {right}))",
        f"(and (= y (+ x 1)) (sep (pto (+ x 1) 7) (pto y 7)))",
        f"(and {left} (wand sep.emp {left}))",
        f"(let ((x (+ x 1)) (y x)) (and (> x y) (pto x y)))",
    ]
    prefix = ("(set-logic ALL)\n(declare-heap (Int Int))\n"
              "(declare-const x Int)(declare-const y Int)(declare-const p Bool)\n")
    if pin_nil or index % 3 != 0:
        prefix += "(assert (= (as sep.nil Int) 0))\n"
    if (index // len(patterns)) % 2 == 0:
        prefix += (f"(assert (= x {numeral(rng.randint(-4, 4))}))\n"
                   f"(assert (= y {numeral(rng.randint(-4, 4))}))\n"
                   f"(assert (= p {rng.choice(['true', 'false'])}))\n")
    return prefix + f"(assert {patterns[index % len(patterns)]})\n"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("solver", "cvc5", "helpers", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--n", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--pin-nil", action="store_true",
                        help="Run a separate restricted corpus with nil fixed to zero in every query")
    args = parser.parse_args()
    if args.n <= 0:
        parser.error("--n must be positive")
    sys.path.insert(0, str(args.helpers.resolve()))
    from fuzz_presburger import invoke
    from fuzz_native_separation import pins

    args.output.mkdir(parents=True, exist_ok=False)
    sources = [Path(__file__).resolve(), args.helpers / "fuzz_presburger.py",
               args.helpers / "fuzz_native_separation.py",
               args.helpers.parent / "proof/isabelle_pa.py",
               args.helpers.parent / "proof/pa_trace.py"]
    drivers = {}
    for source in sources:
        target = args.output / "driver" / ("proof" if source.parent.name == "proof" else "fuzz") / source.name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        drivers[str(target.relative_to(args.output))] = sha(target)
    rng = random.Random(args.seed)
    counts = dict(cases=0, oracle_checked=0, disagreements=0, unknown=0, errors=0,
                  timeouts=0, oracle_inconclusive=0, models=0, malformed_models=0,
                  model_rejections=0, models_checked=0, model_inconclusive=0)
    records = []
    for index in range(args.n):
        prefix = problem(rng, index, args.pin_nil)
        original = args.output / f"case-{index:04}.smt2"
        original.write_text(prefix + "(check-sat)\n")
        query = args.output / f"model-{index:04}.smt2"
        query.write_text(prefix + "(check-sat)(get-model)\n")
        candidate = invoke([str(args.solver), "solve", str(query), "--check-model", "--verbose"], args.timeout)
        oracle = invoke([str(args.cvc5), "--lang=smt2", str(original)], args.timeout)
        counts["cases"] += 1
        verdict = candidate["result"]
        for outcome, key in (("unknown", "unknown"), ("error", "errors"), ("timeout", "timeouts")):
            counts[key] += verdict == outcome
        if oracle["result"] in ("sat", "unsat"):
            counts["oracle_checked"] += 1
            counts["disagreements"] += verdict in ("sat", "unsat") and verdict != oracle["result"]
        else:
            counts["oracle_inconclusive"] += 1
        row = dict(index=index, input=original.name, input_sha256=sha(original),
                   query=query.name, query_sha256=sha(query), candidate=candidate, oracle=oracle)
        if verdict == "sat":
            counts["models"] += 1
            try:
                pinned = args.output / f"pinned-{index:04}.smt2"
                pinned.write_text(prefix + pins(candidate["stdout"]) + "(check-sat)\n")
            except ValueError as error:
                counts["malformed_models"] += 1
                row["model_error"] = str(error)
            else:
                checked = invoke([str(args.cvc5), "--lang=smt2", str(pinned)], args.timeout)
                counts["model_rejections"] += checked["result"] == "unsat"
                counts["models_checked"] += checked["result"] == "sat"
                counts["model_inconclusive"] += checked["result"] not in ("sat", "unsat")
                row.update(pinned=pinned.name, pinned_sha256=sha(pinned), model=checked)
            if "MODEL_MISMATCH" in candidate.get("stderr", ""):
                counts["model_rejections"] += 1
        records.append(row)
        (args.output / "progress.json").write_text(json.dumps(counts) + "\n")
    report = dict(seed=args.seed, pin_nil=args.pin_nil, metrics=counts, records=records, drivers=drivers,
                  solver_sha256=sha(args.solver), cvc5_sha256=sha(args.cvc5))
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (args.output / "metrics.json").write_text(json.dumps(counts) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    excluded = {"cases", "oracle_checked", "models", "models_checked"}
    return int(not counts["models"] or any(v for k, v in counts.items() if k not in excluded))


if __name__ == "__main__":
    raise SystemExit(main())
