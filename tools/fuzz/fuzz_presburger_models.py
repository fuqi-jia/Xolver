#!/usr/bin/env python3
"""Check quantified PA verdicts and every exported free-variable assignment."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shutil

import fuzz_presburger
from fuzz_presburger import invoke, numeral


def problem(rng, index):
    a, b = rng.randint(1, 5), rng.randint(1, 5)
    k = rng.randint(-20, 20)
    # Exercise arbitrary precision as well as negative witness reconstruction.
    lower = rng.randint(-50, 10) - (10**30 if index % 7 == 0 else 0)
    upper = lower + rng.randint(1, 15)
    x = f"(* {a} x)"
    quantified = [
        f"(forall ((y Int)) (=> (>= y x) (>= (* {a} y) {numeral(k)})))",
        f"(exists ((y Int)) (= (+ (* {a} y) x (* {b} z)) {numeral(k)}))",
        f"(forall ((y Int)) (exists ((w Int)) (and (<= (* {a} w) (+ y x)) "
        f"(< (+ y x) (+ (* {a} w) {a})))))",
        "(exists ((y Int)) (and (exists ((y Int)) (= y 0)) (= y x)))",
    ][index % 4]
    return (
        "(set-logic LIA)(declare-const x Int)(declare-const z Int)(declare-const p Bool)\n"
        f"(assert (and (<= {numeral(lower)} x) (<= x {numeral(upper)})))\n"
        f"(assert (= z (+ {x} {numeral(k)})))\n"
        f"(assert (= (mod z {b}) {rng.randrange(b)}))\n"
        f"(assert {'p' if index % 2 else '(not p)'})\n"
        f"(assert {quantified})\n"
    )


def piecewise_problem(rng, index):
    lower = rng.randint(-30, 10) - (10**30 if index % 7 == 0 else 0)
    upper = lower + rng.randint(1, 10)
    offset = numeral(rng.randint(-7, 7))
    divisor = numeral(rng.choice([-3, -2, 2, 3]))
    quantifier = (
        "(forall ((b Bool)) (exists ((y Int)) (= y (ite b (abs z) (div x (- 3))))))"
        if index % 3 else
        "(forall ((b Bool)) (= (ite b x z) x))"
    )
    return (
        "(set-logic LIA)(declare-const x Int)(declare-const z Int)(declare-const p Bool)\n"
        f"(assert (and (<= {numeral(lower)} x) (<= x {numeral(upper)})))\n"
        f"(assert (= z (ite p (+ (abs x) {offset}) (- {offset} (abs x)))))\n"
        f"(assert {'p' if index % 2 else '(not p)'})\n"
        f"(assert {quantifier})\n"
        f"(assert (forall ((b Bool)) (= (mod (ite b x z) {divisor})"
        f" (ite b (mod x {divisor}) (mod z {divisor})))))\n"
    )


def model_bindings(output):
    matches = re.findall(
        r"\(define-fun\s+(x|z|p)\s+\(\)\s+(Int|Bool)\s+"
        r"(true|false|-?\d+|\(-\s+\d+\s*\))\s*\)", output)
    if len(matches) != 3 or {m[0] for m in matches} != {"x", "z", "p"}:
        return None
    for name, sort, value in matches:
        if (name == "p") != (sort == "Bool") or (sort == "Bool") != (value in {"true", "false"}):
            return None
    return "\n".join(f"(assert (= {name} {value}))" for name, sort, value in matches)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "z3", "cvc5", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--n", type=int, default=120)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--suite", choices=["affine", "piecewise"], default="affine")
    args = parser.parse_args()
    root = Path(args.output)
    root.mkdir(parents=True, exist_ok=False)
    drivers = {}
    for name, path in (("fuzz_presburger_models.py", __file__),
                       ("fuzz_presburger.py", fuzz_presburger.__file__)):
        shutil.copyfile(path, root / name)
        drivers[name] = hashlib.sha256((root / name).read_bytes()).hexdigest()
    counts = dict(generated=args.n, checked=0, models_checked=0, model_skips=0,
                  bad_models=0, unsound=0, errors=0, unknown=0, timeouts=0,
                  oracle_skips=0, oracle_disagreements=0)
    records = []
    rng = random.Random(args.seed)
    for i in range(args.n):
        source = (problem if args.suite == "affine" else piecewise_problem)(rng, i)
        path = root / f"case-{i:04}.smt2"
        path.write_text(source + "(check-sat)\n")
        oracle_commands = {"z3": [args.z3, "-smt2"],
                           "cvc5": [args.cvc5, "--lang=smt2"]}
        observations = {name: invoke(command + [str(path)], args.timeout)
                        for name, command in oracle_commands.items()}
        model_path = root / f"model-{i:04}.smt2"
        model_path.write_text(source + "(check-sat)(get-model)\n")
        candidate = invoke([args.solver, "solve", str(model_path)], args.timeout)
        observations["xolver"] = candidate
        a, b = observations["z3"]["result"], observations["cvc5"]["result"]
        result = candidate["result"]
        if a in {"sat", "unsat"} and b in {"sat", "unsat"} and a != b:
            counts["oracle_disagreements"] += 1
        elif a == b and a in {"sat", "unsat"}:
            counts["checked"] += 1
            counts["unsound"] += result in {"sat", "unsat"} and result != a
        else:
            counts["oracle_skips"] += 1
        for verdict, key in (("error", "errors"), ("unknown", "unknown"), ("timeout", "timeouts")):
            counts[key] += result == verdict
        if result == "sat":
            bindings = model_bindings(candidate["stdout"])
            if bindings is None:
                # Explicit model unavailability under a budget is distinct from
                # malformed, incomplete or wrong model output.
                if "model is unavailable" in candidate["stdout"]:
                    counts["model_skips"] += 1
                else:
                    counts["bad_models"] += 1
            else:
                pinned = root / f"pinned-{i:04}.smt2"
                pinned.write_text(source + bindings + "\n(check-sat)\n")
                checks = {name: invoke(command + [str(pinned)], args.timeout)
                          for name, command in oracle_commands.items()}
                observations["model_checks"] = checks
                if all(check["result"] == "sat" for check in checks.values()):
                    counts["models_checked"] += 1
                elif any(check["result"] == "unsat" for check in checks.values()):
                    counts["bad_models"] += 1
                else:
                    counts["model_skips"] += 1
        records.append({"input": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                        "observations": observations})
        (root / "progress.json").write_text(json.dumps({**counts, "completed": i + 1}) + "\n")
    report = {"seed": args.seed, "suite": args.suite, "counts": counts, "records": records,
              "drivers": drivers,
              "binaries": {key: {"path": getattr(args, key),
                                "sha256": hashlib.sha256(Path(getattr(args, key)).read_bytes()).hexdigest()}
                           for key in ("solver", "z3", "cvc5")}}
    (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(not counts["models_checked"] or counts["bad_models"] or counts["unsound"]
               or counts["errors"] or counts["oracle_disagreements"])


if __name__ == "__main__":
    raise SystemExit(main())
