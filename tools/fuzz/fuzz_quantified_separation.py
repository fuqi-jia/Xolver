#!/usr/bin/env python3
"""Original quantified SL inputs, exact heap pins, and a separate SMT oracle.

Oracle Unknown is recorded as incomplete validation, never converted to SAT.
Run on the experiment server with a frozen candidate and cvc5 binary.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import shutil
from fuzz_presburger import invoke
from fuzz_native_separation import pins


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def corpus(seed):
    rng = random.Random(seed)
    result = [
        ("forall-pto", "(forall ((x Int)) (pto x 0))", "unsat"),
        ("forall-exists", "(forall ((x Int)) (exists ((y Int)) (and (> y x) sep.emp)))", "sat"),
        ("wand-dependent-witness", "(and sep.emp (forall ((x Int)) (wand (pto x 0) (exists ((y Int)) (pto x y)))))", "sat"),
        ("wand-antecedent", "(and sep.emp (wand (exists ((x Int)) (pto x 0)) (pto 1 0)))", "unsat"),
        ("wand-unbounded", "(forall ((x Int)) (wand true sep.emp))", "unsat"),
        ("negative-exists", "(not (exists ((x Int)) (pto x 0)))", "sat"),
        ("boolean-domain", "(forall ((b Bool)) (ite b sep.emp sep.emp))", "sat"),
    ]
    for i in range(8):
        a, b = rng.sample(range(1, 40), 2)
        result.extend([
            (f"exist-{i}", f"(exists ((x Int)) (and (= x {a}) (pto x {b})))", "sat"),
            (f"overlap-{i}", f"(exists ((x Int)) (sep (pto x {a}) (pto x {b})))", "unsat"),
            (f"forall-guard-{i}", f"(and (pto {a} {b}) (forall ((x Int)) (=> (= x {a}) (pto x {b}))))", "sat"),
            (f"forall-conflict-{i}", f"(and (pto {a} {b}) (forall ((x Int)) (=> (= x {a}) (not (pto x {b})))))", "unsat"),
            (f"empty-negative-{i}", f"(and sep.emp (not (forall ((x Int)) (not (pto x {a})))))", "unsat"),
            (f"quantified-star-{i}", f"(sep (exists ((x Int)) (and (= x {a}) (pto x {b}))) (exists ((y Int)) (and (= y {b}) (pto y {a}))))", "sat"),
        ])
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--solver", type=Path, required=True)
    p.add_argument("--cvc5", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--timeout", type=float, default=4)
    p.add_argument("--seed", type=int, default=22031)
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    driver = args.output / "driver"
    driver.mkdir()
    for name in ("fuzz_quantified_separation.py", "fuzz_native_separation.py", "fuzz_presburger.py"):
        shutil.copyfile(Path(__file__).with_name(name), driver / name)
    counts = dict(cases=0, mismatches=0, unknown=0, errors=0, timeouts=0,
                  models=0, rejected_models=0, malformed_models=0, oracle_incomplete=0,
                  oracle_disagreements=0, model_incomplete=0)
    records = []
    for i, (name, formula, expected) in enumerate(corpus(args.seed)):
        prefix = "(set-logic ALL)(declare-heap (Int Int))(assert " + formula + ")\n"
        query = args.output / f"case-{i:03}-{name}.smt2"
        query.write_text(prefix + "(check-sat)(get-model)\n")
        candidate = invoke([str(args.solver), "solve", str(query), "--check-model"], args.timeout)
        oracle_input = args.output / f"oracle-{i:03}.smt2"
        oracle_input.write_text(prefix + "(check-sat)\n")
        oracle = invoke([str(args.cvc5), "--lang=smt2", str(oracle_input)], args.timeout)
        counts["cases"] += 1
        verdict = candidate["result"]
        counts["mismatches"] += verdict in ("sat", "unsat") and verdict != expected
        for value, key in (("unknown", "unknown"), ("error", "errors"), ("timeout", "timeouts")):
            counts[key] += verdict == value
        counts["oracle_disagreements"] += oracle["result"] in ("sat", "unsat") and oracle["result"] != expected
        counts["oracle_incomplete"] += oracle["result"] not in ("sat", "unsat")
        record = dict(name=name, expected=expected, input_sha256=digest(query), candidate=candidate, oracle=oracle)
        if verdict == "sat":
            counts["models"] += 1
            try:
                pinned = args.output / f"pinned-{i:03}.smt2"
                pinned.write_text(prefix + pins(candidate["stdout"]) + "(check-sat)\n")
            except (ValueError, KeyError) as error:
                counts["malformed_models"] += 1
                record["model_error"] = str(error)
            else:
                checked = invoke([str(args.cvc5), "--lang=smt2", str(pinned)], args.timeout)
                counts["rejected_models"] += checked["result"] == "unsat"
                counts["model_incomplete"] += checked["result"] not in ("sat", "unsat")
                record.update(model=checked, pinned_sha256=digest(pinned))
            counts["rejected_models"] += "MODEL_MISMATCH" in candidate.get("stderr", "")
        records.append(record)
        (args.output / "progress.json").write_text(json.dumps(counts) + "\n")
    report = dict(metrics=counts, records=records, seed=args.seed,
                  solver_sha256=digest(args.solver), oracle_sha256=digest(args.cvc5))
    (args.output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(counts))
    return int(any(n for key, n in counts.items() if key not in ("cases", "models")))


if __name__ == "__main__":
    raise SystemExit(main())
