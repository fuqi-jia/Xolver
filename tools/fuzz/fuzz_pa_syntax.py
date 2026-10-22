#!/usr/bin/env python3
"""Compare scope/chain syntax with independently expanded formulas and two oracles."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random

from fuzz_presburger import invoke, numeral


def pair(rng, index):
    a, b, c, d = [rng.randint(-5, 5) for _ in range(4)]
    n = numeral
    declarations = ""
    if index % 4 == 0:
        declarations = f"(declare-const x Int)(assert (= x {n(a)}))"
        original = f"(let ((x {n(b)}) (y (+ x {n(c)}))) (= y (+ x {n(d)})))"
        expanded = f"(= (+ x {n(c)}) (+ {n(b)} {n(d)}))"
    elif index % 4 == 1:
        original = (f"(let ((x {n(a)}) (y {n(b)})) "
                    "(let ((x y) (y x)) " + f"(= (+ x {n(c)}) (+ y {n(d)}))))")
        expanded = f"(= (+ {n(b)} {n(c)}) (+ {n(a)} {n(d)}))"
    elif index % 4 == 2:
        declarations = "(declare-const p Bool)(declare-const q Bool)"
        values = [rng.choice(["p", "q", "true", "false", "(not p)"])
                  for _ in range(rng.randint(3, 7))]
        original = "(= " + " ".join(values) + ")"
        expanded = "(and " + " ".join(f"(= {x} {y})" for x, y in zip(values, values[1:])) + ")"
        if rng.getrandbits(1):
            original, expanded = f"(not {original})", f"(not {expanded})"
    else:
        op = rng.choice(["<", "<=", ">", ">=", "="])
        values = [n(a), "x", n(b), n(c)]
        original = f"({op} " + " ".join(values) + ")"
        expanded = "(and " + " ".join(f"({op} {x} {y})" for x, y in zip(values, values[1:])) + ")"
        quantifier = rng.choice(["forall", "exists"])
        original = f"({quantifier} ((x Int)) {original})"
        expanded = f"({quantifier} ((x Int)) {expanded})"
    return [f"(set-logic LIA){declarations}(assert {formula})(check-sat)\n"
            for formula in (original, expanded)]


def piecewise_pair(rng, index):
    """Expand finite quantification and piecewise comparisons independently."""
    n = numeral
    a, b = n(rng.randint(-5, 5)), n(rng.randint(-5, 5))
    q = rng.choice(["forall", "exists"])
    connect = "and" if q == "forall" else "or"
    family = index % 6
    if family < 2:
        other = rng.choice(["forall", "exists"])
        def body(p):
            value = f"(ite {p} {a} {b})" if p == "p" else (a if p == "true" else b)
            return f"(= x {value})"
        if family == 0:
            original = f"({q} ((p Bool)) ({other} ((x Int)) {body('p')}))"
            expanded = f"({connect} ({other} ((x Int)) {body('true')}) ({other} ((x Int)) {body('false')}))"
        else:
            original = f"({other} ((x Int)) ({q} ((p Bool)) {body('p')}))"
            expanded = f"({other} ((x Int)) ({connect} {body('true')} {body('false')}))"
    elif family < 5:
        linear = f"(+ (* {n(rng.choice([-3, -2, -1, 1, 2, 3]))} x) {a})"
        condition = f"(>= {linear} 0)"
        value = f"(abs {linear})"
        yes, no = linear, f"(- {linear})"
        expanded_condition = condition
        if family == 3:
            divisor = n(rng.choice([-3, -2, 2, 3]))
            op = rng.choice(["div", "mod"])
            value, yes, no = [f"({op} {v} {divisor})" for v in (value, yes, no)]
        elif family == 4:
            condition = f"(forall ((y Int)) (>= (+ y {linear}) y))"
            value = f"(ite {condition} {linear} (- {linear}))"
        relation = rng.choice(["<", "<=", "=", "distinct"])
        original = f"({relation} {value} {b})"
        expanded = (f"(or (and {expanded_condition} ({relation} {yes} {b}))"
                    f" (and (not {expanded_condition}) ({relation} {no} {b})))")
        original, expanded = [f"({q} ((x Int)) {v})" for v in (original, expanded)]
    else:
        op = rng.choice(["xor", "=>", "=", "distinct"])
        values = [rng.choice(["p", "q", "true", "false", "(not p)"]) for _ in range(4)]
        original = f"({op} {' '.join(values)})"
        if op == "=>":
            expanded = values[-1]
            for v in reversed(values[:-1]):
                expanded = f"(or (not {v}) {expanded})"
        elif op == "xor":
            expanded = values[0]
            for v in values[1:]:
                expanded = f"(not (= {expanded} {v}))"
        else:
            pairs = [(i, j) for i in range(4) for j in range(i + 1, 4)] if op == "distinct" else [(0, 1), (1, 2), (2, 3)]
            relations = [f"(= {values[i]} {values[j]})" for i, j in pairs]
            if op == "distinct":
                relations = [f"(not {r})" for r in relations]
            expanded = f"(and {' '.join(relations)})"
        other = rng.choice(["forall", "exists"])
        original, expanded = [f"({q} ((p Bool)) ({other} ((q Bool)) {v}))"
                              for v in (original, expanded)]
    if rng.getrandbits(1):
        original, expanded = f"(not {original})", f"(not {expanded})"
    return [f"(set-logic LIA)(assert {v})(check-sat)\n" for v in (original, expanded)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "z3", "cvc5", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--n", type=int, default=200)
    parser.add_argument("--suite", choices=["syntax", "piecewise"], default="syntax")
    args = parser.parse_args()
    root = Path(args.output)
    root.mkdir(parents=True, exist_ok=False)
    rng = random.Random(args.seed)
    counts = dict(pairs=args.n, checked=0, mismatches=0, inconclusive=0)
    records = []
    for i in range(args.n):
        variants = []
        generate = pair if args.suite == "syntax" else piecewise_pair
        for name, source in zip(("original", "expanded"), generate(rng, i)):
            path = root / f"{i:04}-{name}.smt2"
            path.write_text(source)
            observations = {
                "z3": invoke([args.z3, "-smt2", str(path)], 10),
                "cvc5": invoke([args.cvc5, "--lang=smt2", str(path)], 10),
                "xolver": invoke([args.solver, "solve", str(path)], 10),
            }
            variants.append(dict(input=path.name,
                                 sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                                 observations=observations))
        results = [x["result"] for variant in variants for x in variant["observations"].values()]
        if all(r in {"sat", "unsat"} for r in results):
            counts["checked"] += 1
            counts["mismatches"] += len(set(results)) != 1
        else:
            counts["inconclusive"] += 1
        records.append(variants)
        (root / "progress.json").write_text(json.dumps({**counts, "completed": i + 1}) + "\n")
    report = dict(counts=counts, seed=args.seed, suite=args.suite, records=records,
                  binaries={name: dict(path=getattr(args, name), sha256=hashlib.sha256(
                      Path(getattr(args, name)).read_bytes()).hexdigest())
                            for name in ("solver", "z3", "cvc5")})
    (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(counts["mismatches"] != 0 or counts["checked"] != args.n)


if __name__ == "__main__":
    raise SystemExit(main())
