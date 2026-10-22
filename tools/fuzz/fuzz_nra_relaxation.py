#!/usr/bin/env python3
"""Exercise nonlinear affine relaxations against exact witnesses and two oracles."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random

from fuzz_presburger import invoke, numeral


def problem(rng, index):
    names = ("x", "y", "z")
    point = [rng.randint(-3, 3) for _ in names]

    def monomial():
        factors = [rng.randrange(len(names)) for _ in range(rng.randint(1, 3))]
        rng.shuffle(factors)
        value = 1
        for factor in factors:
            value *= point[factor]
        return "(* " + " ".join(names[factor] for factor in factors) + " 1)", value

    def polynomial():
        parts, value = [], 0
        for _ in range(rng.randint(2, 4)):
            term, v = monomial()
            coefficient = rng.randint(-5, 5)
            parts.append(f"(* {numeral(coefficient)} {term})")
            value += coefficient * v
        return "(+ " + " ".join(parts) + ")", value

    def scaled_relation(term, relation, bound):
        scale = rng.choice([-7, -3, -1, 1, 2, 5])
        if scale < 0:
            relation = {"<": ">", "<=": ">=", ">": "<", ">=": "<=",
                        "=": "=", "distinct": "distinct"}[relation]
        return f"({relation} (* {numeral(scale)} {term}) {numeral(scale * bound)})"

    mode = index % 4
    witness = None
    if mode == 0:
        clauses = []
        for _ in range(5):
            term, value = polynomial()
            relation = rng.choice(["=", "<", "<=", ">", ">=", "distinct"])
            bound = value
            if relation in ("<", "<=", "distinct"):
                bound += rng.randint(1, 4)
            elif relation in (">", ">="):
                bound -= rng.randint(1, 4)
            clauses.append(scaled_relation(term, relation, bound))
        formula = "(and " + " ".join(clauses) + ")"
        expected, witness = "sat", dict(zip(names, point))
    elif mode in (1, 2):
        left, _ = polynomial()
        right, _ = polynomial()
        a, b = rng.randint(-4, 4), rng.randint(-4, 4)
        # The first family needs a multirow affine contradiction. The second
        # relies on strictness at an equal rational boundary.
        clauses = [
            scaled_relation(left, "<=", a),
            scaled_relation(right, "<=", b),
            scaled_relation(f"(+ {left} {right})",
                            ">=" if mode == 1 else ">", a + b + (mode == 1)),
        ]
        rng.shuffle(clauses)
        # Force SAT search to see both signed arithmetic assumptions and an
        # irrelevant disjunction. Either branch of the disjunction is harmless.
        extra, _ = polynomial()
        formula = "(and " + " ".join(clauses) + f" (or flag (= {extra} 0)))"
        expected = "unsat"
    else:
        atoms = []
        for _ in range(3):
            term, _ = polynomial()
            atoms.append(scaled_relation(term, rng.choice(["<=", ">", "=", "distinct"]),
                                        rng.randint(-4, 4)))
        formula = f"(and {atoms[0]} (or {atoms[1]} {atoms[2]}))"
        expected = None
    script = "(set-logic QF_NRA)\n(declare-const flag Bool)\n"
    script += "".join(f"(declare-const {name} Real)\n" for name in names)
    script += f"(assert {formula})\n(check-sat)\n"
    return script, expected, witness


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("solver", "z3", "cvc5", "output"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--n", type=int, default=160)
    parser.add_argument("--timeout", type=float, default=8)
    args = parser.parse_args()
    root = Path(args.output)
    root.mkdir(parents=True, exist_ok=True)
    rng = random.Random(args.seed)
    counts = dict(generated=args.n, checked=0, unsound=0, errors=0, unknown=0,
                  timeouts=0, oracle_skips=0, oracle_disagreements=0,
                  known_answers=0, known_disagreements=0)
    records = []
    for index in range(args.n):
        script, expected, witness = problem(rng, index)
        path = root / f"case-{index:04}.smt2"
        path.write_text(script)
        observations = {
            "z3": invoke([args.z3, "-smt2", str(path)], args.timeout),
            "cvc5": invoke([args.cvc5, "--lang=smt2", str(path)], args.timeout),
            "xolver": invoke([args.solver, "solve", str(path)], args.timeout),
        }
        z3, cvc5, candidate = (observations[k]["result"] for k in ("z3", "cvc5", "xolver"))
        definite = {"sat", "unsat"}
        if z3 in definite and cvc5 in definite and z3 != cvc5:
            counts["oracle_disagreements"] += 1
        elif z3 == cvc5 and z3 in definite:
            counts["checked"] += 1
            counts["unsound"] += int(candidate in definite and candidate != z3)
        else:
            counts["oracle_skips"] += 1
        if expected:
            counts["known_answers"] += 1
            counts["known_disagreements"] += sum(
                o["result"] in definite and o["result"] != expected
                for o in observations.values())
        counts["errors"] += int(candidate == "error")
        counts["unknown"] += int(candidate == "unknown")
        counts["timeouts"] += int(candidate == "timeout")
        records.append(dict(input=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                            expected=expected, witness=witness, observations=observations))
        (root / "progress.json").write_text(json.dumps({**counts, "completed": index + 1}) + "\n")
    report = dict(seed=args.seed, counts=counts, records=records,
                  binaries={name: dict(path=getattr(args, name),
                                       sha256=hashlib.sha256(Path(getattr(args, name)).read_bytes()).hexdigest())
                            for name in ("solver", "z3", "cvc5")})
    (root / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return int(not counts["checked"] or counts["unsound"] or counts["errors"]
               or counts["oracle_disagreements"] or counts["known_disagreements"])


if __name__ == "__main__":
    raise SystemExit(main())
