#!/usr/bin/env python3
"""Server-only PA kernel replay, including deliberately false claims."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from unittest.mock import patch

# Installed under tools/remote in a checkout, or staged together in build/.
proof = Path(__file__).resolve().parents[1] / "proof"
if proof.is_dir():
    sys.path.insert(0, str(proof))
from replay_pa import replay
from isabelle_pa import Query


FIXTURES = [
    ("successor", "(assert (forall ((x Int)) (exists ((y Int)) (> y x))))", "sat"),
    ("parity", "(assert (forall ((x Int)) (exists ((y Int)) (= x (* 2 y)))))", "unsat"),
    ("division", "(assert (forall ((x Int)) (= x (+ (* (- 3) (div x (- 3))) (mod x (- 3))))))", "sat"),
    ("remainder", "(assert (exists ((x Int)) (< (mod x (- 3)) 0)))", "unsat"),
    ("let-scope", "(declare-const x Int)(assert (= x 2))"
     "(assert (let ((x 1) (y x)) (= y x)))", "unsat"),
    ("shadow", "(assert (exists ((x Int)) (and (= x 1) "
     "(exists ((x Int)) (= x 0)))))", "sat"),
    ("free-bool", "(declare-const p Bool)(declare-const x Int)"
     "(assert (and p (= x 4) (exists ((y Int)) (= x (* 2 y)))))", "sat"),
    ("boolean-chain", "(declare-const p Bool)(assert (= p true false))", "unsat"),
    ("implication-chain", "(assert (=> false true false))", "sat"),
    ("strict-chain", "(assert (exists ((x Int)) (< 0 x 1)))", "unsat"),
    ("large", "(assert (exists ((x Int)) (= (* 3 x) 3000000000000000000000000000003)))", "sat"),
    ("signed-division", "(assert (forall ((x Int)) (= (div x (- 3)) (- (div x 3)))))", "sat"),
    ("bool-alternation", "(assert (forall ((p Bool)) (exists ((q Bool)) (distinct p q))))", "sat"),
    ("bool-uniform-witness", "(assert (exists ((p Bool)) (forall ((q Bool)) (distinct p q))))", "unsat"),
    ("mixed-uniform-witness", "(assert (exists ((x Int))"
     " (forall ((p Bool)) (= x (ite p 3 (- 2))))))", "unsat"),
    ("abs-quantified-condition", "(assert (forall ((x Int))"
     " (= (ite (forall ((y Int)) (>= (+ y x) y)) x (- x)) (abs x))))", "sat"),
    ("abs-negative-preimage", "(assert (exists ((x Int)) (= (abs x) (- 1))))", "unsat"),
    ("abs-signed-division", "(assert (forall ((x Int))"
     " (= (+ (* (- 3) (div (abs x) (- 3))) (mod (abs x) (- 3))) (abs x))))", "sat"),
    ("distinct-constants", "(assert (exists ((p Bool))"
     " (forall ((q Bool)) (distinct true false false false))))", "unsat"),
    ("distinct-negation", "(declare-const p Bool)(declare-const q Bool)"
     "(assert p)(assert q)(assert (distinct (not p) q))", "sat"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--isabelle", type=Path, required=True)
    parser.add_argument("--cache", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pa-report", type=Path)
    parser.add_argument("--sample", type=int, default=24)
    args = parser.parse_args()
    if args.sample < 0:
        parser.error("--sample must be nonnegative")
    args.output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(__file__, args.output / "audit_driver.py")
    sources = args.output / "sources"
    sources.mkdir()
    counts = dict(fixture_disagreements=0, verified_claims=0,
                  false_verdict_rejected=0, false_model_rejected=0,
                  false_normalized_verdict_rejected=0, false_normalization_rejected=0)
    claims, observations = [], []
    for name, assertions, expected in FIXTURES:
        path = sources / (name + ".smt2")
        path.write_text("(set-logic LIA)\n" + assertions + "\n(check-sat)\n")
        process = subprocess.run([str(args.solver), "solve", str(path)], capture_output=True,
                                 text=True, timeout=30)
        answers = [s for s in process.stdout.splitlines() if s in {"sat", "unsat", "unknown"}]
        correct = process.returncode == 0 and answers == [expected]
        counts["fixture_disagreements"] += not correct
        observations.append(dict(input=name, expected=expected, rc=process.returncode,
                                 stdout=process.stdout, stderr=process.stderr))
        claims.append(dict(input=str(path), verdict=expected))
    if args.pa_report and args.sample:
        report = json.loads(args.pa_report.read_text())
        for row in report["records"]:
            verdict = row["observations"]["xolver"]["result"]
            if verdict not in {"sat", "unsat"}:
                continue
            path = args.pa_report.parent / row["input"]
            if hashlib.sha256(path.read_bytes()).hexdigest() != row["sha256"]:
                raise RuntimeError("differential input changed")
            claims.append(dict(input=str(path), verdict=verdict))
            if len(claims) == len(FIXTURES) + args.sample:
                break
    # Check a supplied free-variable assignment against the original quantified
    # formula, rather than against the solver's eliminated formula.
    model_path = sources / "model.smt2"
    model_path.write_text("(set-logic LIA)(declare-const x Int)(declare-const p Bool)"
                          "(assert (and p (exists ((y Int)) (= x (* 2 y)))))"
                          "(assert (forall ((q Bool))"
                          " (= (ite q x (- x)) (ite q (- 6) 6))))"
                          "(check-sat)\n")
    claims.append(dict(input=str(model_path), verdict="sat", model=dict(x=-6, p=True)))
    (args.output / "solver-observations.json").write_text(json.dumps(observations, indent=2) + "\n")
    (args.output / "manifest.json").write_text(json.dumps(claims, indent=2) + "\n")
    # Separate acceptance tests from the larger elimination workload. A slow
    # stress case must not erase already kernel-checked targeted claims, while
    # aggregate success still requires every requested claim and both controls.
    targeted = claims[:len(FIXTURES)] + [claims[-1]]
    differential = claims[len(FIXTURES):-1]
    counts["expected_claims"] = len(claims)
    positive = replay(targeted, args.isabelle, args.output / "targeted", args.cache, 180)
    if positive["verified"]:
        counts["verified_claims"] = len(targeted)
        negatives = [
            ("false-verdict", dict(input=str(sources / "successor.smt2"), verdict="unsat"),
             "false_verdict_rejected"),
            ("false-model", dict(input=str(model_path), verdict="sat", model=dict(x=-5, p=True)),
             "false_model_rejected"),
            ("false-normalized-verdict", dict(input=str(sources / "large.smt2"), verdict="unsat"),
             "false_normalized_verdict_rejected"),
        ]
        for name, claim, metric in negatives:
            negative = replay([claim], args.isabelle, args.output / name, args.cache, 180)
            log = (args.output / name / "isabelle.log").read_text()
            # Infrastructure failure and timeout do not demonstrate rejection.
            counts[metric] = int(negative["returncode"] not in {0, 124} and
                                ("Failed to apply initial proof method" in log or
                                 "Failed to finish proof" in log))
        # Corrupt a helper while retaining the correct original SAT theorem.
        # This tests the kernel's treatment of hints, independently of verdict
        # and model rejection. The audit driver and generated theory record
        # the mutation; the production translator itself is left unchanged.
        normalize = Query.normalization
        def false_hint(self, *arguments):
            normalize(self, *arguments)
            for key in self.normalizations:
                self.normalizations[key] = "False"
        with patch.object(Query, "normalization", false_hint):
            bad_hint = replay([dict(input=str(sources / "large.smt2"), verdict="sat")],
                              args.isabelle, args.output / "false-normalization", args.cache, 180)
        (args.output / "false-normalization/mutation.json").write_text(json.dumps({
            "test_only": True, "mutation": "Replace every proposed normalized right-hand side with False",
            "original_verdict_unchanged": True}) + "\n")
        log = (args.output / "false-normalization/isabelle.log").read_text()
        counts["false_normalization_rejected"] = int(
            bad_hint["returncode"] not in {0, 124} and
            ("Failed to apply initial proof method" in log or "Failed to finish proof" in log))
        (args.output / "progress.json").write_text(json.dumps(counts, indent=2) + "\n")
        if differential:
            stress = replay(differential, args.isabelle, args.output / "differential", args.cache, 900)
            if stress["verified"]:
                counts["verified_claims"] += len(differential)
    counts["passed"] = int(counts["verified_claims"] == len(claims) and
                           counts["fixture_disagreements"] == 0 and
                           counts["false_verdict_rejected"] == 1 and
                           counts["false_model_rejected"] == 1 and
                           counts["false_normalized_verdict_rejected"] == 1 and
                           counts["false_normalization_rejected"] == 1)
    (args.output / "metrics.json").write_text(json.dumps(counts, indent=2) + "\n")
    if os.environ.get("EOS_METRICS_FILE"):
        Path(os.environ["EOS_METRICS_FILE"]).write_text(json.dumps(counts) + "\n")
    print(json.dumps(counts))
    return not counts["passed"]


if __name__ == "__main__":
    raise SystemExit(main())
