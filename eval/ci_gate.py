"""eval.ci_gate — promotion gate + scramble-stability for the final candidate.

Two checks, both exit-nonzero on failure (for CI / promotion):

  gate     : require-zero-wrong (no decided-disagreement vs z3/cvc5 OR BLAN) AND
             no-24s-regression vs a baseline run. A wrong answer is the primary
             competition sort key, so it is an unconditional FAIL.

  scramble : scramble-stability. The competition scrambles inputs, so a config
             must not depend on syntactic features. We compare a scrambled run
             against the unscrambled run of the SAME config and FAIL on:
               - any verdict FLIP (sat<->unsat on the same case) = soundness bug
               - a solved-count drop beyond tolerance = scramble-fragile config
             Join is by canonical key: run_benchmark writes scrambled files to
             /tmp/xolver-scrambled-s<seed>/<original-path>, which preserves the
             "<LOGIC>/<family>/<file>.smt2" suffix, so normalize_key()'s
             last-occurrence rule joins scrambled<->unscrambled automatically.

Python 3.7+ / stdlib only.
"""
import argparse
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional

from eval.loader import load_run_dir
from eval.model import CaseResult
from eval.oracle import BlanRow, decided_disagreements, load_blan_csv
from eval.score import score

DECIDED = ("sat", "unsat")


@dataclass
class GateResult:
    passed: bool
    wrong: int
    candidate_solved_1200: int
    candidate_solved_24: int
    baseline_solved_24: Optional[int]
    solved_24_delta: Optional[int]
    reasons: List[str] = field(default_factory=list)


def gate(candidate: List[CaseResult], baseline: Optional[List[CaseResult]] = None,
         blan_map: Optional[Dict[str, BlanRow]] = None, main_t: float = 1200.0,
         fast_t: float = 24.0, allow_24s_regression: int = 0) -> GateResult:
    reasons: List[str] = []
    passed = True

    dis = decided_disagreements(candidate, blan_map=blan_map, oracle_label="oracle")
    wrong = len(dis)
    if wrong > 0:
        passed = False
        reasons.append("require-zero-wrong FAILED: %d decided-disagreement(s)" % wrong)
        for d in dis[:10]:
            reasons.append("    %s  xolver=%s  %s=%s" % (d.key, d.xolver_result, d.oracle, d.oracle_result))

    cs = score(candidate, main_t, fast_t)
    base24: Optional[int] = None
    delta: Optional[int] = None
    if baseline is not None:
        bs = score(baseline, main_t, fast_t)
        base24 = bs.solved_24
        delta = cs.solved_24 - bs.solved_24
        if delta < -abs(allow_24s_regression):
            passed = False
            reasons.append("no-24s-regression FAILED: solved@24 %d -> %d (delta %d)"
                           % (bs.solved_24, cs.solved_24, delta))

    if passed:
        reasons.append("PASS: 0 wrong; solved@24 not regressed (delta %s)"
                       % ("n/a" if delta is None else delta))
    return GateResult(passed, wrong, cs.solved_1200, cs.solved_24, base24, delta, reasons)


@dataclass
class StabilityResult:
    passed: bool
    flips: List[str]
    solved_unscrambled: int
    solved_scrambled: int
    reasons: List[str] = field(default_factory=list)


def scramble_stability(unscrambled: List[CaseResult], scrambled: List[CaseResult],
                       main_t: float = 1200.0, fast_t: float = 24.0,
                       tolerance: int = 0) -> StabilityResult:
    by_key = {c.key: c for c in unscrambled}
    flips: List[str] = []
    for c in scrambled:
        u = by_key.get(c.key)
        if u and u.result in DECIDED and c.result in DECIDED and u.result != c.result:
            flips.append(c.key)

    su = score(unscrambled, main_t, fast_t).solved_1200
    ss = score(scrambled, main_t, fast_t).solved_1200
    reasons: List[str] = []
    passed = True
    if flips:
        passed = False
        reasons.append("VERDICT FLIPS under scramble (SOUNDNESS BUG): %d" % len(flips))
        for k in flips[:10]:
            reasons.append("    %s" % k)
    if su - ss > abs(tolerance):
        passed = False
        reasons.append("scramble-fragile: solved %d -> %d (drop %d)" % (su, ss, su - ss))
    if passed:
        reasons.append("PASS: stable under scramble (solved %d -> %d, 0 flips)" % (su, ss))
    return StabilityResult(passed, flips, su, ss, reasons)


def _cmd_gate(args) -> int:
    candidate = load_run_dir(args.candidate)
    baseline = load_run_dir(args.baseline) if args.baseline else None
    blan = load_blan_csv(args.blan) if args.blan else None
    r = gate(candidate, baseline=baseline, blan_map=blan,
             main_t=args.main_timeout, fast_t=args.fast_timeout,
             allow_24s_regression=args.allow_24s_regression)
    print("=== CI GATE: %s ===" % ("PASS" if r.passed else "FAIL"))
    print("wrong=%d  solved@1200=%d  solved@24=%d  baseline@24=%s  delta@24=%s"
          % (r.wrong, r.candidate_solved_1200, r.candidate_solved_24,
             r.baseline_solved_24, r.solved_24_delta))
    for line in r.reasons:
        print("  " + line)
    return 0 if r.passed else 1


def _cmd_scramble(args) -> int:
    uns = load_run_dir(args.unscrambled)
    scr = load_run_dir(args.scrambled)
    r = scramble_stability(uns, scr, main_t=args.main_timeout, fast_t=args.fast_timeout,
                           tolerance=args.tolerance)
    print("=== SCRAMBLE STABILITY: %s ===" % ("PASS" if r.passed else "FAIL"))
    for line in r.reasons:
        print("  " + line)
    return 0 if r.passed else 1


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="CI promotion gate + scramble-stability.")
    sub = p.add_subparsers(dest="cmd", required=True)

    g = sub.add_parser("gate", help="require-zero-wrong + no-24s-regression")
    g.add_argument("--candidate", required=True, help="candidate run dir")
    g.add_argument("--baseline", default=None, help="baseline run dir (for 24s regression)")
    g.add_argument("--blan", default=None, help="BLAN CSV / glob / dir (QF_NIA 3rd oracle)")
    g.add_argument("--main-timeout", type=float, default=1200)
    g.add_argument("--fast-timeout", type=float, default=24)
    g.add_argument("--allow-24s-regression", type=int, default=0)
    g.set_defaults(func=_cmd_gate)

    s = sub.add_parser("scramble", help="scramble-stability of one config")
    s.add_argument("--unscrambled", required=True, help="unscrambled run dir")
    s.add_argument("--scrambled", required=True, help="scrambled run dir (same config)")
    s.add_argument("--main-timeout", type=float, default=1200)
    s.add_argument("--fast-timeout", type=float, default=24)
    s.add_argument("--tolerance", type=int, default=0, help="allowed solved-count drop")
    s.set_defaults(func=_cmd_scramble)

    args = p.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
