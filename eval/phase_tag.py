"""eval.phase_tag — parse-phase vs solve-phase tagging x oracle-solvability.

One corpus pass answers a decided question. Run each case BOTH parse-only (small
budget, via NIA's --parse-only) and in the normal solve differential, then tag:

  parse   : parse-only timed out at the small budget -> the case never finished
            parsing (eager define-fun expansion blowup).
  solved  : parsed fine and the solve run decided it (sat/unsat).
  solve   : parsed fine but the solve run failed (timeout/unknown/error).

Crossed with oracle-solvability (z3/cvc5 decided), this yields:
  (b) parse_blowup = oracle-DECIDED cases that die at PARSE — i.e. solvable
      problems lost before solving starts. That number decides whether a
      lazy-macro frontend fix earns the roadmap.
  (a) the solve-phase set is where the gated levers (XOLVER_NIA_MODULAR / UNSAT,
      XOLVER_NIA_LOCALSEARCH / SAT) can actually recover — feed it to
      eval.compare for the solved-delta.

Python 3.6+ / stdlib only.
"""
import argparse
import sys
from typing import Dict, List, Optional

from eval._compat import dataclass, field
from eval.loader import load_run_dir
from eval.model import CaseResult

DECIDED = ("sat", "unsat")
PARSE_FAIL = ("timeout", "killed", "error")
PHASES = ("parse", "solve", "solved")


def classify_phase(parse_result: str, parse_time: float, main_result: str,
                   parse_budget: float = 0.0) -> str:
    """parse | solved | solve. parse_budget>0 also treats a parse-only run that
    hit the budget (time >= budget) as parse-phase even if it didn't report a
    failure verdict."""
    if parse_result in PARSE_FAIL or (parse_budget and parse_time >= parse_budget):
        return "parse"
    if main_result in DECIDED:
        return "solved"
    return "solve"


@dataclass
class PhaseReport:
    counts: Dict[str, int] = field(default_factory=dict)            # phase -> total
    solvable_counts: Dict[str, int] = field(default_factory=dict)   # phase -> oracle-decided
    parse_blowup: int = 0                                           # answer (b)
    by_family_parse_blowup: Dict[str, int] = field(default_factory=dict)
    joined: int = 0
    parse_only_unmatched: int = 0


def solve_phase_keys(parse_cases: List[CaseResult], main_cases: List[CaseResult],
                     parse_budget: float = 0.0) -> List[str]:
    """Keys that parsed fine but the solve run did not decide — the recovery
    target set for the gated levers (answer a)."""
    pmap = {c.key: c for c in parse_cases}
    out = []
    for m in main_cases:
        p = pmap.get(m.key)
        if p is None:
            continue
        if classify_phase(p.result, p.time, m.result, parse_budget) == "solve":
            out.append(m.key)
    return out


def phase_report(parse_cases: List[CaseResult], main_cases: List[CaseResult],
                 parse_budget: float = 0.0) -> PhaseReport:
    pmap = {c.key: c for c in parse_cases}
    counts = {p: 0 for p in PHASES}
    solvable = {p: 0 for p in PHASES}
    byfam: Dict[str, int] = {}
    joined = 0
    for m in main_cases:
        p = pmap.get(m.key)
        if p is None:
            continue
        joined += 1
        phase = classify_phase(p.result, p.time, m.result, parse_budget)
        counts[phase] += 1
        is_solvable = m.oracle_result in DECIDED
        if is_solvable:
            solvable[phase] += 1
            if phase == "parse":
                byfam[m.family] = byfam.get(m.family, 0) + 1
    return PhaseReport(counts=counts, solvable_counts=solvable,
                       parse_blowup=solvable["parse"], by_family_parse_blowup=byfam,
                       joined=joined,
                       parse_only_unmatched=max(0, len(pmap) - joined))


def format_phase(r: PhaseReport) -> str:
    lines = ["joined %d cases (parse-only run + solve run)" % r.joined,
             "{:<8} {:>7} {:>16}".format("phase", "total", "oracle-decided"),
             "-" * 33]
    for p in PHASES:
        lines.append("{:<8} {:>7} {:>16}".format(p, r.counts.get(p, 0),
                                                  r.solvable_counts.get(p, 0)))
    lines.append("-" * 33)
    lines.append("(b) PARSE-BLOWUP (oracle-decided cases dying at parse): %d" % r.parse_blowup)
    if r.by_family_parse_blowup:
        lines.append("    by family:")
        for fam in sorted(r.by_family_parse_blowup,
                          key=lambda k: (-r.by_family_parse_blowup[k], k)):
            lines.append("      %-28s %d" % (fam, r.by_family_parse_blowup[fam]))
    lines.append("(a) solve-phase failures (lever-recovery target): %d (%d oracle-decided)"
                 % (r.counts.get("solve", 0), r.solvable_counts.get("solve", 0)))
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Tag parse-phase vs solve-phase failures x oracle-solvability.")
    p.add_argument("--parse-only-run", required=True,
                   help="run dir from the solver --parse-only pass (small budget)")
    p.add_argument("--solve-run", required=True,
                   help="run dir from the normal solve differential (with z3/cvc5 compare)")
    p.add_argument("--parse-budget", type=float, default=0.0,
                   help="parse-only wall budget; time >= this also counts as parse-phase")
    args = p.parse_args(argv)
    parse_cases = load_run_dir(args.parse_only_run)
    main_cases = load_run_dir(args.solve_run)
    print(format_phase(phase_report(parse_cases, main_cases, args.parse_budget)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
