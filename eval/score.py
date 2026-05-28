"""eval.score — the 4 SMT-COMP score tables + PAR-2, computed offline.

The four published Single-Query sub-scores, all derivable from one 1200s run's
per-case (result, time):
  - solved_1200 : decided (sat/unsat), within main_t, not wrong
  - solved_24   : same, re-scored at the 24s wall (fast_t)
  - sat / unsat : the solved split (the published SAT/UNSAT sub-scores)
Plus:
  - wrong   : decided-disagreement vs the oracle (run_benchmark MISMATCH). This
              is the PRIMARY competition sort key — one wrong answer sinks a
              division below every zero-error solver. Disjoint from solved.
  - unknown : neither solved-within-budget nor wrong = "free" (e=0, n=0).
  - par2    : mean penalized runtime (solved -> time, else 2*main_t).

Python 3.7+ / stdlib only.
"""
from typing import Callable, Dict, List

from eval._compat import dataclass
from eval.model import CaseResult

DECIDED = ("sat", "unsat")


@dataclass
class Score:
    total: int = 0
    solved_1200: int = 0
    solved_24: int = 0
    sat: int = 0
    unsat: int = 0
    wrong: int = 0
    unknown: int = 0
    par2: float = 0.0


def is_wrong(c: CaseResult) -> bool:
    """A decided-disagreement against the oracle (run_benchmark MISMATCH)."""
    return c.match == "MISMATCH"


def is_decided(c: CaseResult) -> bool:
    return c.result in DECIDED


def score(cases: List[CaseResult], main_t: float = 1200.0, fast_t: float = 24.0) -> Score:
    s = Score(total=len(cases))
    penalty = 0.0
    for c in cases:
        if is_wrong(c):
            s.wrong += 1
            penalty += 2.0 * main_t
            continue
        solved_main = is_decided(c) and c.time <= main_t
        if solved_main:
            s.solved_1200 += 1
            if c.result == "sat":
                s.sat += 1
            else:
                s.unsat += 1
            if c.time <= fast_t:
                s.solved_24 += 1
            penalty += c.time
        else:
            # Undecided (unknown/timeout/error/killed), or decided but slower
            # than main_t — not solved within budget, not wrong: free.
            s.unknown += 1
            penalty += 2.0 * main_t
    s.par2 = penalty / s.total if s.total else 0.0
    return s


def score_by(cases: List[CaseResult], key_fn: Callable[[CaseResult], str],
             main_t: float = 1200.0, fast_t: float = 24.0) -> Dict[str, Score]:
    """Group cases by key_fn(case) and score each group independently."""
    groups: Dict[str, List[CaseResult]] = {}
    for c in cases:
        groups.setdefault(key_fn(c), []).append(c)
    return {k: score(v, main_t, fast_t) for k, v in groups.items()}
