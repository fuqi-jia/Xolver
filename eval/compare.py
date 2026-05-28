"""eval.compare — baseline-vs-candidate solved-delta diff + promotion gate.

The per-flag recovery-differential report: run baseline (floors only) and
candidate (floors + the flag) on the SAME aligned set with z3/cvc5 compare, then
this shows, per family and overall, the solved@1200 / solved@24 / wrong deltas.

Promotion rule (0-unsound is the FLOOR, not the bar):
  promote  iff  overall solved-delta > 0 (1200 OR 24)
           AND  0 added wrong
           AND  0 decided-disagreements (z3/cvc5 MISMATCH + optional BLAN).
A sound flag with no solve gain (or pure time loss) does NOT promote.

z3/cvc5 only by default — pass --blan to fold the BLAN oracle in (QF_NIA).
Python 3.6+ / stdlib only.
"""
import argparse
import sys
from typing import Dict, List, Optional

from eval._compat import dataclass
from eval.analyze import GROUPERS
from eval.loader import load_run_dir
from eval.model import CaseResult
from eval.oracle import BlanRow, decided_disagreements, load_blan_csv
from eval.score import score


@dataclass
class GroupDiff:
    group: str
    base_solved_1200: int
    cand_solved_1200: int
    d_solved_1200: int
    base_solved_24: int
    cand_solved_24: int
    d_solved_24: int
    base_wrong: int
    cand_wrong: int
    d_wrong: int


@dataclass
class CompareResult:
    groups: List[GroupDiff]
    overall: GroupDiff
    decided_disagreements: int
    promote: bool
    reason: str


def _diff(group, base_cases, cand_cases, main_t, fast_t) -> GroupDiff:
    b = score(base_cases, main_t, fast_t)
    c = score(cand_cases, main_t, fast_t)
    return GroupDiff(group,
                     b.solved_1200, c.solved_1200, c.solved_1200 - b.solved_1200,
                     b.solved_24, c.solved_24, c.solved_24 - b.solved_24,
                     b.wrong, c.wrong, c.wrong - b.wrong)


def compare_runs(base: List[CaseResult], cand: List[CaseResult], group_by: str = "family",
                 main_t: float = 1200.0, fast_t: float = 24.0,
                 blan_map: Optional[Dict[str, BlanRow]] = None) -> CompareResult:
    grouper = GROUPERS.get(group_by, GROUPERS["family"])
    bg, cg = {}, {}
    for x in base:
        bg.setdefault(grouper(x), []).append(x)
    for x in cand:
        cg.setdefault(grouper(x), []).append(x)
    groups = [_diff(g, bg.get(g, []), cg.get(g, []), main_t, fast_t)
              for g in sorted(set(bg) | set(cg))]
    overall = _diff("ALL", base, cand, main_t, fast_t)

    dd = len(decided_disagreements(cand, blan_map=blan_map, oracle_label="oracle"))
    gained = overall.d_solved_1200 > 0 or overall.d_solved_24 > 0
    no_new_wrong = overall.d_wrong <= 0
    promote = gained and no_new_wrong and dd == 0
    if dd > 0:
        reason = "NO: %d decided-disagreement(s) — 0-unsound floor breached" % dd
    elif not no_new_wrong:
        reason = "NO: +%d wrong" % overall.d_wrong
    elif not gained:
        reason = ("NO: no solved-count gain (d@1200=%+d, d@24=%+d)"
                  % (overall.d_solved_1200, overall.d_solved_24))
    else:
        reason = ("PROMOTE: d@1200=%+d, d@24=%+d, 0 added wrong, 0 disagreements"
                  % (overall.d_solved_1200, overall.d_solved_24))
    return CompareResult(groups, overall, dd, promote, reason)


_HEADER = "{:<30} {:>11} {:>9} {:>7}".format("group", "d_solved@1200", "d_solved@24", "d_wrong")


def _row(g: GroupDiff) -> str:
    return "{:<30} {:>+11d} {:>+9d} {:>+7d}".format(
        g.group[:30], g.d_solved_1200, g.d_solved_24, g.d_wrong)


def format_compare(res: CompareResult) -> str:
    lines = [_HEADER, "-" * len(_HEADER)]
    for g in res.groups:
        # show only families that moved, to keep the report readable
        if g.d_solved_1200 or g.d_solved_24 or g.d_wrong:
            lines.append(_row(g))
    lines.append("-" * len(_HEADER))
    lines.append(_row(res.overall))
    lines.append("decided-disagreements (0-unsound check): %d" % res.decided_disagreements)
    lines.append("Promote? %s  — %s" % ("YES" if res.promote else "NO", res.reason))
    return "\n".join(lines)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Baseline-vs-candidate solved-delta diff + promotion gate (per flag).")
    p.add_argument("--baseline", required=True, help="baseline run dir (floors only)")
    p.add_argument("--candidate", required=True, help="candidate run dir (floors + flag)")
    p.add_argument("--by", default="family", choices=sorted(GROUPERS))
    p.add_argument("--blan", default=None, help="optional BLAN CSV/glob/dir (QF_NIA +1 oracle)")
    p.add_argument("--main-timeout", type=float, default=1200)
    p.add_argument("--fast-timeout", type=float, default=24)
    args = p.parse_args(argv)

    base = load_run_dir(args.baseline)
    cand = load_run_dir(args.candidate)
    blan = load_blan_csv(args.blan) if args.blan else None
    res = compare_runs(base, cand, group_by=args.by, main_t=args.main_timeout,
                       fast_t=args.fast_timeout, blan_map=blan)
    print(format_compare(res))
    return 0 if res.promote else 1


if __name__ == "__main__":
    sys.exit(main())
