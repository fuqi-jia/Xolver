"""eval.analyze — score an Xolver benchmark run into the 4 SMT-COMP tables.

Usage:
  python3 -m eval.analyze --run-dir results/run_2026... --by logic
  python3 -m eval.analyze --stats results/run_.../QF_NIA/statistics.json --by family
  python3 -m eval.analyze --run-dir <dir> --by timeout_bucket --json

File-based: reads run_benchmark.py outputs, never re-runs the solver.
Python 3.7+ / stdlib only.
"""
import argparse
import json
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional

from eval.loader import load_run_dir, load_statistics_json
from eval.model import CaseResult
from eval.score import Score, score, score_by


def timeout_bucket(t: float) -> str:
    if t < 1:
        return "<1s"
    if t < 24:
        return "1-24s"
    if t < 300:
        return "24-300s"
    if t < 1200:
        return "300-1200s"
    return "1200s+"


GROUPERS = {
    "logic": lambda c: c.logic,
    "family": lambda c: "%s/%s" % (c.logic, c.family),
    "sat_status": lambda c: c.result,
    "timeout_bucket": lambda c: timeout_bucket(c.time),
}


@dataclass
class Report:
    label: str
    overall: Score
    groups: Dict[str, Score]
    group_by: str


def build_report(cases: List[CaseResult], main_t: float = 1200.0, fast_t: float = 24.0,
                 group_by: str = "logic", label: str = "run") -> Report:
    grouper = GROUPERS.get(group_by, GROUPERS["logic"])
    return Report(label=label,
                  overall=score(cases, main_t, fast_t),
                  groups=score_by(cases, grouper, main_t, fast_t),
                  group_by=group_by)


_HEADER = "{:<30} {:>7} {:>11} {:>9} {:>6} {:>6} {:>6} {:>9}".format(
    "group", "total", "solved@1200", "solved@24", "sat", "unsat", "wrong", "PAR2")


def _fmt_row(name: str, s: Score) -> str:
    return "{:<30} {:>7} {:>11} {:>9} {:>6} {:>6} {:>6} {:>9.1f}".format(
        name[:30], s.total, s.solved_1200, s.solved_24, s.sat, s.unsat, s.wrong, s.par2)


def format_report(rep: Report) -> str:
    lines = ["== %s : by %s ==" % (rep.label, rep.group_by), _HEADER, "-" * len(_HEADER)]
    for name in sorted(rep.groups):
        lines.append(_fmt_row(name, rep.groups[name]))
    lines.append("-" * len(_HEADER))
    lines.append(_fmt_row("ALL", rep.overall))
    if rep.overall.wrong:
        lines.append("*** %d WRONG (decided-disagreement) — primary sort key, must be 0 ***"
                     % rep.overall.wrong)
    return "\n".join(lines)


def _score_dict(s: Score) -> dict:
    return {"total": s.total, "solved_1200": s.solved_1200, "solved_24": s.solved_24,
            "sat": s.sat, "unsat": s.unsat, "wrong": s.wrong, "unknown": s.unknown,
            "par2": s.par2}


def report_to_dict(rep: Report) -> dict:
    return {"label": rep.label, "group_by": rep.group_by,
            "overall": _score_dict(rep.overall),
            "groups": {k: _score_dict(v) for k, v in rep.groups.items()}}


def _load(args) -> List[CaseResult]:
    if args.stats:
        return load_statistics_json(args.stats)
    return load_run_dir(args.run_dir)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Score an Xolver run into the 4 SMT-COMP tables (1200s/24s/SAT/UNSAT).")
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--run-dir", help="A run dir (RUN_DIR/<LOGIC>/statistics.json)")
    src.add_argument("--stats", help="A single statistics.json")
    p.add_argument("--by", default="logic", choices=sorted(GROUPERS),
                   help="group-by dimension (default: logic)")
    p.add_argument("--main-timeout", type=float, default=1200.0,
                   help="competition wall for solved@1200 (default 1200)")
    p.add_argument("--fast-timeout", type=float, default=24.0,
                   help="fast-path wall for solved@24 (default 24)")
    p.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    p.add_argument("--label", default="run")
    args = p.parse_args(argv)
    cases = _load(args)
    rep = build_report(cases, args.main_timeout, args.fast_timeout, args.by, args.label)
    if args.json:
        print(json.dumps(report_to_dict(rep), indent=2))
    else:
        print(format_report(rep))
    return 0


if __name__ == "__main__":
    sys.exit(main())
