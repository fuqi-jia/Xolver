"""eval.modular_ladder — graded mod-2^k Xolver-vs-z3 agreement ladder.

The NIA-modular engine (XOLVER_NIA_MODULAR) targets power-of-2 moduli up to
2^256 (EVM / Certora), which is beyond every oracle. You can't validate the
summit directly, so this builds the soundness evidence as a LADDER: bucket the
designed mod-2^k cases by rung (8/16/32/... up to where z3 still decides) and
check Xolver-vs-z3 agreement per rung.

  - agree on every z3-decided rung + ZERO decided-disagreements  => the modular
    reasoning is sound on everything an oracle can check; the un-oracleable
    summit inherits that confidence.
  - ANY decided-disagreement on ANY rung => the engine is unsound (gate fails).

Oracle is z3/cvc5 only (no BLAN needed — runs the moment the binary has the
flag). For QF_UFNIA (Certora) the oracle is likewise z3/cvc5.

Python 3.6+ / stdlib only.
"""
import argparse
import re
import sys
from typing import Callable, List, Optional

from eval._compat import dataclass
from eval.loader import load_run_dir, load_statistics_json
from eval.model import CaseResult

DECIDED = ("sat", "unsat")
DEFAULT_RUNG_REGEX = r"mod[_-]?(\d+)|(\d+)[_-]?bit|2\^(\d+)"


def agreement(case: CaseResult) -> str:
    x, z = case.result, case.oracle_result
    xd, zd = x in DECIDED, z in DECIDED
    if xd and zd:
        return "agree" if x == z else "disagree"
    if xd and not zd:
        return "xolver_only"
    if zd and not xd:
        return "z3_only"
    return "both_unknown"


def rung_from_key(key: str, pattern: str) -> Optional[str]:
    m = re.search(pattern, key)
    if not m:
        return None
    for g in m.groups():
        if g:
            return g
    return None


def rung_from_constants(text: str) -> Optional[int]:
    """Best-effort modulus bit-width = the largest integer literal's exponent.

    A power-of-two modulus 2^k (e.g. 256) -> k; a mask 2^k - 1 -> k. Returns
    None when there's no non-trivial constant.
    """
    nums = [int(t) for t in re.findall(r"\d+", text)]
    nums = [n for n in nums if n > 1]
    if not nums:
        return None
    n = max(nums)
    if n & (n - 1) == 0:        # exact power of two -> exponent
        return n.bit_length() - 1
    return n.bit_length()        # mask 2^k - 1 -> k


@dataclass
class RungStats:
    rung: str
    total: int = 0
    z3_decided: int = 0
    agree: int = 0
    disagree: int = 0
    xolver_only: int = 0
    z3_only: int = 0
    both_unknown: int = 0


def ladder_report(cases: List[CaseResult],
                  rung_fn: Callable[[CaseResult], Optional[str]]) -> List[RungStats]:
    groups = {}
    for c in cases:
        rung = rung_fn(c)
        rung = "none" if rung is None else str(rung)
        st = groups.get(rung)
        if st is None:
            st = RungStats(rung=rung)
            groups[rung] = st
        st.total += 1
        kind = agreement(c)
        setattr(st, kind, getattr(st, kind) + 1)
        if c.oracle_result in DECIDED:
            st.z3_decided += 1

    def sort_key(r):
        try:
            return (0, int(r.rung))
        except (TypeError, ValueError):
            return (1, r.rung)

    return sorted(groups.values(), key=sort_key)


def total_disagreements(rungs: List[RungStats]) -> int:
    return sum(r.disagree for r in rungs)


_HEADER = "{:>6} {:>6} {:>8} {:>6} {:>9} {:>12} {:>8} {:>8}".format(
    "rung", "total", "z3_dec", "agree", "disagree", "xolver_only", "z3_only", "summit")


def format_ladder(rungs: List[RungStats]) -> str:
    lines = [_HEADER, "-" * len(_HEADER)]
    for r in rungs:
        lines.append("{:>6} {:>6} {:>8} {:>6} {:>9} {:>12} {:>8} {:>8}".format(
            r.rung, r.total, r.z3_decided, r.agree, r.disagree,
            r.xolver_only, r.z3_only, r.both_unknown))
    nd = total_disagreements(rungs)
    lines.append("-" * len(_HEADER))
    lines.append("(summit column = both-unknown: beyond every oracle — inherits "
                 "soundness from the agreeing rungs below)")
    if nd > 0:
        lines.append("*** UNSOUND: %d decided-disagreement(s) Xolver-vs-z3 — engine bug ***" % nd)
    else:
        lines.append("OK: 0 decided-disagreements on any z3-decided rung — "
                     "modular engine sound on the ladder; summit inherits.")
    return "\n".join(lines)


def _rung_fn_from_args(args) -> Callable[[CaseResult], Optional[str]]:
    if args.rung_from_const:
        def fn(c):
            try:
                with open(c.path) as f:
                    k = rung_from_constants(f.read())
                return None if k is None else str(k)
            except (OSError, IOError):
                return None
        return fn
    pattern = args.rung_regex
    return lambda c: rung_from_key(c.key, pattern)


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Graded mod-2^k Xolver-vs-z3 agreement ladder (NIA-modular soundness).")
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--run-dir", help="run dir (run with --compare-with z3)")
    src.add_argument("--stats", help="a single statistics.json")
    p.add_argument("--rung-regex", default=DEFAULT_RUNG_REGEX,
                   help="regex with a capture group for the bit-width in the key")
    p.add_argument("--rung-from-const", action="store_true",
                   help="instead, derive the rung from the largest 2^k constant in each .smt2")
    args = p.parse_args(argv)

    cases = load_statistics_json(args.stats) if args.stats else load_run_dir(args.run_dir)
    rungs = ladder_report(cases, _rung_fn_from_args(args))
    print(format_ladder(rungs))
    return 2 if total_disagreements(rungs) > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
