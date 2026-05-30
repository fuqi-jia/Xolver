"""eval.diffmodel — load + classify results/diff_*.csv.

diff_*.csv schema: key,baseline,candidate,oracle  (key = <LOGIC>/<family>/<file>.smt2;
verdicts sat|unsat|unknown|timeout|error). baseline = floors-only Xolver,
candidate = floors+flag Xolver, oracle = z3@1200 (3-oracle join in eval.oracle3).

解错 (jie-cuo = "wrong answer") = candidate decided AND oracle decided AND they
disagree. It is the paramount gate: any 解错 blocks a flag from going default-ON.

Python 3.6+ / stdlib only.
"""
import csv
import glob
import os
import re
import sys
from typing import Dict, List, Optional, Tuple, Union

from eval._compat import dataclass
from eval.model import family_of

DECIDED = ("sat", "unsat")


@dataclass
class DiffRow:
    key: str
    logic: str
    family: str
    baseline: str
    candidate: str
    oracle: str


def _logic_of(key: str) -> str:
    return key.split("/", 1)[0] if "/" in key else key


def _expand(paths: Union[str, List[str]]) -> List[str]:
    if isinstance(paths, str):
        paths = [paths]
    files: List[str] = []
    for p in paths:
        if os.path.isdir(p):
            files.extend(sorted(glob.glob(os.path.join(p, "diff_*.csv"))))
        elif any(c in p for c in "*?["):
            files.extend(sorted(glob.glob(p)))
        else:
            files.append(p)
    return files


# Verdict priority for dedup-merge: a DECIDED verdict beats timeout / unknown /
# error / missing. When two runs of the same key disagree (e.g. one node finished,
# the other timed out — common when master's node-slicing accidentally runs the
# full corpus on multiple nodes), we want the BEST result (the one a single
# competition run would have credited).
_VERDICT_PRIORITY = {"sat": 4, "unsat": 4, "unknown": 2, "timeout": 1,
                     "error": 0, "missing": 0}


def _better(a: str, b: str) -> str:
    """Pick the higher-priority verdict; ties broken by keeping `a` (stable)."""
    return a if _VERDICT_PRIORITY.get(a, 0) >= _VERDICT_PRIORITY.get(b, 0) else b


def _merge_rows(a: DiffRow, b: DiffRow) -> DiffRow:
    """Merge two rows for the same key: best-of-both for each verdict column."""
    return DiffRow(
        key=a.key, logic=a.logic, family=a.family,
        baseline=_better(a.baseline, b.baseline),
        candidate=_better(a.candidate, b.candidate),
        oracle=_better(a.oracle, b.oracle),
    )


def load_diff(paths: Union[str, List[str]],
              warn: Optional[bool] = True) -> List[DiffRow]:
    """Load + merge diff_*.csv (file, list, glob, or dir of diff_*.csv).

    Dedup by key with best-of-both-runs merge: when two diff files contain the
    same key (e.g. a node-slicing bug ran the full corpus on multiple nodes),
    we pick the higher-priority verdict per column (decided > timeout > unknown
    > error). This makes the pipeline robust against duplicate runs and credits
    the better measurement — exactly what a single competition run would do.

    If duplicates are detected and warn=True, a one-line note is emitted to
    stderr so the data-quality issue is visible (counts of dup keys + diverging
    rows) without breaking the pipeline.
    """
    by_key: Dict[str, DiffRow] = {}
    dup_keys = 0
    diverging = 0
    for path in _expand(paths):
        with open(path, newline="") as f:
            for rec in csv.reader(f):
                if len(rec) < 4:
                    continue
                key = rec[0].strip()
                if not key or key == "key":
                    continue
                logic = _logic_of(key)
                new = DiffRow(key=key, logic=logic, family=family_of(key, logic),
                              baseline=rec[1].strip(), candidate=rec[2].strip(),
                              oracle=rec[3].strip())
                old = by_key.get(key)
                if old is None:
                    by_key[key] = new
                else:
                    dup_keys += 1
                    if (old.baseline, old.candidate, old.oracle) \
                            != (new.baseline, new.candidate, new.oracle):
                        diverging += 1
                    by_key[key] = _merge_rows(old, new)
    if warn and dup_keys:
        sys.stderr.write(
            "[load_diff] dedup: %d duplicate keys merged (%d had diverging "
            "verdicts; best-of-both-runs merge applied)\n" % (dup_keys, diverging))
    return list(by_key.values())


def is_decided(v: str) -> bool:
    return v in DECIDED


def is_jiecuo(r: DiffRow) -> bool:
    """解错: candidate and oracle both decided and disagree (candidate is wrong)."""
    return is_decided(r.candidate) and is_decided(r.oracle) and r.candidate != r.oracle


def jiecuo_flip(r: DiffRow) -> str:
    """Flip direction of a 解错: oracle(truth) -> candidate(wrong answer)."""
    return "%s->%s" % (r.oracle, r.candidate)


def correct_solved(verdict: str, oracle: str) -> bool:
    """Decided AND not contradicting a decided oracle. (Decided-but-oracle-blind
    counts as solved — confirmation is the oracle-blind audit's job, not here.)"""
    return is_decided(verdict) and not (is_decided(oracle) and verdict != oracle)


_CAT_RE = re.compile(r'_([A-Za-z]+(?:_[A-Za-z]+)*)_\d+\.smt2$')


def name_category(key: str) -> str:
    """The finer cluster label within a family: the benchmark-name category token
    (e.g. edge_closing, terminationG, safety) when present, else the immediate
    parent subdir (e.g. SAT14, CInteger). '?' if neither."""
    parts = key.split("/")
    m = _CAT_RE.search(parts[-1])
    if m:
        return m.group(1)
    if len(parts) >= 3:
        return parts[-2]
    return "?"
