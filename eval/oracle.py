"""eval.oracle — the 3rd oracle (BLAN) join + decided-disagreement reports.

z3/cvc5 are the live oracles (run_benchmark.py already classifies xolver-vs-oracle
as MATCH/DIFF/MISMATCH). BLAN is a cached CSV oracle for QF_NIA (a sound
bit-blaster; our bit-blast backend was ported from it, so any BLAN-vs-Xolver
decided disagreement is a real bug). This module joins the cached CSV by the
canonical key and emits two strictly-separated report classes:

  - decided_disagreements: both sides DECIDED (sat/unsat) and differ. SOUNDNESS
    bug — sinks a division. Covers vs-z3/cvc5 (MISMATCH) AND vs-BLAN.
  - blan_debug_targets: BLAN decided, Xolver undecided (unknown/timeout/error).
    A completeness/recovery target (unknown is free, so harmless to score) —
    the "debug locally" list.

BLAN CSV schema (from BLAN/run_blan.sh): header `key,verdict,seconds`,
key = "QF_NIA/<family>/<file>.smt2", verdict in {sat,unsat,unknown,timeout,error}.

Python 3.7+ / stdlib only.
"""
import csv
import glob
import os
from typing import Dict, List, Optional, Union

from eval._compat import dataclass
from eval.model import CaseResult

DECIDED = ("sat", "unsat")


@dataclass
class BlanRow:
    verdict: str
    seconds: float


@dataclass
class Disagreement:
    key: str
    logic: str
    family: str
    xolver_result: str
    oracle: str          # "z3" / "cvc5" / "BLAN"
    oracle_result: str


def _decided(v: str) -> bool:
    return v in DECIDED


def _expand_paths(paths: Union[str, List[str]]) -> List[str]:
    if isinstance(paths, str):
        paths = [paths]
    files: List[str] = []
    for p in paths:
        if os.path.isdir(p):
            files.extend(sorted(glob.glob(os.path.join(p, "blan_*.csv"))))
        elif any(ch in p for ch in "*?["):
            files.extend(sorted(glob.glob(p)))
        else:
            files.append(p)
    return files


def load_blan_csv(paths: Union[str, List[str]]) -> Dict[str, BlanRow]:
    """Load + merge BLAN node CSVs into key -> BlanRow.

    Accepts a file, a list of files, a glob, or a directory (loads blan_*.csv).
    On key overlap across nodes, a decided verdict wins over an undecided one.
    """
    out: Dict[str, BlanRow] = {}
    for path in _expand_paths(paths):
        with open(path, newline="") as f:
            for row in csv.reader(f):
                if len(row) < 2:
                    continue
                key = row[0].strip()
                if not key or key == "key":  # header (also handles concatenated files)
                    continue
                verdict = row[1].strip().lower()
                seconds = 0.0
                if len(row) >= 3 and row[2].strip():
                    try:
                        seconds = float(row[2])
                    except ValueError:
                        seconds = 0.0
                existing = out.get(key)
                if existing is None or (_decided(verdict) and not _decided(existing.verdict)):
                    out[key] = BlanRow(verdict=verdict, seconds=seconds)
    return out


def decided_disagreements(cases: List[CaseResult],
                          blan_map: Optional[Dict[str, BlanRow]] = None,
                          oracle_label: str = "oracle") -> List[Disagreement]:
    """All cases where Xolver and a DECIDED oracle disagree on a DECIDED verdict.

    vs z3/cvc5: reuse run_benchmark's MISMATCH (already "both decided + differ").
    vs BLAN: both Xolver and BLAN decided and differ.
    """
    out: List[Disagreement] = []
    for c in cases:
        if c.match == "MISMATCH":
            out.append(Disagreement(c.key, c.logic, c.family, c.result,
                                    oracle_label, c.oracle_result))
        if blan_map is not None:
            br = blan_map.get(c.key)
            if (br is not None and _decided(c.result) and _decided(br.verdict)
                    and c.result != br.verdict):
                out.append(Disagreement(c.key, c.logic, c.family, c.result,
                                        "BLAN", br.verdict))
    return out


def blan_debug_targets(cases: List[CaseResult],
                       blan_map: Dict[str, BlanRow]) -> List[Disagreement]:
    """Cases BLAN decided but Xolver did not (recovery / debug-locally targets)."""
    out: List[Disagreement] = []
    for c in cases:
        br = blan_map.get(c.key)
        if br is not None and _decided(br.verdict) and not _decided(c.result):
            out.append(Disagreement(c.key, c.logic, c.family, c.result,
                                    "BLAN", br.verdict))
    return out
