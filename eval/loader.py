"""eval.loader — read run_benchmark.py outputs into CaseResult lists.

File-based by design (the master's "对拍 from files, run only the misses
locally" workflow): nothing here re-runs the solver. Reads the per-logic
`statistics.json` that run_benchmark.py writes to RUN_DIR/<LOGIC>/.

Python 3.7+ / stdlib only.
"""
import glob
import json
import os
from typing import List

from eval.model import CaseResult, family_of, normalize_key


def _row_to_case(row: dict, logic: str) -> CaseResult:
    path = row.get("file", "")
    key = normalize_key(path, logic)
    if key is None:
        # Path not under this logic (e.g. odd scramble temp path) — keep the raw
        # path as key so the row is still counted, but it won't join family/BLAN.
        key = path
        family = "unknown"
    else:
        family = family_of(key, logic)
    return CaseResult(
        key=key,
        logic=logic,
        family=family,
        path=path,
        result=row.get("xolver_result", "unknown"),
        time=float(row.get("xolver_time", 0.0) or 0.0),
        oracle_result=row.get("compare_result", "skip"),
        oracle_time=float(row.get("compare_time", 0.0) or 0.0),
        match=row.get("match", "SKIP"),
    )


def load_statistics_json(path: str) -> List[CaseResult]:
    """Load one logic's statistics.json into a list of CaseResult."""
    with open(path) as f:
        data = json.load(f)
    meta = data.get("meta", {})
    stats = data.get("statistics", {})
    logic = meta.get("logic") or stats.get("logic") or ""
    return [_row_to_case(r, logic) for r in data.get("results", [])]


def load_run_dir(run_dir: str) -> List[CaseResult]:
    """Load every per-logic statistics.json under a run directory.

    run_benchmark.py writes RUN_DIR/<LOGIC>/statistics.json (one subdir per
    logic, always — even single-logic runs). A statistics.json sitting directly
    in run_dir is also picked up for flexibility.
    """
    out: List[CaseResult] = []
    direct = os.path.join(run_dir, "statistics.json")
    if os.path.isfile(direct):
        out.extend(load_statistics_json(direct))
    for sj in sorted(glob.glob(os.path.join(run_dir, "*", "statistics.json"))):
        out.extend(load_statistics_json(sj))
    return out
