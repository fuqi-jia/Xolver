"""eval.model — shared path/key normalization for the eval harness.

Python 3.7+ / stdlib only (the test server may lack 3.12; see memory
feedback_python_version_conservative).
"""
from dataclasses import dataclass
from typing import Optional


@dataclass
class CaseResult:
    """One benchmark case's outcome, normalized for the eval harness.

    `result`/`oracle_result` are verdict strings: sat | unsat | unknown |
    timeout | error | killed | skip. `oracle_result == "skip"` means no oracle
    was run for this case. `match` is run_benchmark.py's classification
    (MATCH | DIFF | MISMATCH | SKIP) against the live z3/cvc5 oracle.
    """
    key: str
    logic: str
    family: str
    path: str
    result: str
    time: float
    oracle_result: str = "skip"
    oracle_time: float = 0.0
    match: str = "SKIP"


def normalize_key(path: str, logic: str) -> Optional[str]:
    """Normalize a solver-result file path to the canonical join key
    "<LOGIC>/<family>/.../<file>.smt2".

    Mirrors BLAN's shell keying `key="QF_NIA/${f##*QF_NIA/}"`: strip the longest
    prefix ending in "<LOGIC>/", i.e. key off the LAST occurrence of the marker.
    This is what lets a Xolver absolute path, a mirror dir, or a scramble temp
    path all join against the same BLAN CSV row. Returns None when the marker is
    absent (the path is not under this logic).
    """
    marker = logic + "/"
    idx = path.rfind(marker)
    if idx == -1:
        return None
    return marker + path[idx + len(marker):]


def family_of(key: str, logic: str) -> str:
    """The SMT-LIB family of a normalized key = the first path component under
    the logic dir.

    SMT-COMP groups and selects benchmarks by this top-level dir (submitter /
    application source), so the family-split must use it — not the leaf dir. A
    file directly under the logic dir has no family -> "root" (matches
    run_benchmark.py's category sentinel).
    """
    prefix = logic + "/"
    rest = key[len(prefix):] if key.startswith(prefix) else key
    parts = rest.split("/")
    if len(parts) <= 1:
        return "root"
    return parts[0]
