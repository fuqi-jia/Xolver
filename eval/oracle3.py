"""eval.oracle3 — 3-oracle (z3 ∪ cvc5 ∪ BLAN) join + oracle-blind tagging.

A case is confirmed X if ANY oracle says X (sat/unsat); oracle-blind if all
three are undecided (timeout/unknown/error/missing). Folding BLAN + cvc5 into the
diff's z3 oracle strengthens the 解错 gate — e.g. BLAN catches a false-UNSAT z3
timed out on. The oracle-blind set with a DECIDED candidate is exactly NIA's
modular-UNSAT surpass class: it routes to the independent-cert audit, NOT the
oracle gate (no oracle can confirm it).

Joins cached CSVs only (key,verdict,seconds) — never re-runs a solver.
Python 3.6+ / stdlib only.
"""
from typing import Dict, List, Optional

from eval.diffmodel import DECIDED, DiffRow, is_decided
from eval.oracle import BlanRow, load_blan_csv


def load_verdict_cache(paths):
    """key -> BlanRow from a key,verdict,seconds cache (z3_*/cvc5_*/blan_*.csv)."""
    return load_blan_csv(paths)


def merge_verdict(verdicts: List[str]) -> str:
    """sat/unsat if any oracle decided it (and they agree); 'conflict' if decided
    oracles disagree; 'blind' if none decided."""
    decided = [v for v in verdicts if v in DECIDED]
    if not decided:
        return "blind"
    return decided[0] if len(set(decided)) == 1 else "conflict"


def build_oracle3(z3_map: Optional[Dict[str, BlanRow]] = None,
                  cvc5_map: Optional[Dict[str, BlanRow]] = None,
                  blan_map: Optional[Dict[str, BlanRow]] = None) -> Dict[str, str]:
    """key -> merged verdict (sat/unsat/conflict/blind) over the cache maps."""
    maps = [m for m in (z3_map, cvc5_map, blan_map) if m]
    keys = set()
    for m in maps:
        keys |= set(m)
    return {k: merge_verdict([m[k].verdict for m in maps if k in m]) for k in keys}


def _effective_oracle(diff_oracle: str, o3_val: str) -> str:
    """Fold the diff's z3 oracle with the cache-merge: decided wins; disagreeing
    decided -> conflict; otherwise keep the diff oracle (likely undecided)."""
    decided = [v for v in (diff_oracle, o3_val) if v in DECIDED]
    if not decided:
        return diff_oracle
    return decided[0] if len(set(decided)) == 1 else "conflict"


def rescore_with_oracle3(rows: List[DiffRow], oracle3: Dict[str, str]) -> List[DiffRow]:
    """Return rows with .oracle replaced by the 3-oracle effective verdict, so the
    scorer's 解错 check sees the strongest available oracle."""
    out = []
    for r in rows:
        new_oracle = _effective_oracle(r.oracle, oracle3.get(r.key, "blind"))
        out.append(DiffRow(r.key, r.logic, r.family, r.baseline, r.candidate, new_oracle))
    return out


def oracle_blind_keys(rows: List[DiffRow], oracle3: Dict[str, str]) -> List[str]:
    """Keys where the candidate is DECIDED but no oracle can confirm it — the
    cert-audit set (NIA modular-UNSAT surpass class)."""
    out = []
    for r in rows:
        eff = _effective_oracle(r.oracle, oracle3.get(r.key, "blind"))
        if is_decided(r.candidate) and not is_decided(eff):
            out.append(r.key)
    return out
