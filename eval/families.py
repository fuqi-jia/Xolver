"""eval.families — family-level train/val split for autotuning.

SMT-COMP selects benchmarks by family (top dir = submitter/source) and
guarantees new-family coverage, so the autotuner must train on some families
and validate on families it never saw — otherwise a "val gain" is just overfit
to one submitter's encoding quirks. This module keeps each family wholly in one
side of the split. Deterministic per (logic, seed).

Python 3.7+ / stdlib only.
"""
import random
from typing import Dict, List, Set, Tuple

from eval.model import CaseResult


def families_by_logic(cases: List[CaseResult]) -> Dict[str, Set[str]]:
    """Distinct families present per logic."""
    out: Dict[str, Set[str]] = {}
    for c in cases:
        out.setdefault(c.logic, set()).add(c.family)
    return out


def val_family_assignment(cases: List[CaseResult], val_fraction: float = 0.3,
                          seed: int = 0) -> Set[Tuple[str, str]]:
    """The set of (logic, family) pairs assigned to the validation side.

    Per logic: sort families (stable), seeded-shuffle, take round(n*frac) of
    them — clamped to [1, n-1] so both sides are non-empty. A logic with a
    single family can't yield an unseen-family val set, so it contributes none
    (all train).
    """
    by_logic = families_by_logic(cases)
    val: Set[Tuple[str, str]] = set()
    for logic in sorted(by_logic):
        fams = sorted(by_logic[logic])
        n = len(fams)
        if n < 2:
            continue
        rng = random.Random("%s:%d" % (logic, seed))
        rng.shuffle(fams)
        n_val = int(round(n * val_fraction))
        n_val = max(1, min(n_val, n - 1))
        for f in fams[:n_val]:
            val.add((logic, f))
    return val


def split_families(cases: List[CaseResult], val_fraction: float = 0.3,
                   seed: int = 0) -> Tuple[List[CaseResult], List[CaseResult]]:
    """Partition cases into (train, val) at family granularity."""
    val_pairs = val_family_assignment(cases, val_fraction, seed)
    train: List[CaseResult] = []
    val: List[CaseResult] = []
    for c in cases:
        if (c.logic, c.family) in val_pairs:
            val.append(c)
        else:
            train.append(c)
    return train, val
