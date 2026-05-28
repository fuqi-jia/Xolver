"""eval.flags — the XOLVER_* strategy space for the offline autotuner.

The strategy space is OUR env flags (not Z3 tactics). Names verified against the
solver's `getenv("XOLVER_*")` calls in src/, so the autotuner never emits a
no-op flag. Two disjoint sets:

  SOUNDNESS_FLOORS  — pinned ON in EVERY candidate. The search only toggles
                      OPTIMIZATION_FLAGS, so it is structurally incapable of
                      producing an unsound (floor-off) config.
  OPTIMIZATION_FLAGS — boolean completeness/perf levers the autotuner explores.

Numeric/diag/dump/budget envs (e.g. *_MS, *_DIAG, *_CAP, *_MAXBITS) and disable
flags (*_NO_*) are intentionally excluded — they are not 0/1 levers.

Python 3.7+ / stdlib only.
"""
from typing import Dict, List

# Pinned ON in every candidate (the soundness floors named in the Agent E charter).
SOUNDNESS_FLOORS: List[str] = [
    "XOLVER_PP_STRICT_VALIDATION",
    "XOLVER_PP_VALIDATE_NONLINEAR_SAT",
    "XOLVER_SAT_DEFER_EARLY_CONFLICT",
    "XOLVER_COMB_SAT_FLOOR",
    "XOLVER_NRA_UNSAT_CERT",
]

# Boolean optimization/completeness toggles (the --allon opt set + the two
# default-OFF NIA gates + the validator memo perf flag). NRA hybrid/preelim/
# linearize are candidates here precisely so the autotuner re-runs the broad
# differential on them (a flag that adds any `wrong` is rejected in combine()).
OPTIMIZATION_FLAGS: List[str] = [
    # combination
    "XOLVER_COMB_CAREGRAPH", "XOLVER_COMB_MODEL_BASED",
    "XOLVER_COMB_SCALAR_BACKFILL", "XOLVER_COMB_UFARG_ARRANGE",
    # LIA / LRA
    "XOLVER_LIA_CUTS", "XOLVER_LIA_REPAIR",
    "XOLVER_LRA_BOUND_AXIOMS", "XOLVER_LRA_PIVOT_HEUR", "XOLVER_LRA_PROP",
    # NIA
    "XOLVER_NIA_REFUTE", "XOLVER_NIA_GCD", "XOLVER_NIA_ICP",
    "XOLVER_NIA_CDCAC", "XOLVER_NIA_BV_CASCADE",
    "XOLVER_NIA_DIVISOR_CAP", "XOLVER_NIA_UNIVARIATE_FULL",
    # NRA (hybrid/preelim/linearize gated by the wrong-count differential)
    "XOLVER_NRA_LAZARD_LIFT", "XOLVER_NRA_LIBPOLY_PSC",
    "XOLVER_NRA_VARORDER", "XOLVER_NRA_VARORDER_SIMPLEX",
    "XOLVER_NRA_HYBRID", "XOLVER_NRA_PREELIM", "XOLVER_NRA_LINEARIZE",
    # preprocessing / SAT / strategy (universal)
    "XOLVER_PP_REWRITE", "XOLVER_PP_SOLVE_EQS", "XOLVER_PP_PG_CNF",
    "XOLVER_PP_LET_ELIM", "XOLVER_PP_VALIDATOR_MEMO",
    "XOLVER_SAT_LEMMA_MGMT", "XOLVER_SAT_MIN", "XOLVER_STRAT_PRESETS",
    # UF
    "XOLVER_UF_DISEQ_WATCH", "XOLVER_UF_FAST_CC",
]

_UNIVERSAL = [
    "XOLVER_PP_REWRITE", "XOLVER_PP_SOLVE_EQS", "XOLVER_PP_PG_CNF",
    "XOLVER_PP_LET_ELIM", "XOLVER_PP_VALIDATOR_MEMO",
    "XOLVER_SAT_LEMMA_MGMT", "XOLVER_SAT_MIN", "XOLVER_STRAT_PRESETS",
]


def flags_for_logic(logic: str) -> List[str]:
    """The optimization flags plausibly relevant to a logic (stage-1 scoping).

    Imperfect by design — extra flags just get measured and discarded in
    combine(); missing a flag only narrows the search. Universal pp/sat/strat
    flags always apply.
    """
    name = logic.upper()
    sel = set(_UNIVERSAL)

    def add_prefix(prefix):
        sel.update(f for f in OPTIMIZATION_FLAGS if f.startswith(prefix))

    has_nia = "NIA" in name or "NIRA" in name
    has_nra = "NRA" in name or "NIRA" in name
    has_lia = "LIA" in name or "LIRA" in name or "IDL" in name
    has_lra = "LRA" in name or "LIRA" in name or "RDL" in name
    is_comb = ("UF" in name) or name.startswith("QF_A") or "AUF" in name or "DT" in name

    if has_nia:
        add_prefix("XOLVER_NIA_")
    if has_nra:
        add_prefix("XOLVER_NRA_")
    if has_lia:
        add_prefix("XOLVER_LIA_")
    if has_lra:
        add_prefix("XOLVER_LRA_")
    if is_comb:
        add_prefix("XOLVER_COMB_")
        add_prefix("XOLVER_UF_")
    return sorted(sel & set(OPTIMIZATION_FLAGS))


# Precomputed for the competition-relevant logics.
_LOGICS = [
    "QF_NIA", "QF_NRA", "QF_NIRA", "QF_LIA", "QF_LRA", "QF_LIRA",
    "QF_IDL", "QF_RDL", "QF_UF", "QF_UFLRA", "QF_UFLIA", "QF_UFNIA",
    "QF_UFNRA", "QF_ANIA", "QF_AUFNIA", "QF_UFDTNIA",
    "QF_AX", "QF_ALIA", "QF_ALRA", "QF_AUFLIA", "QF_AUFLRA",
]
LOGIC_FLAGS: Dict[str, List[str]] = {lg: flags_for_logic(lg) for lg in _LOGICS}


def candidate_env(selected_flags: List[str]) -> Dict[str, str]:
    """Build the env for one candidate config: all soundness floors ON, plus the
    selected optimization flags ON. Floors are always present and cannot be
    dropped by the selection."""
    env: Dict[str, str] = {floor: "1" for floor in SOUNDNESS_FLOORS}
    for f in selected_flags:
        env[f] = "1"
    return env
