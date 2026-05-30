# QF_UFNIA polyhedral-recovery target (Track C output, post Track A + Track B)

Source: NOTES/oracle_QF_UFNIA_sample.json (200 cases, 30 sampled)
Per-config timeout: 12s

## Track B status — pos_pinbounds + pos_polyhedral now RECOVER

The synthetic LRA cases used to validate Track A's seam (`pos_pinbounds.smt2`,
`pos_polyhedral.smt2`) now return correct `unsat` with
`XOLVER_SIMPLEX_IMPLIED_EQ=1`. The Track B fix in LraSolver's
`interfaceDisequalities_` conflict loop closes the SAT-escape that previously
let SAT satisfy by negating the deduced eq atom (`v10002=F`).

| case | OFF | ON (Track A + B) |
|---|---|---|
| pos_pinbounds | sat | **unsat** (recovered) |
| pos_polyhedral | sat | **unsat** (recovered) |
| neg_free | sat | sat (sound; no false UNSAT) |
| pos_transitive | unsat | unsat (already caught) |

## Detector-capability histogram (30 cases, post Track A + Track B)

| bucket | count | meaning |
|---|---|---|
| already_solves | 14 | baseline returns oracle verdict |
| iface_recovers | 1 | needs XOLVER_NIA_IFACE_LIFECYCLE (AndOrXor_709) |
| uf_model_recovers | 0 | needs +XOLVER_EUF_UF_MODEL |
| track2b_recovers | 0 | needs +XOLVER_SIMPLEX_IMPLIED_EQ |
| unrecovered | 15 | timeout-or-unknown under all three flags |
| wrong | 0 | (critical: 0 sound regression) |

The 0 track2b_recovers on this QF_UFNIA sample is because NiaSolver does NOT
use the LRA-style `assertedVarEqualityReason` / `interfaceEqAuxVars_` pattern
(it manages interfaceDisequalities through its constraint set with
`Relation::Neq` directly). Track B's LRA fix doesn't reach the QF_UFNIA path
without a symmetric extension in NiaSolver.

## Wisa target — STILL false-sat

`xs_10_20`, `xs_15_25` (QF_UFLIA) still return sat (expected unsat) with
all three flags on. LiaSolver has a `tryProvePairEqualityByLpDuality` mirror
of LRA's Track A, AND a Track B diseq-conflict hook, but the hook is
**gated default-OFF** behind `XOLVER_LIA_LP_DUALITY` because firing it
unconditionally regressed `alia_012_sat_selfstore_arith_arrangement` from
sat to unknown — the LIA probe over-fires on the array-axiom-mediated
constraints where the simplex relaxation pins what integer reasoning
correctly leaves free.

## What needs to happen next for Wisa

1. Understand the alia_012 edge: why does the LIA LP-duality probe say
   `(i0 - i1) = 0` is pinned when the formula's models include `i0 != i1`?
   Hypothesis: the simplex doesn't model array equalities (`a = store(a, i, e)`),
   so its polyhedron is broader; the probe might be confused by default
   bounds on free integer vars.
2. Either narrow the LIA probe to non-array-combination contexts, OR
   teach the probe to recognize when array axioms constrain the integers.
3. Then flip `XOLVER_LIA_LP_DUALITY` default-ON and re-mine the QF_UFLIA
   Wisa-class cases.

## Symmetric NiaSolver extension (separate work, NIA's #36)

For QF_UFNIA recovery via Track B-style detection, NiaSolver needs an
analog of `interfaceEqAuxVars_` + a polyhedral diseq-conflict check.
That is a structural NIA change — NIA's lane, coordinated via the
combination seam contract.
