# Task NRA-HYB — Simplex+CAC Hybrid: Partition Analysis (Step 1)

Master's priority-2 dispatch (NEW 8h queue, 2026-06-02): real-interval
NRA hybrid following the QF_NIA HYB partition pattern. Real intervals
are uncountable so direct enumeration doesn't apply, but **partition by
constraint role** does — linear constraints to simplex, nonlinear to
CAC.

This document delivers **Step 1**: partition statistics infrastructure
+ empirical justification for the full coordinated solver.

---

## Architectural rationale (master's idea)

Real-interval NRA is undecidable to enumerate exhaustively, but the
*structural partition* is computable:

* **Linear constraints** (L): every monomial has total degree ≤ 1.
  Simplex (LRA infrastructure, e.g. `agent/lia-lra-deep`'s
  incremental-β) solves these in polynomial time.
* **Nonlinear constraints** (N): at least one monomial of degree ≥ 2.
  CAC is required for exact reasoning.

The hybrid scheme:

```
1. Simplex on L (with V_L ∪ V_M) → rational point r
2. CAC verifies N on V_N with V_M fixed at r
3. If CAC SAT      → validate full atom set (invariant 1)
4. If CAC infeas   → CAC generates a lemma over V_M
                       linear → adds to L
                       nonlinear → tightens N
5. Goto 1, until budget exhausts or convergence
```

Soundness: the final SAT must validate **every** original atom; CAC
provides sound UNSAT lemmas; iteration is monotone (lemmas only tighten).

---

## Step 1 deliverable: partition stats

New translation unit `src/theory/arith/nra/search/HybridPartitionStats.{h,cpp}`:

* **`computePartition(polys, kernel)` → `HybridPartitionReport`**:
  pure function, classifies each PolyId as linear / nonlinear via
  cached `kernel.terms(p)` (S1c), accumulates `V_L`, `V_N`, `V_M`
  variable sets.
* **`maybeDumpPartitionReport(report)`**: emits to stderr under
  `XOLVER_NRA_HYB_PARTITION_STATS=1`. Report-only; no solver state
  mutation.

Hooked from `NraSolver::check()` at the first entry per
`presolveConstraints_` size; one-shot per solve cycle.

---

## Empirical partition pattern (5 NRA stress cases)

Using `XOLVER_NRA_HYB_PARTITION_STATS=1` after the Task Q
post-promotion binary (`agent/nra-2 @ c5caa1b`):

| Case | constraints L / total | linear_frac | V_L / V_N / V_M | mixed_frac |
|---|---|---|---|---|
| `nra_022_sat_algebraic_root` | 1 / 2 | **50.0 %** | 0 / 0 / 1 | 100 % |
| `nra_054_sat_metitarski_atan_approx` | 3 / 4 | **75.0 %** | 0 / 0 / 2 | 100 % |
| `nra_140_sat_root_2` | 0 / 1 | 0.0 % (pure NRA) | 0 / 1 / 0 | 0 % |
| `nra_150_sat_melquiond2_hashcons_stress` | 5 / 6 | **83.3 %** | 0 / 0 / 3 | 100 % |
| `nra_145_sat_polypaver_exp3d_ls_recovered` | 7 / 8 | **87.5 %** | 0 / 0 / 3 | 100 % |

## Key findings

### Finding 1 — Linear constraints dominate the active set

4 of 5 cases have **50-87.5 % linear constraint fraction**. CAC is
currently solving these linear constraints with its (cylindrical
algebraic) projection machinery, which is **algorithmically expensive
for linear inputs**. Simplex solves them in O(n³) per pivot.

The 1 pure-nonlinear case (`nra_140`) is the calibration baseline —
hybrid degenerates to "use CAC only", no benefit but no harm.

### Finding 2 — All variables are mixed (V_M)

In every case where both L and N constraints exist, **every variable
appears in both classes** — V_L and V_N are empty, V_M holds all
variables. This is the expected pattern: NRA test cases typically
share variables across all constraints.

The hybrid algorithm's value is therefore NOT cleanly
"linear-variable simplex → nonlinear-variable CAC". It's:
**partition by constraint, assign all V_M via simplex, then CAC checks
the small nonlinear residual with V_M fixed.**

This is more nuanced than the original sketch but still tractable.

### Finding 3 — Polypaver LS-recovery case has 87.5 % linear

The polypaver chunk-0023 case (one of the 9 LS-recovered cases from
Task I) has **only 1 nonlinear constraint out of 8**. Today this case
takes 30 s+ under arm_off but solves in 0.1 s under arm_lscd. A
simplex+CAC hybrid would skip even the LS pre-pass: simplex would find
a candidate r in microseconds, CAC would verify 1 nonlinear constraint
with V_M fixed in milliseconds, and final validation closes the SAT.

This is the design proof of concept for the hybrid value class.

---

## Step 2-N: Future work

This patch lays the foundation. The full hybrid solver requires:

* **Step 2**: Wire LRA `GeneralSimplex` to consume L constraints from
  the partition. Reuse `agent/lia-lra-deep`'s incremental-β.
* **Step 3**: Bridge `SingleCellProjection` (CAC) to consume V_M
  rational assignments as the "fixed" frame for V_N evaluation.
* **Step 4**: Coordination loop with lemma extraction
  (linear / nonlinear) and reinsertion into L / N.
* **Step 5**: SAT validation via existing
  `realDivPurifySatFloor` (invariant 1).
* **Step 6**: Flag `XOLVER_NRA_HYB_SIMPLEX_CAC` gating; default-OFF
  during development.

Each step is a 4-step audit per `CAMPAIGN-RULES-hash-cons-audit.md`
methodology (skill imports + soundness gate).

---

## Soundness gate (this Step 1)

* **0 functional change**: `HybridPartitionStats` is pure
  measurement, no state mutation.
* **0 unsound**: NRA reg 151/151 with stats flag both off and on.
* **0 env-string leakage**: `XOLVER_NRA_HYB_PARTITION_STATS` is a
  stats-only diagnostic env var (like `XOLVER_NRA_KERNEL_STATS`),
  acceptable to ship per the flag matrix.

---

*Binary: `agent/nra-2` @ `c5caa1b` + this patch.*
*WSL-safe protocol observed (single-process per case, ulimit-wrapped,
timeout 5 s).*
