# Task K — NRA-side B-v3 bilinear-substitution audit

Master's priority-3 dispatch. Profile 5 `nra_054`-class cases; if NRA-side
CAC monomial substitution exposes redundant `x*y` bilinear work beyond what
the NIA agent's B-v2 already handles, ship a NRA-specific B-v3 lever.

**Conclusion**: no NRA-specific bilinear surface to exploit. The bilinear path
flows entirely through cached layers post-Task-J. **Deferred — do not ship**.

---

## Methodology

WSL-safe single-case profile of representative NRA workloads under combined
levers + `XOLVER_NRA_KERNEL_STATS=1` + `XOLVER_NRA_CAC_INSTR=1`.

| Case | Size | Cells | Leaves | terms hits / total | tpi hits / total |
|---|---|---|---|---|---|
| `nra_022` algebraic_root | small | – | – | 180 / 185 = **97.30%** | 96 / 99 = **96.97%** |
| `nra_054` metitarski_atan_approx | small | 4 | 4 | 586 / 670 = **87.46%** | 88 / 163 = **53.99%** |
| `nra_140` root_2 | small | 5 | 3 | 44 / 46 = **95.65%** | 23 / 24 = **95.83%** |
| `sqrt-problem-Melquiond2-chunk-0010` | **27-line, 111 cells, 3581 pool** | 111 | 97 | **80171 / 82178 = 97.56%** | **21808 / 22486 = 96.98%** |

The Melquiond2 case is the load-bearing data point: 3581 unique polynomials
across 111 CAC cells, 97 leaves, with 80k+ `terms()` calls.

---

## Why a B-v3 NRA lever would be redundant

The bilinear `x*y` substitution path in NRA flows through three already-cached
layers, in this order:

1. **`mul(x, y) → PolyId`** — `LibPolyKernel::mul` returns a hash-cons hit
   when the operand pair has been seen before, via `binOpCache_` (S1, commit
   `547ea11`). Canonicalized `(min, max)` ordering means `mul(x, y)` and
   `mul(y, x)` collide.
2. **`toPrimitiveInteger(rp) → (PolyId, scale)`** — S2 (commit `155d407`)
   memoizes by `RationalPolynomial` fingerprint at the driver entry. On the
   Melquiond2 case this fires **21808 hits / 22486 calls (96.98 %)**.
3. **`terms(p) → vector<MonomialTerm>`** — S1c (commit `4950213`, Task J)
   memoizes the decomposition view. On Melquiond2 this fires **80171 hits /
   82178 calls (97.56 %)**.

Any bilinear `x*y` term appearing in a fresh atom is cached at all three
layers on its second appearance. The CAC projection's monomial-substitution
hot path reads through this stack — there is no separate uncached entry
point. An NRA-specific B-v3 lever would have to either (a) sit *above* the
kernel layer and avoid the calls entirely (a much bigger structural change,
not a "30-line patch") or (b) cache something *not in the stack*, of which
no current profile shows a candidate.

Contrast: NIA's B-v2 bilinear substitution targets the substitution
mechanism inside the NIA reasoner pipeline, which has a different surface
(domain-store / RRT / modular reasoner combination) and a different
cacheable boundary. The same lever does not translate to NRA-CAC.

---

## Empirical bilinear-pattern signal

The binary-op hit rate on the Melquiond2 case is **29.89 %** (1065 misses on
1519 total), which is the lowest of the four sample cases. This represents
genuine unique-input work — many distinct polynomial multiplications in the
projection. But every output of those multiplications flows into a cached
downstream view:

```
mul(x, y) → PolyId p1        # S1: 30% hit rate (unique inputs)
  ↓
toPrimitiveInteger(rp(p1)) → (p1', s)
                              # S2: 97% hit rate (RP fingerprint)
  ↓
terms(p1')                    # S1c: 97% hit rate (PolyId-keyed)
  ↓
degree(p1', var)              # uses cached terms() for non-main-var
```

The 70 % binOp miss rate is **structural** (genuine new combinations being
formed), not redundant — those new poly IDs only get computed once and
their derivatives (tpi conversion, decomposition) are then heavily reused.

---

## Recommendation

* **Do not ship a B-v3 NRA lever.** The hot path is already three-layer
  cached. A new lever would be (a) redundant under measurement or (b) a
  large structural refactor outside the Stage 5 scope.
* **Re-evaluate post-server-batch.** If a new server-side perf signal
  surfaces a specific bilinear pattern not captured by S1+S2+S1c
  (eg `pseudoRemainder` redundancy under stable variable order), reactivate
  as a Phase E sprint.
* **NIA agent's B-v2 remains the right place** for NIA-engine bilinear work.

---

*Binary: `agent/nra-2` @ `3c97196` (15 NRA-lane commits this session, side-built
in `build_taskj/`).*
*Profile env: `XOLVER_NRA_KERNEL_STATS=1` + `XOLVER_NRA_CAC_INSTR=1`.*
