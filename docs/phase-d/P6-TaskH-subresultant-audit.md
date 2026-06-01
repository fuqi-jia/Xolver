# Task H — subResultant chain hash-cons audit

Master's priority-4 dispatch: audit subResultant + neighboring projection ops
for missing hash-cons coverage.

## Findings

### 1. `principalSubresultantCoefficients` (`SubresultantChain.cpp:111`)

**Status**: cache exists, **default-OFF**.

```cpp
bool srCacheEnabled() {
    static const bool kEnabled = [] {
        const char* e = std::getenv("XOLVER_NRA_CAC_SR_CACHE");
        return e && *e && *e != '0';
    }();
    return kEnabled;
}
thread_local std::unordered_map<std::string, PscChainResult> g_pscCache;
```

- Sound by construction: PSC is a pure function of (p, q, v, maxMatrixDim, kernel-flag, forcePsc, libpolyPscEnabled). Same canonical inputs → same `PscChainResult`. Comment at lines 24-27 confirms.
- Scope: thread-local, cleared via `clearPscChainCache()` from CacEngine per solve.
- Key encoding: string `polyKey(p) ## polyKey(q) # v # maxMatrixDim # forcePsc # K|N # L|D`. Same `polyKey` pattern as `unitKey` in `SingleCellProjection.cpp` (a potential later cross-cutting target for S3 integer-fingerprint replacement).

**Why it's OFF**: source comment warns the string-key build cost may exceed the saved determinant work on small polys. Risk is performance, not correctness.

### 2. `discriminant` / `resultant`

Computed via `principalSubresultantCoefficients` (top-PSC for resultant, PSC of (f, f') for discriminant). **Both benefit transitively** once g_pscCache is enabled.

### 3. `pseudoRemainder` / `pseudoRemainderWithScale`

Not cached. **Deferred** in S1b for soundness reasons:

> libpoly's `prem` uses each polynomial's `main_variable`, which `pscChain` transiently mutates. Same `(p, divisor)` could yield different remainders depending on installed variable order at first call → caching could silently bind to the wrong-order result.

This deferral still stands. Safe addition would need to key on (p, divisor, current-variable-order-state) — non-trivial.

### 4. Lazard projection ops (LazardProjectionClosure / LazardProjectionOperator / ProjectionClosure / LocalProjection)

These are higher-layer composition wrappers that call PSC + pseudoRemainder internally. **No direct caching needed at this layer** — wins flow up automatically once the underlying primitives are cached.

## Local paired test (PSC cache OFF vs ON)

| Case | OFF verdict / wall | ON verdict / wall |
|---|---|---|
| nra_054 atan | sat / 0.094s | sat / 0.096s |
| nra_140 root_2 | sat / 0.089s | sat / 0.089s |
| nra_022 alg_root | sat / 0.091s | sat / 0.088s |
| nra_065 unsat circles | unsat / 0.085s | unsat / 0.078s |
| nra_129 unsat disks | unsat / 0.083s | unsat / 0.079s |
| nra_141 hycomp ball | unsat / 0.094s | unsat / 0.097s |

**All 6: identical verdicts, 0 unsound, wall-time within noise.**

Local cases too small to demonstrate PSC cache benefit (each case has few PSC calls; setup cost roughly balances). The wins live on larger benchmarks (cas/sqrtmodinv / hycomp / meti-tarski clusters where PSC recurs across cell jumps).

## Full regression with PSC cache enabled

`XOLVER_NRA_CAC_SR_CACHE=1` + full reg:
- QF_NRA: **143/143**, 0 unsound
- QF_NIA: **113/113**, 0 unsound

## Recommendations

1. **No source default flip recommended** — comment in `SubresultantChain.cpp:36-38` documents a potential small-poly net-negative; data-driven decision should come from server batch.
2. **Master action**: add `XOLVER_NRA_CAC_SR_CACHE=1` to CANDFLAGS in `tools/run_differential.sh` for the next 5-min batch. The lever is:
   - locally derisked (143/143 + 113/113, 0 unsound under env-on)
   - sound by construction (PSC pure function, comment-asserted)
   - thread-local scoped per solve (no cross-session leak)
3. **No new patch needed** — the infrastructure is already in source, gated, and well-documented.
4. **No other subresultant op surfaces missing-cache** worth a 30-line patch:
   - PSC: covered (env-gated)
   - discriminant/resultant: transitive via PSC
   - pseudoRemainder: variable-order soundness blocker (deferred)
   - Lazard composition: higher-layer wrappers benefit transitively

## Cross-reference

- Existing kernel-level hash-cons (S1+S1b at commits `547ea11`+`afeda00`): inner libpoly mul/add/gcd/leadingCoefficient/squareFreeFactors
- Driver-level S2 toPrimitiveInteger memo (commit `155d407`): canonical RP fingerprint
- PSC cache (this audit): exists, default-OFF, derisked, ready for CANDFLAGS

The three layers compose: when PSC is asked, internal toPrimitiveInteger calls hit S2; internal kernel ops hit S1+S1b. PSC cache result skips the recomputation entirely.

---

*Branch: `agent/nra-2` @ `e9c323e` + this audit doc.*
