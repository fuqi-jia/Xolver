# P6 — cas / sqrtmodinv cac-deep diagnose

**Status**: read-only diagnosis (build/opt awaits D2 server sweep + master green-light).
**Branch**: `agent/nra-2 @ 3199f1a` (worktree `../zolver-nra`).
**Clusters**: QF_UFNRA `cas` (96% wipeout) + `sqrtmodinv-hoenicke` (86%) ≈ +43 paired.
**Master spec**: nonlinear-real, no mod / no sqrt ops → CAC kernel is real bottleneck, NOT modular reasoning. Hot path identified as `RationalPolynomial::toPrimitiveInteger` + `libpoly mul`.

---

## 1. Call-site inventory (read-only)

`toPrimitiveInteger` is called from **two architecturally distinct layers**:

| Layer | Site | Frequency | Cost class |
|---|---|---|---|
| Init (cold) | `CacEngine.cpp:35` (per constraint, once at solve start) | O(constraints) | amortized — not hot |
| Hot inner | `SingleCellProjection.cpp:234,271,330,421` | per cell visit × per boundary poly × ≥ 2 in step-0/1 | dominant in cas/sqrtmodinv |
| Hot inner | `SubresultantChain.cpp:176,177` (libpoly PSC path) | per (p,q) pair | per projection |
| Hot inner | `Squarefree.cpp:98,99` | per polynomial | per characterization |
| Hot inner | `NraSolver.cpp:1240` | flag-gated | conditional |
| Other | `LibpolyBackend.cpp:570,775`, `PolynomialConverter.cpp:22,57`, `LibPolyKernel.cpp:755` | varies | mostly cold |

**Key observation**: every `Hot inner` site does an *RP → PolyId* conversion. Most consume the PolyId immediately for libpoly operations (`squareFreeFactors`, `vanishesAtPrefix`, `specializeToUnivariate`, `signAt`, `pscChain`). The PolyIds are then thrown away — no caching.

---

## 2. The **double round-trip** in `SingleCellProjection` step 0

`SingleCellProjection.cpp:230-266` does:

```cpp
std::unordered_set<std::string> seenFac;
for (const auto& rp : boundaryPolys) {
    auto norm = rp.toPrimitiveInteger(*kernel);        // [A] RP → PolyId
    if (!norm.ok()) return bail("toPrim");
    if (kernel->isConstant(norm.poly)) continue;
    if (!prefixHasAlgebraic &&
        algebra->vanishesAtPrefix(norm.poly, prefix, var) == VanishResult::Vanishes) {
        reduced.push_back(rp);                          // keep original RP
        continue;
    }
    for (PolyId f : kernel->squareFreeFactors(norm.poly)) {
        if (kernel->isConstant(f)) continue;
        auto frp = RationalPolynomial::fromPolyId(f, *kernel);  // [B] PolyId → RP
        if (!frp) { reduced.push_back(rp); continue; }
        frp->normalize();
        if (seenFac.insert(unitKey(*frp)).second) reduced.push_back(std::move(*frp));
    }
}
// Step 1 immediately AFTER:
for (const auto& rp : reduced) {
    auto norm = rp.toPrimitiveInteger(*kernel);        // [C] RP → PolyId (AGAIN, of the SAME factor)
    ...
}
```

For each boundary poly that produces `k` square-free factors:
- **[A]** 1 RP→PolyId conversion (toPrimitiveInteger: LCM + GCD + divide-and-conquer mul/add)
- **[B]** k PolyId→RP conversions (fromPolyId: iterate terms + addTerm + normalize)
- **[C]** k RP→PolyId conversions (toPrimitiveInteger AGAIN — building the SAME libpoly polynomials)

So for `n` boundary polys averaging `k` factors each, step 0+1 burns **(n + nk) toPrimitiveInteger calls + nk fromPolyId calls** when the underlying libpoly polynomial for each factor was already alive in `f`. The PolyIds in step [B] are simply *forgotten*.

**The dedup `unitKey(*frp)` is the only reason RP form is needed** — for hashing into the `seenFac` set. `kernel.eq(PolyId, PolyId)` would work but is O(libpoly equality), and there's no `PolyId.hash()`. The string-based `unitKey` round-trip is the structural cause.

---

## 3. `LibPolyKernel` add/mul/pow are not hash-consed

`LibPolyKernel.cpp:93-111`:

```cpp
PolyId LibPolyKernel::add(PolyId a, PolyId b) { return alloc(poly::operator+(get(a), get(b))); }
PolyId LibPolyKernel::mul(PolyId a, PolyId b) { return alloc(poly::operator*(get(a), get(b))); }
PolyId LibPolyKernel::pow(PolyId a, uint32_t k) { return alloc(poly::pow(get(a), k)); }
```

Each call returns a **fresh `alloc`** of a new `poly::Polynomial`. No memoization. So the divide-and-conquer build in `toPrimitiveInteger` creates `O(N log N)` intermediate libpoly polynomials per RP→PolyId conversion, and ANY repeat conversion creates a DUPLICATE PolyId for the same value.

`mkVar`/`mkConst` *are* hash-consed (`mkVar` checks `varToPoly_` map). But the binary ops aren't.

---

## 4. Three concrete micro-opt levers

### Lever A: `unitKey(PolyId)` instead of `unitKey(RationalPolynomial)`
**Where**: `SingleCellProjection.cpp:258-264` step 0
**What**: skip the `fromPolyId(f) → RP → normalize → unitKey(RP)` round-trip; compute a canonical fingerprint directly from PolyId via `LibPolyKernel::terms(f)` and serialize the kernel terms (kernel terms are already canonical).
**Win**: eliminate the [B] fromPolyId per factor + keep step-1 [C] from rebuilding.
**Even better**: store `std::pair<PolyId, RationalPolynomial>` in `reduced`, where the RP is the LAZY fallback (only computed by step 1 if a code path actually needs RP form — `lazardResidualRational` is the one that does).
**Risk**: `unitKey` currently includes the leading-coefficient unitization (`p *= 1/lead; normalize()`), which divides through. Doing that on a PolyId means going through rationals anyway. Cheapest sound fingerprint: hash `kernel.terms(f)` raw, accept that proportional polys with different scales hash differently → potentially LESS dedup. Need to measure if extra dedup loss costs the wipeout back.

### Lever B: Hash-cons binary ops in `LibPolyKernel`
**Where**: `LibPolyKernel::add/sub/mul/pow`
**What**: add a small `unordered_map<pair<PolyId,PolyId>, PolyId>` cache keyed by `(opCode, a, b)`. Repeated `toPrimitiveInteger` for the same RP → same final PolyId; repeated factor recomputation → free.
**Win**: makes the double-round-trip cheap retroactively (the SECOND `toPrimitiveInteger` for a factor hits cache at every internal mul step).
**Risk**: cache invalidation. `LibPolyKernel` polys are immutable-once-alloc (libpoly poly handles aren't mutated in place), so cache is sound. Memory: bounded by total alloc count; need eviction strategy under long-running solves.
**Cost**: O(1) hashmap probe per add/mul. Probably positive even without round-trip lever.

### Lever C: Memoize `RationalPolynomial::toPrimitiveInteger` on RP fingerprint
**Where**: new cache in `LibPolyKernel` or `RationalPolynomial`
**What**: hash the RP's `FlatMonomialMap` (already canonical after normalize) and short-circuit if `(rpHash → PolyId)` is cached.
**Win**: skip steps 1-4 of `toPrimitiveInteger` (LCM/GCD/scale/divide-and-conquer) entirely on repeat.
**Risk**: hash collisions need full eq fallback. Cache lifetime tied to PolynomialKernel alloc vector — sound by lifetime if cache lives in kernel.
**Synergy**: covers cases Lever B misses (Lever B helps INTERNAL builds; Lever C helps repeated TOP-LEVEL calls with the same RP).

---

## 5. Recommended ship order (after master green-light)

| Sprint | Lever | Files touched | Risk | Expected delta |
|---|---|---|---|---|
| P6-S1 | **Lever B** (hash-cons add/mul/pow) | `LibPolyKernel.{h,cpp}` only | low — pure additive cache | covers double-round-trip + repeat builds simultaneously |
| P6-S2 | **Lever C** (memoize toPrimitiveInteger by RP fingerprint) | `LibPolyKernel` + small RP hash helper | low — sound by lifetime | extra wins on repeat top-level calls |
| P6-S3 (only if S1+S2 don't close) | **Lever A** (PolyId-keyed dedup) | `SingleCellProjection.cpp` step 0 | medium — touches dedup correctness | structural fix, more invasive |

**Why S1 first**: it's the smallest diff (~30 lines in one file), no correctness reasoning about dedup, and `bool` immediately tests "does the hash-cons close cas/sqrtmodinv?" If yes → ship S1 alone, defer S2/S3. If no → S2 confirms whether the cost is in top-level toPrimitiveInteger setup (LCM/GCD/Item build) vs internal libpoly mul.

---

## 6. Gating plan (WSL-safe)

Once master green-lights P6:

1. **Build**: `cmake --build build -j 2` (NEVER unbounded).
2. **Unit gate**: `( ulimit -v 4000000; timeout 60 ./build/tests/xolver_unit_tests )` — full suite, 0 fail required.
3. **NRA reg gate**: `( ulimit -v 4000000; python3 tools/run_regression.py --root tests/regression --logic QF_NRA --solver build/bin/xolver --timeout 20 -j 2 )` — 143/143 hard gate, 0 unsound.
4. **Sample paired** (≤ 30 cases): pick a small cas + sqrtmodinv subset locally only if available, otherwise defer paired sweep to server.
5. **Server hand-off**: master runs the broad QF_UFNRA paired sweep on cas + sqrtmodinv + the rest of the corpus.

**Never** run unbounded local sweeps. Reference: `docs/WSL-SAFE-PROTOCOL.md`.

---

## 7. Open questions for master

- **Q1**: Lever B cache eviction policy — bounded LRU or grow-forever for the session? Long solves on big polys could grow the cache; the kernel itself already holds every allocated PolyId so a parallel cache table is at most a constant-factor memory hit.
- **Q2**: Lever A correctness: if PolyId-keyed dedup loses some proportional-pair collapses (different unit scales), the cell may get slightly finer boundaries → still sound, but extra projection work. Acceptable trade for the wipeout? Master decision.
- **Q3**: Order vs D2 server result — if D2 server sweep shows cas/sqrtmodinv has a different bottleneck (e.g. real cost lives in `vanishesAtPrefix` or `pscChain`, not RP↔PolyId), reroute P6.

---

*Diagnosis complete. Awaiting D2 server sweep + master green-light to build/ship.*
