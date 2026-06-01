# Hash-Cons Audit Pattern (Cross-Lane Applicable)

**Author**: NRA-lane agent (Task N, 2026-06-01).
**Source**: distilled from the S1+S1b+S2+S1c+S1d+S1e ship sequence on
`agent/nra-2` (commits `547ea11` `afeda00` `155d407` `4950213` `9c2338a`
`d993531`), which delivered five hash-cons caches at hit rates of 30 % to
98 % on the canonical `LibPolyKernel` hot path.

This rule generalizes to any theory layer whose interface is built around
**immutable identifiers** (e.g. `PolyId`, `EClassId`, `ClauseId`,
`ArrayTermId`, `EnodeId`). Use it whenever you suspect heavy
algorithmic work is being recomputed across stages.

---

## The rule

> A function is a hash-cons cache candidate iff **(1)** its inputs are
> *immutable IDs* (or values that are cheaply hashable and fixed once
> allocated), **(2)** the function is *pure* (no side-effects beyond the
> result), and **(3)** the call graph contains *meaningful re-query
> redundancy* — the same input is asked the same question many times.

The yield of a cache depends almost entirely on **(3)** — the per-call
cost matters far less than how many times the same call is repeated.
A function with 1 µs cost but 100× repetition is a better cache target
than one with 100 µs cost called twice.

---

## When NOT to cache

| Anti-pattern | Why it fails |
|---|---|
| Function depends on *sample / assignment / model* | Not pure — same ID, different output as the model evolves. Example: `sgn(p, sample)`, `evalInteger(p, sample)`. |
| Function depends on *mutated solver state* across calls | The cache would bind to whichever state happened to be present at first call. Example: `pseudoRemainder` depends on `main_variable`, which `pscChain` mutates — caching by `(p, divisor)` alone is unsound. |
| Function is *already a single primitive call* | The cache lookup itself dominates. Example: `isConstant(p)` is `lp_polynomial_is_constant(p)` — one tagged-bit check, ~1 ns. Wrapping in a `unordered_map::find` is *slower*. |
| Call-graph redundancy is *low* | Empirically measured by instrumentation. If hit rate < 50 %, skip. The cache adds overhead without payoff. |

The third anti-pattern catches teams who reflexively cache "anything pure
and bounded". Caching `isConstant` was an early temptation in the Task M
audit; aborted after recognizing the per-call cost is ~1 ns vs ~50 ns map
lookup.

---

## Audit methodology

A four-step process. Steps 1-2 take ~30 minutes per candidate; steps 3-4
take ~15 minutes if the candidate clears.

### Step 1 — `grep` for "alloc / fresh / copy" patterns

Look for functions in your module that **allocate a new object, walk a
data structure, or copy data on every call**. These are the candidates.

```bash
grep -nE 'std::vector<|std::set<|new |alloc\(' src/theory/<your_lane>/<module>.cpp \
  | head -50
```

Cross-reference with **call-site counts** — pick candidates with the most
sites:

```bash
for op in op1 op2 op3; do
  count=$(grep -rE "\.${op}\(|->${op}\(" src/ | wc -l)
  echo "$op: $count call sites"
done
```

A high call-site count is **necessary but not sufficient** — it indicates
*potential* redundancy. Step 2 measures *actual* redundancy.

### Step 2 — Add stats instrumentation (no cache)

Add two `mutable uint64_t` counters to the class — *hits* and *misses* —
and gate stats dump behind an env var. Update the call site to bump
*misses* on every call. Then run a representative stress case (canonical
hot benchmarks from your lane) and read the count.

Caveat: at this stage you don't have a cache, so "hits" stay zero — but
the *miss count* tells you the call frequency. If the miss count is in
the tens, skip — there's not enough work to amortize a cache.

### Step 3 — Add the cache (template below) and remeasure

Now wrap the function in an `unordered_map` keyed on the immutable IDs.
Run the same stress case and observe the hit rate.

**Decision threshold**:
- **≥ 80 % hit rate → ship.** Strong call-graph redundancy.
- **50-80 % → judgement call.** Look at *absolute* hit count; 70 % of 10k
  calls is meaningful, 70 % of 100 calls is noise.
- **< 50 % hit rate → revert.** Empirical evidence of low redundancy.
- **0 hits, 0 misses (cold) → revert.** The function isn't on the hot
  path for the cases you measured. (Don't blindly assume it's hot on
  other cases; profile on real workloads next.)

### Step 4 — Validate soundness gate

Run the full unit suite + your lane's regression. **Soundness is the gate,
not the hit rate.** A cache that bumps the hit-rate by 5 percentage
points but introduces one false-UNSAT is a regression, period.

```bash
( ulimit -v 4000000; timeout 600 ./build_taskj/tests/xolver_unit_tests )
T0=$(date +%s); for f in tests/regression/<lane>/*.smt2; do ... ; done
```

If unit + lane reg = clean, commit with `[lane]/p6: TaskX — hash-cons
<function> (S<N>)` and push.

---

## Cache template (30 lines, additive)

```cpp
// In <Module>.h, private section:
mutable std::unordered_map<KeyT, ValueT> myCache_;
mutable uint64_t myHits_ = 0;
mutable uint64_t myMisses_ = 0;

// In <Module>.cpp, at function entry:
ReturnT MyModule::theFunction(InputT input) const {
    const KeyT key = makeKey(input);
    {
        auto it = myCache_.find(key);
        if (it != myCache_.end()) {
            ++myHits_;
            return it->second;
        }
    }
    ++myMisses_;

    // ... original implementation ...
    ReturnT result = computeOriginal(input);
    myCache_.emplace(key, result);
    return result;
}

// In ~MyModule() destructor:
if (std::getenv("XOLVER_<LANE>_<MODULE>_STATS")) {
    const auto total = myHits_ + myMisses_;
    const double rate = total ? 100.0 * myHits_ / total : 0.0;
    std::fprintf(stderr, "[STATS] my hits=%llu misses=%llu rate=%.2f%% cache=%zu\n",
                 (unsigned long long)myHits_, (unsigned long long)myMisses_,
                 rate, myCache_.size());
}
```

Soundness invariants the template preserves:
1. **`mutable` allows the cache on `const` methods** without changing
   their pure-function contract from the caller's view.
2. **`emplace` (not `insert_or_assign`)** so a value once stored is
   never overwritten — guards against caching half-completed results
   that some later codepath would have refined.
3. **Lifetime of the cache = lifetime of the owning class.** For
   `LibPolyKernel`, this means the cache lives as long as the kernel,
   which lives as long as the solver instance; entries never go stale
   because `PolyId`s are never recycled.
4. **No `nullopt` short-circuit unless the result is actually
   `std::optional`.** Caching success-or-failure both is fine; caching
   *only* success and re-computing failure on every call wastes the
   re-computation.

---

## Cross-lane application — where to look next

| Lane | Module | Candidates | Expected key shape |
|---|---|---|---|
| **NIA** | `LibPolyKernel` (shared with NRA) | already S1+S1b+S2+S1c+S1d+S1e | `(op, PolyId, PolyId)`, `PolyId`, `RP fingerprint`, `(PolyId, VarId)` |
| **NIA** | `ModularResidueReasoner` | `enumResidues(poly, modulus)`, `liftHensel(p, root)` | `(PolyId, mpz)` |
| **EUF** | `RollbackSignatureTable` | `find(eclass)`, `congruentSignature(enode)` | `EnodeId`, `EClassId` |
| **EUF** | `ProofForest` | `pathTo(root, eclass)`, `explainEquality(eq)` | `EClassId`, `(EClassId, EClassId)` |
| **Array** | `ArrayReasoner` | `representativeStore(arr)`, `selectClosure(arr, idx)` | `(ArrayTermId, IdxTermId)` |
| **SAT** | CaDiCaL is third-party, but at the *adapter* layer | clause-canonicalization on the boundary | `vector<Lit>` (sorted, hashed) |
| **Combination** | `SharedTermRegistry` | `termsOfSort(sort)`, `signaturesAcross(theory)` | `SortId`, `(TheoryId, EClassId)` |
| **Datatype** | DT plugin | `constructorsOf(sort)`, `selectorEval(c, i)` | `SortId`, `(CtorId, FieldId)` |

For each lane: pick one candidate, run the four-step methodology, ship if
clears the threshold. Each shipped cache reduces aggregate wall-clock
without changing soundness behaviour, which means it is a **free win**
under the master-spec invariants (FLOOR vs RECOVERY policy: cache speeds
RECOVERY without touching the soundness FLOOR).

---

## Empirical reference — `LibPolyKernel` (NRA) results

For calibration on what realistic hit rates look like:

| Cache | Function | Sites | Stress hit rate (Melquiond2, 3581 polys) | Cache size | Status |
|---|---|---|---|---|---|
| S1 | `add/sub/mul/pow/neg` | many | **29.89 %** (binary ops) | 1055 | shipped (structural unique inputs but downstream caches absorb) |
| S1b | `gcd / lc / sqf` | medium | shares S1 binOp | 10 (sqf) | shipped |
| S2 | `toPrimitiveInteger` (RP) | driver | **96.98 %** | 678 | shipped |
| S1c | `terms()` | 88 | **97.56 %** | 2007 | shipped |
| S1d | `variables()` | 92 | **96.84 %** | 12 | shipped |
| S1e | `degree(p, v)` | 55 | **98.37 %** | 6 | shipped |
| S1f | `getIntegerCoefficients(p, v)` | 11 | **0 / 0** (cold) | – | reverted (< 50 % rule) |
| – | `isConstant(p)` | many | – | – | rejected (per-call < lookup) |
| – | `pseudoRemainder` | 1 | – | – | rejected (unsound under main_variable mutation) |

The 5 shipped caches collectively touch every poly-kernel call from the
SAT layer downward. **Memory cost is bounded by the unique-input set**
(varies from 6 entries for `degree` to 2007 for `terms`); none grew
unboundedly across the regression suite (143 / 143 with all caches on,
unit 1083 / 1083).

---

## Anti-pattern: caching *speculatively*

The lowest-cost mistake in this methodology is to skip steps 2-3 and
just cache *because the function looks cacheable*. Two recent examples:

* **`intCoeffs` (Task M)**: would have shipped on instinct (pure
  function, key (PolyId, VarId), 11 sites — all the signals say
  *cache me*). Profiling showed it was called **0 times** on the four
  canonical NRA stress cases. The cache would have been dead code.
* **`pseudoRemainder` (Task A)**: would have shipped on instinct (binary
  op, immutable inputs). Recognized **only via reading the libpoly docs**
  that `prem` depends on the kernel's currently-installed `main_variable`,
  which `pscChain` mutates. Caching by `(p, divisor)` would produce
  *wrong results* on second call with a different installed order.

**Don't skip the profile step.** Instinct is right ~70 % of the time;
that 30 % is unsound caches or dead caches.

---

## Cross-reference

* The `WSL-SAFE-PROTOCOL.md` constraints apply unchanged to the
  hit-rate-measurement step — keep stress runs single-process,
  `ulimit -v 4G`, `timeout N` per case, `-j 2` if parallelizing.
* The Stage-5 NRA-lane summary (`docs/phase-d/STAGE5-NRA-lane-summary.md`)
  has the full per-commit details for each cache shipped here.
* The Task K bilinear audit (`docs/phase-d/P6-TaskK-bilinear-audit.md`)
  is a case study of using the call-graph redundancy framework to *reject*
  a lever — bilinear x*y patterns flow through 3 cached layers (S1 → S2
  → S1c), and the 96-97 % aggregate hit rate already absorbs the
  redundancy; adding a fourth layer would be strictly redundant.

---

*Branch: `agent/nra-2`. Tip: `d993531` at the time of writing.*
*WSL-safe-protocol observed throughout.*
