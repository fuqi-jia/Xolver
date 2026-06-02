# Task V — EUF cross-lane hash-cons audit

Master's priority-1 dispatch (8 h queue v2). Apply
`docs/CAMPAIGN-RULES-hash-cons-audit.md` directly to `src/theory/euf/`.

**Conclusion**: no shippable surface. EUF data structures are either
**already-cached** (the cache *is* the data structure) or **structurally
under-optimized but empirically shallow** (current workloads keep find
chains ≤ 2 hops). Defer. No cross-lane notification needed.

---

## Per-component audit

### `RollbackSignatureTable` — already the cache

The class **is** an `std::unordered_map<AppSignature, EufTermId,
AppSignatureHash>` with a rollback trail. There is no underlying expensive
computation to memoize — its entire purpose is the lookup cache for
congruence-class signatures. Adding a layer of hash-cons would duplicate
the same map.

### `EufTermManager::intern` — already hash-consed

Line 98-99 of `EufTermManager.cpp` shows `intern()` checks
`exprToTerm_` first and returns the cached term on hit. This *is* the
hash-cons cache for ExprId → EufTermId. The 6-line worker after the
cache-miss path is what the cache absorbs on repeat queries.

### `IncrementalEGraph::same` / `::rep` — wrap union-find

Both delegate to `RollbackUnionFind::find()`. Their behavior is
identical to caching the find call itself, which is examined below.

### `RollbackUnionFind::find()` — structurally under-optimized, empirically not a bottleneck

Lines 13-19 of `RollbackUnionFind.cpp`:

```cpp
EClassId find(EClassId x) const {
    assert(x < parent_.size());
    while (parent_[x] != x) {
        x = parent_[x];
    }
    return x;
}
```

**This is a naive iterative walk with NO path compression.** A textbook
union-find adds path compression: each find updates `parent_[x]` to
point directly to the root, amortising future calls to O(α(n)).

The reason path compression is missing: it would require updating
`parent_` *outside* the rollback trail's bookkeeping (path compression
is semantics-preserving and rollback-irrelevant, but the codebase's
rollback trail records every `parent_` change to support undo). Adding
non-tracked compression mutations is sound, but requires a careful
review of the rollback contract — that's **structural work outside the
"30-line additive cache" budget** of the hash-cons pattern.

**Empirical chain depth on representative cases** (find()
instrumentation, env-gated `XOLVER_EUF_HC_STATS=1`):

| Case | find() calls | totalDepth | avgDepth | maxDepth |
|---|---|---|---|---|
| `euf_001_sat_basic_eq` | 20 | 1 | 0.05 | 1 |
| `uflia_005_sat_fun_arith` | 684 | 592 | **0.87** | **2** |
| `uflra_007_sat_fn_diseq` | 116 | 30 | 0.26 | 1 |
| `z3.1184131` (QF_UF TypeSafe) | 87 | 8 | 0.09 | 1 |

Under union-by-size (which `unite()` does, lines 35-37 of
`RollbackUnionFind.cpp`), the tree stays balanced and chains stay
shallow. **Path compression on these workloads saves at most 1 pointer
hop per call**. The find body is already a 3-instruction loop. The
optimization yield is sub-percent.

For Wisa-sized EUF workloads (xs_10_10 / xs_10_20), the instrumentation
returned empty (timeout before STATS dump). A deeper EUF stress harness
is needed to measure chains on those cases; if a future profile shows
`maxDepth > 10` or `avgDepth > 5`, revisit. For Stage 5 ship, find() is
NOT in scope.

### `ProofForest::path` — 1 call site

Single call site at `IncrementalEGraph.cpp:445`. **Definitionally no
cross-call redundancy**. Same anti-pattern as `extractSymbolicResidue`
in NRA — a one-site function cannot benefit from caching.

### `IncrementalEGraph::computeSignature` — trail-mutable

The signature is computed from current UF representatives, which change
with merges/rollbacks. Same input term, different signature across
trail levels — fails the pure-function prerequisite.

### `IncrementalEGraph::explainEquality` — trail-mutable + precision-critical

Reads the current proof forest, which is mutable per merge/rollback.
Per the Wisa #11 memory ([[project_wisa_varconst]]), incorrect
explainEquality is a known false-UNSAT *source*. Caching anywhere
within explain paths requires deep soundness analysis.

---

## What does cross-lane application yield here?

The methodology's value on this audit is the **decisive `no`** it
produces in ~30 minutes per candidate. The EUF lane has already pushed
its data structures into the form a hash-cons would produce (built-in
indexing for `SignatureTable` and `intern`), and the one
under-optimized path (`find()`) is empirically shallow at current
scale. Without the methodology, an outside agent might spend hours
attempting find() caching only to learn the chains are 1 hop deep.

This is the methodology working as intended: **a tool to rule things
out cheaply**, not just to ship caches.

## Cross-lane notification

**Not required**. No patch, no surface change. The EQNA / EUF-area
agents own deeper EUF optimization; if they identify a deep EUF
stress workload showing meaningful find() chain depth, the
`docs/CAMPAIGN-RULES-hash-cons-audit.md` methodology applies directly
to that signal.

---

*Binary: `agent/nra-2` @ `d4d30d5`.*
*Instrumentation env: `XOLVER_EUF_HC_STATS=1` (reverted after audit;
this env var is not in the shipped binary).*
*WSL-safe protocol observed.*
