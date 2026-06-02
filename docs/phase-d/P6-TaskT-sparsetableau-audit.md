# Task T — SparseTableau cross-lane audit (LIA / LRA territory)

Master's priority-4 dispatch (8 h queue). Apply the cross-lane hash-cons
pattern from `docs/CAMPAIGN-RULES-hash-cons-audit.md` to LRA
`SparseTableau` and the bounds infrastructure.

**Conclusion**: no hash-cons surface. SparseTableau **already has its
own indexing mechanism** that does the work a hash-cons would do, and
bounds are trail-mutable state that fails the pure-function prerequisite.
Defer. No cross-lane notification needed.

---

## Audit findings

### SparseTableau — already indexed in-class

`SparseRow::pos` (`src/theory/arith/lra/SparseTableau.h:34-37`) is a
`std::unordered_map<int /* col */, int /* index into entries */>`,
maintained lazily above an entry-size threshold (`INDEX_THRESHOLD` in
`SparseTableau.cpp`). The semantics:

- Small rows: linear scan of `entries` (cheap when N small).
- Large rows: O(1) lookup via `pos`.

Every structural mutation (`setCoeff`, `addCoeff`, `eraseCoeff`,
`replaceRow`) updates both `entries` and `pos` in step. Lines 70-71,
97-98, 122-… in `SparseTableau.cpp` confirm the bookkeeping.

A hash-cons layer over `getCoeff(row, col)` would either:
- **Duplicate the existing index** (waste memory, no perf gain), or
- **Layer above `pos`** — but `getCoeff` already short-circuits through
  `pos` when `hasIndex`, so the cache lookup would be redundant with the
  in-row map lookup.

The structural conclusion is that **this code has already had the
hash-cons-pattern-equivalent optimisation applied** at the data-structure
level (a per-row index), which is in fact the strongest form: invariant
maintenance is automatic with each mutation, no separate invalidation.

### Bounds (`BoundInfo`) — fails purity prerequisite

LRA bounds live in `GeneralSimplex` as per-variable `BoundInfo` state.
They are **mutable across trail decisions**: the same `var` returns
different bound values at different decision levels (via push/pop). The
pure-function prerequisite of the hash-cons rule fails on input → output
mapping changing with solver state.

The existing simplex code accesses bounds through direct member access
(no `getBound(var)` virtual to wrap), so even a per-level cache would
need a redesign that's outside an 8 h sprint window.

### `LraPropagationEngine` and bound-tightening

These layers do pure computation per-step but each step works on
*currently-active* bounds, which are trail-mutable. Same input variable,
different bound, different propagation result — not cacheable across
calls without invalidation tied to the trail, which the simplex itself
already handles via push/pop scoping.

---

## What about elsewhere in the LIA lane?

Master's pattern doc identifies several `EUF` / `Array` / `Combination`
candidates that don't apply here. Inside the LIA lane proper, the closest
pure-key candidates would be in `LraPropagationEngine`'s symbolic
computations on the *original* (un-asserted) constraint set. Those are
small in our LRA reg (143 cases in the NRA branch, 30+ NRA reg) and would
need a dedicated LIA-side profile to identify hot spots. **Cross-lane
ownership belongs to the LIA-deep lane** (`agent/lia-lra-deep` per the
session memory pointer), not this NRA sprint.

---

## Cross-lane notification

**Not required**. The audit found no surface; there is no patch to
notify or sync. The LIA-lane agent on `agent/lia-lra-deep` already
ships incremental-β (`fde9917`) and other in-class optimisations — they
own the local optimisation surface and don't need a heads-up about a
no-op audit from another lane.

If a future LIA-lane sprint identifies a hot symbolic-arithmetic path
that fits the hash-cons pattern, they can apply
`docs/CAMPAIGN-RULES-hash-cons-audit.md` directly to their own code.

---

*Binary: `agent/nra-2` @ `c473c7f`.*
*WSL-safe protocol observed (audit-only, no rebuild).*
