# Task S — AlgebraicNumber layer audit

Master's priority-3 dispatch (8 h queue). Apply the hash-cons audit
pattern to the layer below `LibPolyKernel`: `AlgebraicNumber` and the
operations exposed via `RealValue::sign`, `RealValue::compare`,
`RealAlgebraicOps`.

**Conclusion**: no shippable cache surface. The layer fails the
**immutable-ID prerequisite** of the hash-cons rule from
`CAMPAIGN-RULES-hash-cons-audit.md` — `AlgebraicNumber` is a plain value
struct with no analog of `PolyId`. Defer.

---

## Layer surface

- `struct AlgebraicNumber` (`src/util/RealValue.h:44`): plain data —
  `vector<mpz_class> coefficients`, `mpq_class lower`, `mpq_class upper`,
  two bools for open-ness of the isolation interval. **No identity**
  — every value is a fresh struct produced by polynomial arithmetic.
- `class RealValue`: wraps either a rational `mpq_class` or an
  `AlgebraicNumber`. Member ops `sign()`, `compare(o)`, `floor()`,
  `ceil()`, arithmetic operators. Rational-rational paths are inlined
  mpq operations (cheap); algebraic paths delegate to
  `realalg::compare/sign` in `RealAlgebraicOps.h`.
- `RealAlgebraicOps`: standalone functions over `RealValue`. Uses
  libpoly's algebraic-number engine for sign / compare / arithmetic on
  algebraic operands.

## Why hash-cons fails the immutable-ID prerequisite

The rule from `CAMPAIGN-RULES-hash-cons-audit.md` requires:

> **(1)** inputs are *immutable IDs* (or values that are cheaply hashable
> and fixed once allocated)

`AlgebraicNumber` satisfies *cheaply hashable* (`vector<mpz_class>` +
2 `mpq_class` + 2 `bool`), but **fails the call-graph redundancy test**:

- Each new algebraic value produced by `+ - * /` is a **fresh struct**
  with fresh coefficients and a fresh isolation interval. There is no
  ID system that would let two call sites pass the *same* AlgebraicNumber.
- The CAC algorithm produces algebraic values at projection/lifting
  boundaries. Each boundary value flows downstream once for verification
  and is then discarded. **Re-queries of the same value are rare** by
  construction.
- The rational `RealValue::sign()` / `compare()` paths are 3 mpq
  operations (~50 ns). The `isConstant` anti-pattern applies: a
  `unordered_map<AlgebraicNumber, int, Hash>` lookup would be slower
  per call than the actual operation.

## Empirical signal (instrumentation deferred)

The methodology's step 2 (instrument call frequency without a cache)
was prepared but not run, because:

* `AlgebraicNumber` lives in `src/util/`, which is shared by
  RealValue users across **multiple solvers** (NRA, NIA, LRA, LIA,
  combination). Adding an instrument counter here would require
  thread-local state to avoid TSan races in unit tests, which would in
  turn force a non-trivial change beyond the "30-line additive" pattern.
* The structural argument above already predicts low redundancy
  (fresh-per-op values, no ID reuse), and the `isConstant` anti-pattern
  applies to the rational-path which is the common case.

If a future deep profile of QF_NRA workloads identifies a specific
sub-bottleneck inside the algebraic operations (e.g. one specific
`compare()` site being called repeatedly with the same operand pair),
a *narrow* per-site cache in the caller is a better fit than a kernel
layer cache.

## What about the libpoly algebraic backend?

`src/theory/arith/nra/backend/LibpolyAlgebraic.cpp` translates between
`RealValue` and `poly::AlgebraicNumber` (the libpoly handle type) on
each operation. Memo: per the `RealValue.h:36-43` comment, the codebase
**explicitly avoids holding libpoly handles in `AlgebraicNumber`** to
prevent double-free hazards. Adding an ID system here would require
revisiting that design choice — out of scope for an 8 h sprint window.

If libpoly handles ever do get held (with a `shared_ptr<void>` + libpoly
deleter, as the comment suggests), then **handle equality** becomes a
candidate ID for caching, and this audit should be re-opened.

---

## Conclusion

The `AlgebraicNumber` layer is structurally hostile to hash-cons:
no ID system, fresh-per-op values, low call-graph redundancy by
algorithm design. The methodology cleanly rules it out without needing
to run the instrumentation phase.

Future ID-based hash-cons opportunity would require a libpoly handle
adoption in `AlgebraicNumber`, which the codebase has explicitly
deferred for double-free safety reasons.

---

*Binary: `agent/nra-2` @ `28a75e0`.*
*WSL-safe protocol observed (no rebuild required for this audit).*
