# MGC-RD Phase 1.3 — NL Extension Lemma Audit

User dispatched 3-day R&D budget (2026-06-02) to fix MGC cluster TO.
Key hint: cvc5 closes mgc_02 in 4.7 s via **NL extension lemmas**, not
full CAC. Audit xolver's existing NL ext lemma surface, identify
which lemma classes are missing.

**Result**: the gap is precise and concrete. `NonlinearTermAbstraction`
explicitly rejects `x^n` for n ≥ 3 and any trilinear (`x*y*z`) terms.
MGC monomials like `vv3⁴` and `theta*vv1*vv3²` are never abstracted,
so the LINEARIZE / NLA_CUTS path emits no cuts for them. The high-
degree polynomial falls through to CDCAC which hangs on projection.

---

## xolver's existing NL ext lemma generators

`src/theory/arith/linearizer/`:

| Generator | Covered | File |
|---|---|---|
| `McCormickGenerator` | bilinear `x*y` | `McCormickGenerator.{h,cpp}` |
| `SquareCutGenerator` | `x²` — secant + tangent + nonneg + product | `SquareCutGenerator.{h,cpp}` |

Configuration via `LinearizationConfig`
(`src/theory/arith/linearizer/IncrementalLinearizer.h:19`):

```cpp
struct LinearizationConfig {
    bool emitAllMcCormick = true;
    bool emitSquareSecant = true;
    bool emitSquareTangent = true;
    bool emitSquareNonneg = true;
    size_t maxLemmas = 10;
    size_t maxCutsPerTerm = 4;
};
```

All four lemma classes are enabled by default — when the term is
**detected** as bilinear or square. Otherwise they don't fire.

## The hard cap: `NonlinearTermAbstraction::detectNonlinearTerm`

Source: `src/theory/arith/linearizer/NonlinearTermAbstraction.cpp:9-41`.

```cpp
std::optional<NonlinearTermKey> detectNonlinearTerm(const MonomialTerm& term) {
    const auto& powers = term.powers;

    // Product: x*y
    if (powers.size() == 2 && powers[0].second == 1 && powers[1].second == 1) {
        NonlinearTermKey key{...};
        return key;
    }

    // Square: x^2
    if (powers.size() == 1 && powers[0].second == 2) {
        NonlinearTermKey key{...};
        return key;
    }

    // Linear or constant
    if (powers.empty() ||
        (powers.size() == 1 && powers[0].second == 1)) {
        return std::nullopt;
    }

    // V1 unsupported (e.g., x^3, x*y*z, etc.)
    return std::nullopt;     // ← THE BUG: rejected silently
}
```

**Line 40**: returns `nullopt` for every monomial outside the strict
`{x*y, x²}` whitelist. The comment on line 39 explicitly lists `x^3`
and `x*y*z` as unsupported. **This is the missing surface.**

## Why this breaks MGC

`mgc_02` (first equation):
```
gamma0*theta - theta*vv1*vv3^2 - theta*vv1 = 0
```

Monomial breakdown:
* `gamma0*theta` — bilinear → handled (McCormick)
* `theta*vv1` — bilinear → handled (McCormick)
* `theta*vv1*vv3^2` — **trilinear product × square** → REJECTED

The mixed monomial `theta*vv1*vv3^2` is the structural fingerprint of
the MGC family (the "polynomial has a zero where all variables are
positive" pattern routinely produces degree-3 and degree-4 monomials).
xolver's linearizer skips the whole equation as unsupported and falls
through to CDCAC which then must solve a 9-variable high-degree
system from scratch — no linear cuts available to prune the search.

## What cvc5 has that xolver doesn't (per user's hint)

cvc5 (per `theory::arith::inferencesLemma` stats):

* **`ARITH_NL_SIGN`** (sign analysis of products) — partially in xolver
  as `SignDefinitenessRefuter` (per-constraint, no case-split).
* **`ARITH_NL_INFER_BOUNDS_NT`** (bound inference, no triangulation) —
  needs the same trilinear+ monomial abstraction xolver lacks.
* **`ARITH_NL_COMPARISON`** — tangent-plane comparisons across
  monomials; again needs the abstraction.
* **`ARITH_NL_TRANSCENDENTAL`** (atan / sin / exp monotonicity) —
  meti-tarski class, completely absent in xolver.

The first three need the **monomial abstraction extension**; the
fourth is a separate transcendental sub-lever.

## Phase 2 implementation scope

Three deliverables for the next 1-1.5 days:

### Phase 2A — extend `detectNonlinearTerm`

Add support for:

| Pattern | Generator | Cut shape |
|---|---|---|
| `x^n` for n ≥ 3 | new `PowerCutGenerator` | tangent at current model x₀: `x^n ≥ n*x₀^(n-1)*x - (n-1)*x₀^n` for n even or strict-monotone branches |
| `x*y*z` trilinear | recursive `McCormickGenerator` | decompose `(x*y)*z`, introduce aux for `(x*y)`, apply bilinear to aux × z |
| `x^a * y^b * ...` general | hash-cons + recursive split | iterate the recursion |

Estimated 200-400 LOC. Soundness: every cut is a tangent plane to a
known-sign-definite or known-monotone region, which is a sound
relaxation (cuts are over-approximations of the feasible region).

### Phase 2B — flag + paired test

Gate behind `XOLVER_NRA_NLEXT_HIGHER` (default-OFF). NRA reg
151/151 + 10-case MGC paired test (atan / sin / exp / sqrt /
Mulligan).

Acceptance: at least one MGC case decided that previously TO'd, or
better, a measurable speedup on the cluster.

### Phase 2C — transcendental sub-lever (defer)

`atan` / `sin` / `exp` monotonicity is a separate larger lever
(needs trigonometric range-bounding). Defer to a follow-up sprint if
Phase 2A + 2B already moves the MGC needle.

## Day 1 status

* **Day 1 morning**: NDEEP-1 / NDEEP-5 audit + Mulligan routing bug fix
  (`48b12ee` CAC_ALL_EFFORTS source-flip).
* **Day 1 afternoon**: MGC-PROFILE diagnosis (`6ab763b`) + this audit
  doc. Bottleneck localized to `detectNonlinearTerm`.
* **Tomorrow (Day 2)**: Phase 2A implementation + Phase 2B paired test.

---

*Branch: `agent/nra-2` @ `6ab763b`.*
*Reproducer: `mgc_02` polynomial `theta*vv1*vv3^2` is the unhandled
trilinear-with-square monomial.*
*WSL-safe protocol observed.*
*NO inline solver call (cvc5 stats source: external `cvc5 --verbose --stats`).*
