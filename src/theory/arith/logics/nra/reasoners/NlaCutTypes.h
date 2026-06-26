#pragma once

#include "expr/types.h"
#include "sat/SatSolver.h"
#include <cstdint>
#include <gmpxx.h>
#include <optional>
#include <vector>

namespace xolver {
namespace nla {

// NLA cut family. Different cut shapes have different proof obligations
// and integration points, so callers can dispatch on this when emitting.
enum class NlaCutKind : uint8_t {
    // Tangent line linearisation at a model point. For convex/concave
    // monomials (e.g. x^2 ≥ 0, x^2 ≥ 2*m*x − m^2 for any m), produces a
    // sound linear under-/over-approximation.
    Tangent,
    // Horner-form rewrite. Rewriting a multivariate polynomial in a
    // factored shape can expose structure the original sum-of-monomials
    // form hides (e.g. `xy + xz = x*(y+z)`).
    Horner,
    // Monotonicity / interval-arithmetic cut. From `a ≤ x ≤ b` and
    // `c ≤ y ≤ d` with `a,c ≥ 0`, derive `a*c ≤ x*y ≤ b*d`. The
    // single-variable square case `lo ≤ x ≤ hi, lo ≥ 0 ⇒ lo² ≤ x² ≤ hi²`
    // also lives here.
    Monotonicity,
    // Proportional cut. From `x ≤ y` and `z ≥ 0`, derive `x*z ≤ y*z`
    // (multiplying both sides by a non-negative quantity preserves the
    // inequality direction).
    Proportional,
};

// A single derived nonlinear arithmetic cut: a polynomial inequality the
// reasoner adds to the constraint set. Every cut is sound by construction
// — the generator never invents reasons, only composes existing ones.
//
// Soundness invariant: under every assignment that satisfies the SAT
// literals in `reasons`, `poly rel 0` must hold. The generator is
// responsible for proving this at cut emission time (either via a
// closed-form algebraic identity, or via a grid certificate the test
// suite locks in).
struct NlaCut {
    NlaCutKind kind = NlaCutKind::Monotonicity;
    PolyId poly = NullPoly;       // p
    Relation rel = Relation::Geq; // p rel 0
    std::vector<SatLit> reasons;  // SAT literals implying the cut
};

// Variable interval state. Bounds are rational (covers both LRA/NRA and
// LIA/NIA — integer bounds round to mpq with denominator 1). Either side
// may be absent, signalling "no known bound on this side".
//
// `reasons` is the union of SAT literals that jointly imply both bounds
// (if both are present). When a generator produces a cut from this
// interval, every literal in `reasons` must enter the cut's reason set.
struct VarInterval {
    PolyId varPoly = NullPoly;  // the variable as a polynomial (degree 1)
    std::optional<mpq_class> lo;
    std::optional<mpq_class> hi;
    std::vector<SatLit> reasons;
};

} // namespace nla
} // namespace xolver
