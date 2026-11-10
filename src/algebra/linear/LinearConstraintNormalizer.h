#pragma once

#include "algebra/linear/LinearConstraintTypes.h"
#include "algebra/poly/PolynomialKernel.h"
#include "contracts/TheoryAtomTypes.h"
#include <optional>

namespace xolver {

// ============================================================================
// LinearConstraintNormalizer: single exit for converting linear constraints
// into registry-ready LinearAtomSpec.
//
// Mathematical normalization is independent of SAT atom registration.
// ============================================================================
class LinearConstraintNormalizer {
public:
    // ------------------------------------------------------------------------
    // Build a ZeroLinearConstraint from a polynomial that represents
    //   poly rel 0
    // Fails if poly contains nonlinear terms (degree > 1).
    // ------------------------------------------------------------------------
    static std::optional<ZeroLinearConstraint> fromPolynomialZero(
        const PolynomialKernel& kernel,
        PolyId poly,
        Relation rel,
        SortKind sort,
        const std::string& debugTag = {});

    // ------------------------------------------------------------------------
    // Convert a ZeroLinearConstraint into a LinearAtomSpec.
    // This is the ONLY place where:
    //   - constant term is moved to rhs (rhs = -constant)
    //   - integer constraints have denominators cleared before strictness rounding
    //   - terms are canonicalized (sorted, merged, zero-coeffs removed)
    // ------------------------------------------------------------------------
    static LinearAtomSpec toLinearAtomSpec(const ZeroLinearConstraint& c);

    // ------------------------------------------------------------------------
    // Build the effective constraint given an atom payload and its SAT value.
    // Returns nullopt if the effective relation is not representable as a
    // single linear bound (e.g. disequality when assigned false).
    // ------------------------------------------------------------------------
    static std::optional<ZeroLinearConstraint> makeEffectiveConstraint(
        const LinearAtomPayload& payload,
        bool assignedValue,
        SortKind sort);

    static std::optional<ZeroLinearConstraint> makeEffectiveConstraint(
        const PolynomialAtomPayload& payload,
        bool assignedValue,
        SortKind sort,
        const PolynomialKernel& kernel);

    // ------------------------------------------------------------------------
    // Canonicalize a LinearExpr: sort by var, merge duplicates, drop zeros.
    // ------------------------------------------------------------------------
    static LinearExpr canonicalize(LinearExpr e);

    // ------------------------------------------------------------------------
    // Sign-canonicalize a linear atom `lhs rel rhs` so its FIRST nonzero term
    // has a positive coefficient (terms assumed sorted by var name). When the
    // leading coefficient is negative, the whole atom is multiplied by -1:
    // lhs → -lhs, rhs → -rhs, rel mirrored (Leq↔Geq, Lt↔Gt; Eq/Neq fixed).
    // This makes complementary forms (x-y and y-x) share one aux in the simplex,
    // so x≤y ∧ y≤x collapse to a single [0,0] bound → the difference pins.
    // Returns true iff the atom was negated.
    static bool canonicalizeSign(LinearFormKey& lhs, Relation& rel, mpq_class& rhs);

    // Scale by a positive common denominator, then convert strict comparisons
    // to non-strict bounds. Every variable in lhs must range over integers;
    // this operation must not be applied to real-valued linear forms.
    static void normalizeIntegerConstraint(LinearFormKey& lhs, Relation& rel, mpq_class& rhs);

private:

    // Relation flip for assigned false.
    static Relation negateRelationForEffective(Relation r);
};

} // namespace xolver
