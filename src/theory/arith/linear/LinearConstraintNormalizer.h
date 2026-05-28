#pragma once

#include "theory/arith/linear/LinearConstraintTypes.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/TheoryAtomRegistry.h"
#include <optional>

namespace xolver {

// ============================================================================
// LinearConstraintNormalizer: single exit for converting linear constraints
// into registry-ready LinearAtomSpec.
//
// Invariant: no business code may call getOrCreateLinearBoundAtom directly.
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
    //   - strict integer relations are normalized (< -> ≤ -1, > -> ≥ +1)
    //   - terms are canonicalized (sorted, merged, zero-coeffs removed)
    // ------------------------------------------------------------------------
    static LinearAtomSpec toLinearAtomSpec(const ZeroLinearConstraint& c);

    // ------------------------------------------------------------------------
    // Register a ZeroLinearConstraint into the TheoryAtomRegistry.
    // Returns a dummy lit (var==0) if registration fails.
    // ------------------------------------------------------------------------
    static SatLit registerLinearConstraint(
        TheoryAtomRegistry& registry,
        const ZeroLinearConstraint& c,
        TheoryId targetTheory);

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

private:
    // Normalize strict integer relations in-place.
    static void normalizeStrictIntegerRelation(Relation& rel, mpq_class& rhs);

    // Relation flip for assigned false.
    static Relation negateRelationForEffective(Relation r);
};

} // namespace xolver
