#pragma once

#include "theory/arith/kernel/linear/LinearExpr.h"
#include "sat/SatSolver.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <string>
#include <vector>

namespace xolver {

// ============================================================================
// LinearTerm: one variable term a_i * x_i
// ============================================================================
struct LinearTerm {
    std::string var;
    mpq_class coeff;
};

// ============================================================================
// LinearExpr: constant + Σ a_i * x_i
// ============================================================================
struct LinearExpr {
    mpq_class constant = 0;
    std::vector<LinearTerm> terms;
};

// ============================================================================
// ZeroLinearConstraint: expr rel 0  (business layer unified representation)
// All generators, adapters, and solvers must produce this form.
// ============================================================================
struct ZeroLinearConstraint {
    LinearExpr expr;
    Relation rel = Relation::Eq;
    SortKind sort = SortKind::Int;
    std::string debugTag;
};

// ============================================================================
// LinearAtomSpec: lhs rel rhs  (exactly what getOrCreateLinearBoundAtom expects)
// This must ONLY be produced by LinearConstraintNormalizer::toLinearAtomSpec.
// ============================================================================
struct LinearAtomSpec {
    LinearFormKey lhs;
    Relation rel = Relation::Eq;
    mpq_class rhs = 0;
    SortKind sort = SortKind::Int;
    std::string debugTag;
};

// ============================================================================
// LinearCut: a cut lemma in zero-right-hand-side form.
// Generators produce this; IncrementalLinearizer registers it via normalizer.
// ============================================================================
struct LinearCut {
    ZeroLinearConstraint constraint;
    std::vector<SatLit> reasons;
    std::string debugTag;
};

} // namespace xolver
