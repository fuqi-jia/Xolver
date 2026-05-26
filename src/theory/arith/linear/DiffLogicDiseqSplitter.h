#pragma once

#include "theory/core/TheorySolver.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearExpr.h"
#include <algorithm>
#include <string>
#include <vector>

namespace zolver {

// ============================================================================
// Build a split lemma for a difference-logic disequality  x - y != rhs.
//
// This helper constructs the two mirrored linear forms
//   lhs1 =  x - y   (for the "low" split)
//   lhs2 =  y - x   (for the "high" split)
// and creates theory atoms via the registry.
//
// Parameters:
//   - x, y              : variable names
//   - lit               : original SAT literal for the disequality
//   - splitLo, splitHi  : Relation for lhs1 / lhs2  (e.g. Lt, Leq)
//   - rhsLo, rhsHi      : RHS constants for lhs1 / lhs2
//   - theory            : TheoryId (RDL or IDL)
//   - registry          : TheoryAtomRegistry (must be non-null)
// ============================================================================
inline TheoryLemma buildDiffLogicDiseqSplitLemma(
    const std::string& x,
    const std::string& y,
    SatLit lit,
    Relation splitLo,
    Relation splitHi,
    const mpq_class& rhsLo,
    const mpq_class& rhsHi,
    TheoryId theory,
    TheoryAtomRegistry* registry)
{
    LinearFormKey lhs1;
    lhs1.terms.push_back({x, mpq_class(1)});
    lhs1.terms.push_back({y, mpq_class(-1)});
    std::sort(lhs1.terms.begin(), lhs1.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });

    LinearFormKey lhs2;
    lhs2.terms.push_back({y, mpq_class(1)});
    lhs2.terms.push_back({x, mpq_class(-1)});
    std::sort(lhs2.terms.begin(), lhs2.terms.end(),
              [](auto& a, auto& b) { return a.first < b.first; });

    SatLit litLo = registry->getOrCreateLinearBoundAtom(
        lhs1, splitLo, rhsLo, theory);
    SatLit litHi = registry->getOrCreateLinearBoundAtom(
        lhs2, splitHi, rhsHi, theory);

    return TheoryLemma{{lit.negated(), litLo, litHi}};
}

} // namespace zolver
