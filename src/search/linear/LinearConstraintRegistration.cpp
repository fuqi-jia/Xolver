#include "search/linear/LinearConstraintRegistration.h"

namespace xolver {
// ============================================================================
// registerLinearConstraint
// ============================================================================
SatLit registerLinearConstraint(
    TheoryAtomRegistry& registry,
    const ZeroLinearConstraint& c,
    TheoryId targetTheory) {

    LinearAtomSpec spec = LinearConstraintNormalizer::toLinearAtomSpec(c);
    return registry.getOrCreateLinearBoundAtom(spec.lhs, spec.rel, spec.rhs, targetTheory);
}

}
