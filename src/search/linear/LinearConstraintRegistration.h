#pragma once
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/coordination/TheoryAtomRegistry.h"

namespace xolver {
SatLit registerLinearConstraint(TheoryAtomRegistry&, const ZeroLinearConstraint&, TheoryId);
}
