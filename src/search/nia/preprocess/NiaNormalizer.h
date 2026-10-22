#pragma once

#include "algebra/poly/PolynomialKernel.h"
#include "contracts/SatSolver.h"
#include <vector>

namespace xolver {

// PolynomialConverter clears rational denominators before constructing these
// integer-ring polynomials. The relation already includes asserted polarity.
struct ActiveNiaConstraint {
    PolyId poly;
    Relation rel;
    SatLit reason;
};

struct NormalizedNiaConstraint {
    PolyId poly;      // Integer coefficients, p rel 0.
    Relation rel;     // Eq, Neq, Leq or Geq.
    SatLit reason;
};

// Normalize strict relations over integer-valued polynomials. This operation
// is per constraint, so cached results remain valid while that constraint and
// its reason remain on the active stack.
class NiaNormalizer {
public:
    explicit NiaNormalizer(PolynomialKernel& kernel);

    std::vector<NormalizedNiaConstraint>
    normalize(const std::vector<ActiveNiaConstraint>& active);
    NormalizedNiaConstraint normalizeOne(const ActiveNiaConstraint& constraint);

private:
    PolynomialKernel& kernel_;
};

} // namespace xolver
