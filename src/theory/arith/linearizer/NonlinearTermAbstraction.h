#pragma once

#include "theory/arith/linearizer/LinearizationTypes.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <unordered_map>

namespace zolver {

struct AbstractionResult {
    PolyId linearizedPoly;      // polynomial with aux vars replacing nonlinear monomials
    std::vector<AuxTerm> auxTerms;
    bool unsupported = false;
};

class NonlinearTermAbstraction {
public:
    explicit NonlinearTermAbstraction(PolynomialKernel& kernel);

    // Scan each monomial, replace nonlinear ones with aux vars
    AbstractionResult abstract(PolyId poly);

    // Get or create aux var for a canonical key
    AuxTerm getOrCreateAux(const NonlinearTermKey& key);

private:
    PolynomialKernel& kernel_;
    std::unordered_map<NonlinearTermKey, AuxTerm, NonlinearTermKeyHash> auxCache_;
    uint32_t nextAuxId_ = 0;

    std::optional<NonlinearTermKey> detectNonlinearTerm(
        const PolynomialKernel::MonomialTerm& term);
};

} // namespace zolver
