#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <memory>
#include <vector>

namespace xolver {

// Rational-side dispatcher — currently only builds RelationContractorQ for
// univariate polynomial atoms. Future versions: McCormickContractorQ,
// SquareContractorQ for x^2 ≥ 0 propagation, MonomialContractorQ.
class ContractorFactoryQ {
public:
    struct BuildResult {
        std::vector<std::unique_ptr<ContractorQ>> contractors;
        WatcherMap watchers;
    };

    static BuildResult build(
        const std::vector<IcpConstraint>& constraints,
        PolynomialKernel& kernel);
};

} // namespace xolver
