#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <memory>
#include <vector>

namespace xolver {

/**
 * ContractorFactoryZ: builds V1 contractors from IcpConstraints.
 *
 * Dispatch order (fixed):
 *   1. Try SquareContractorZ
 *   2. Try SumSquaresContractorZ (stub in V1)
 *   3. Try RelationContractorZ only if single-var interval eval succeeds
 *   4. Otherwise no contractor
 */
class ContractorFactoryZ {
public:
    struct BuildResult {
        std::vector<std::unique_ptr<ContractorZ>> contractors;
        WatcherMap watchers;
    };

    static BuildResult build(
        const std::vector<IcpConstraint>& constraints,
        PolynomialKernel& kernel);
};

} // namespace xolver
