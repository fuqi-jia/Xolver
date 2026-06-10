#pragma once

#include "theory/arith/icp/Contractor.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/icp/Worklist.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <memory>
#include <vector>

namespace xolver {

/**
 * ContractorFactory: builds V1 contractors from IcpConstraints.
 *
 * Dispatch order (fixed):
 *   1. Try SquareContractor
 *   2. Try SumSquaresContractor (stub in V1)
 *   3. Try RelationContractor only if single-var interval eval succeeds
 *   4. Otherwise no contractor
 */
class ContractorFactory {
public:
    struct BuildResult {
        std::vector<std::unique_ptr<Contractor>> contractors;
        WatcherMap watchers;
    };

    static BuildResult build(
        const std::vector<IcpConstraint>& constraints,
        PolynomialKernel& kernel);
};

} // namespace xolver
