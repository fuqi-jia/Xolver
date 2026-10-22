#pragma once

#include "search/icp/Contractor.h"
#include "search/icp/IcpTypes.h"
#include "search/icp/Worklist.h"
#include "algebra/poly/PolynomialKernel.h"
#include <memory>
#include <vector>

namespace xolver {

// Build integer contractors for univariate constraints. Recognized squares
// receive square contraction as well as the relation contractor; every other
// univariate polynomial retains the relation check.
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
