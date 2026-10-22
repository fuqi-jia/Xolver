#pragma once

#include "search/icp/Contractor.h"
#include "search/icp/IcpTypes.h"
#include "search/icp/Worklist.h"
#include "algebra/poly/PolynomialKernel.h"
#include <memory>
#include <vector>

namespace xolver {

// Build relation contractors for univariate rational constraints. For each
// live variable of a multivariate constraint, select the first applicable
// monomial, mixed-quadratic, bilinear or Cauchy contractor.
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
