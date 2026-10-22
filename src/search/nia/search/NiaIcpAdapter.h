#pragma once

#include "search/icp/IcpResult.h"
#include "search/icp/IcpTypes.h"
#include "search/nia/core/DomainStore.h"
#include "algebra/poly/PolynomialKernel.h"
#include <vector>

namespace xolver {

/**
 * NiaIcpAdapter: bridges DomainStore/NiaSolver to IcpEngine.
 *
 * V1: forward eval + square/sum-of-squares pattern contractors only.
 */
class NiaIcpAdapter {
public:
    NiaIcpAdapter(PolynomialKernel& kernel, DomainStore& store);

    // Run ICP on the given constraints with current DomainStore bounds.
    IcpResultZ run(const std::vector<IcpConstraint>& constraints,
                   const IcpConfig& config);

private:
    PolynomialKernel& kernel_;
    DomainStore& store_;
};

} // namespace xolver
