#pragma once

#include "theory/arith/icp/IcpResult.h"
#include "theory/arith/icp/IcpTypes.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <vector>

namespace nlcolver {

/**
 * NiaIcpAdapter: bridges DomainStore/NiaSolver to IcpEngineZ.
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

} // namespace nlcolver
