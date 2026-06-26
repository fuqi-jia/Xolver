#include "theory/arith/logics/nia/search/NiaIcpAdapter.h"
#include "theory/arith/kernel/icp/ContractorFactory.h"
#include "theory/arith/kernel/icp/IcpEngine.h"
#include "theory/arith/kernel/interval/ReasonedBox.h"

namespace xolver {

NiaIcpAdapter::NiaIcpAdapter(PolynomialKernel& kernel, DomainStore& store)
    : kernel_(kernel), store_(store) {}

IcpResultZ NiaIcpAdapter::run(const std::vector<IcpConstraint>& constraints,
                              const IcpConfig& config) {
    // Build ReasonedBox from DomainStore
    ReasonedBox box;
    for (const auto& [var, domain] : store_.getAllDomains()) {
        if (domain.hasLower && domain.hasUpper) {
            std::vector<SatLit> reasons;
            reasons.insert(reasons.end(), domain.lower.reasons.begin(), domain.lower.reasons.end());
            reasons.insert(reasons.end(), domain.upper.reasons.begin(), domain.upper.reasons.end());
            box.set(var, ReasonedInterval{IntervalZ{domain.lower.value, domain.upper.value}, reasons});
        }
    }

    // Build contractors and run ICP
    auto buildResult = ContractorFactory::build(constraints, kernel_);
    IcpEngine engine;
    IcpResultZ result = engine.run(buildResult.contractors, buildResult.watchers, box, config);

    // Apply domain updates back to DomainStore
    if (result.status == IcpStatus::DomainUpdate) {
        for (const auto& u : result.updates) {
            if (!u.newInterval.isEmpty()) {
                for (SatLit r : u.reasons) {
                    store_.addLowerBound(u.var, u.newInterval.lo, r);
                    store_.addUpperBound(u.var, u.newInterval.hi, r);
                }
            }
        }
    }

    return result;
}

} // namespace xolver
