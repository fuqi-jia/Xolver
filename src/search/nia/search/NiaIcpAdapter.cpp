#include "search/nia/search/NiaIcpAdapter.h"
#include "search/icp/ContractorFactory.h"
#include "search/icp/IcpEngine.h"
#include "algebra/interval/ReasonedBox.h"

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

    // The engine also returns sound partial progress on budget exhaustion.
    // Pass each complete justification together, including unconditional bounds.
    for (const auto& update : result.updates) {
        if (!update.newInterval.isEmpty()) {
            store_.addLowerBound(update.var, update.newInterval.lo, update.reasons);
            store_.addUpperBound(update.var, update.newInterval.hi, update.reasons);
        }
    }

    return result;
}

} // namespace xolver
