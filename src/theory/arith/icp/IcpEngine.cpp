#include "theory/arith/icp/IcpEngine.h"

namespace xolver {

IcpResultZ IcpEngine::run(
    const std::vector<std::unique_ptr<Contractor>>& contractors,
    const WatcherMap& watchers,
    ReasonedBox& box,
    const IcpConfig& config) {

    Worklist wl;
    for (size_t i = 0; i < contractors.size(); ++i) {
        wl.push(i);
    }

    int iterations = 0;
    int contractorsRun = 0;

    while (!wl.empty()) {
        if (++iterations > config.maxIterations || contractorsRun > config.maxContractors) {
            return IcpResultZ{IcpStatus::UnknownBudget, std::nullopt, {}, std::nullopt};
        }

        size_t cid = wl.pop();
        auto r = contractors[cid]->contract(box);
        ++contractorsRun;

        if (r.status == IcpStatus::Conflict) {
            return IcpResultZ{IcpStatus::Conflict, r.conflict, {}, std::nullopt};
        }

        if (r.status == IcpStatus::DomainUpdate) {
            for (const auto& u : r.updates) {
                auto w = watchers.getWatchers(u.var);
                wl.pushAll(w);
            }
        }
    }

    if (box.isEmpty()) {
        // Should have been caught by contractor, but safety check
        return IcpResultZ{IcpStatus::Conflict, std::nullopt, {}, std::nullopt};
    }

    return IcpResultZ{IcpStatus::NoChange, std::nullopt, {}, std::nullopt};
}

} // namespace xolver
