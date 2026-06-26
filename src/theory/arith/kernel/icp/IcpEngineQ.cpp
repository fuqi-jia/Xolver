#include "theory/arith/kernel/icp/IcpEngineQ.h"

namespace xolver {

IcpResultQ IcpEngineQ::run(
    const std::vector<std::unique_ptr<ContractorQ>>& contractors,
    const WatcherMap& watchers,
    ReasonedBoxQ& box,
    const IcpConfig& config) {

    Worklist wl;
    for (size_t i = 0; i < contractors.size(); ++i) {
        wl.push(i);
    }

    int iterations = 0;
    int contractorsRun = 0;

    while (!wl.empty()) {
        if (++iterations > config.maxIterations || contractorsRun > config.maxContractors) {
            return IcpResultQ{IcpStatus::UnknownBudget, std::nullopt, {}, std::nullopt};
        }

        size_t cid = wl.pop();
        auto r = contractors[cid]->contract(box);
        ++contractorsRun;

        if (r.status == IcpStatus::Conflict) {
            return IcpResultQ{IcpStatus::Conflict, r.conflict, {}, std::nullopt};
        }

        if (r.status == IcpStatus::DomainUpdate) {
            for (const auto& u : r.updates) {
                auto w = watchers.getWatchers(u.var);
                wl.pushAll(w);
            }
        }
    }

    if (box.isEmpty()) {
        return IcpResultQ{IcpStatus::Conflict, std::nullopt, {}, std::nullopt};
    }

    return IcpResultQ{IcpStatus::NoChange, std::nullopt, {}, std::nullopt};
}

} // namespace xolver
