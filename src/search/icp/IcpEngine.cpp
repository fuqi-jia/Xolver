#include "search/icp/IcpEngine.h"
#include <map>
#include <utility>

namespace xolver {

IcpResultZ IcpEngine::run(
    const std::vector<std::unique_ptr<Contractor>>& contractors,
    const WatcherMap& watchers,
    ReasonedBox& box,
    const IcpConfig& config) {

    // An empty input interval already proves a conflict, including when there
    // are no contractors. Preserve its justification for the SAT layer.
    for (const auto& [var, interval] : box.entries()) {
        if (interval.interval.isEmpty()) {
            return {IcpStatus::Conflict, TheoryConflict{interval.reasons}, {}};
        }
    }

    Worklist wl;
    for (size_t i = 0; i < contractors.size(); ++i) wl.push(i);

    // Keep only the last (tightest) interval and its accumulated reasons for
    // each changed variable. Sound progress remains usable at a budget limit.
    std::map<std::string, BoundUpdateZ> changed;
    auto finish = [&](IcpStatus status) {
        std::vector<BoundUpdateZ> updates;
        updates.reserve(changed.size());
        for (auto& [var, update] : changed) updates.push_back(std::move(update));
        return IcpResultZ{status, std::nullopt, std::move(updates)};
    };

    int iterations = 0;
    int contractorsRun = 0;
    while (!wl.empty()) {
        if (iterations >= config.maxIterations || contractorsRun >= config.maxContractors) {
            return finish(IcpStatus::UnknownBudget);
        }
        ++iterations;
        size_t cid = wl.pop();
        auto result = contractors[cid]->contract(box);
        ++contractorsRun;
        if (result.status == IcpStatus::Conflict) {
            return {IcpStatus::Conflict, std::move(result.conflict), {}};
        }
        if (result.status != IcpStatus::DomainUpdate) continue;

        for (const auto& update : result.updates) {
            if (!box.narrow(update.var, update.newInterval, update.reasons)) continue;
            const auto interval = box.get(update.var);
            if (interval->interval.isEmpty()) {
                return {IcpStatus::Conflict, TheoryConflict{interval->reasons}, {}};
            }
            changed.insert_or_assign(update.var,
                BoundUpdateZ{update.var, interval->interval, interval->reasons});
            wl.pushAll(watchers.getWatchers(update.var));
        }
    }
    return finish(changed.empty() ? IcpStatus::NoChange : IcpStatus::DomainUpdate);
}

} // namespace xolver
