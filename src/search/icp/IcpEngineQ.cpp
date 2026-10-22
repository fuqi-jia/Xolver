#include "search/icp/IcpEngineQ.h"
#include <utility>

namespace xolver {

IcpResultQ IcpEngineQ::run(
    const std::vector<std::unique_ptr<ContractorQ>>& contractors,
    const WatcherMap& watchers,
    ReasonedBoxQ& box,
    const IcpConfig& config) {

    for (const auto& [var, interval] : box.entries()) {
        if (interval.interval.isEmpty())
            return {IcpStatus::Conflict, TheoryConflict{interval.reasons}, {}};
    }

    Worklist worklist;
    for (size_t i = 0; i < contractors.size(); ++i) worklist.push(i);
    int iterations = 0;
    int contractorsRun = 0;
    while (!worklist.empty()) {
        if (iterations >= config.maxIterations || contractorsRun >= config.maxContractors)
            return {IcpStatus::UnknownBudget, std::nullopt, {}};
        ++iterations;
        auto result = contractors[worklist.pop()]->contract(box);
        ++contractorsRun;
        if (result.status == IcpStatus::Conflict)
            return {IcpStatus::Conflict, std::move(result.conflict), {}};
        // Rational contractors update the box directly. An emptied interval
        // already has a complete contradiction, even if this call used the
        // final unit of the work budget.
        if (result.status == IcpStatus::DomainUpdate) {
            for (const auto& update : result.updates) {
                const auto interval = box.get(update.var);
                if (interval && interval->interval.isEmpty())
                    return {IcpStatus::Conflict,
                        TheoryConflict{interval->reasons}, {}};
                worklist.pushAll(watchers.getWatchers(update.var));
            }
        }
    }
    // Preserve the rational engine's existing fixpoint contract: updates are
    // read from the mutable box, and NoChange denotes the reached fixpoint.
    return {IcpStatus::NoChange, std::nullopt, {}};
}

} // namespace xolver
