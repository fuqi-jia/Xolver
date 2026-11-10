#pragma once

#include "contracts/TheorySolver.h"
#include "search/combination/CareGraph.h"
#include <algorithm>
#include <span>
#include <utility>
#include <vector>

namespace xolver {

// Each distinct term has independently been proved equal to the same exact
// value under its listed premises. The value itself stays with the producer.
struct SharedEqualityWitness {
    SharedTermId term;
    std::vector<SatLit> reasons;
};

// A star connects the same equality class as all pairwise edges. Choose a
// cared anchor so every retained edge passes the existing care-pair filter.
// Rebuild from current witnesses on every check; explanations are never cached.
inline void appendSharedEqualityGroup(std::span<const SharedEqualityWitness> entries,
    std::vector<TheorySolver::SharedEqualityPropagation>& result,
    const CareGraph* careGraph = nullptr) {
    if (entries.size() < 2) return;
    auto anchor = entries.begin();
    if (careGraph) {
        anchor = std::find_if(entries.begin(), entries.end(),
            [&](const auto& entry) { return careGraph->cares(entry.term); });
        if (anchor == entries.end()) return;
    }
    for (auto entry = entries.begin(); entry != entries.end(); ++entry) {
        if (entry == anchor || entry->term == anchor->term) continue;
        // Keep the original pair orientation, including when care relevance
        // selects an anchor later in the producer's stable group order.
        const auto& first = entry < anchor ? *entry : *anchor;
        const auto& second = entry < anchor ? *anchor : *entry;
        std::vector<SatLit> reasons;
        reasons.reserve(first.reasons.size() + second.reasons.size());
        reasons.insert(reasons.end(), first.reasons.begin(), first.reasons.end());
        reasons.insert(reasons.end(), second.reasons.begin(), second.reasons.end());
        std::sort(reasons.begin(), reasons.end(), [](SatLit a, SatLit b) {
            return a.var < b.var || (a.var == b.var && a.sign < b.sign);
        });
        reasons.erase(std::unique(reasons.begin(), reasons.end()), reasons.end());
        result.push_back({first.term, second.term, std::move(reasons)});
    }
}

} // namespace xolver
