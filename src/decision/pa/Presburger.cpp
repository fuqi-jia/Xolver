#include "decision/pa/Elimination.h"

namespace xolver::pa {
bool hasQuantifiers(const std::vector<SOMTParser::Node>& roots) {
    auto work = roots;
    std::unordered_set<SOMTParser::Node> visited;
    while (!work.empty()) {
        auto node = std::move(work.back()); work.pop_back();
        if (!node || !visited.insert(node).second) continue;
        const auto k = node->getKind();
        if (k == SOMTParser::NODE_KIND::NT_FORALL || k == SOMTParser::NODE_KIND::NT_EXISTS) return true;
        for (auto child : SOMTParser::children(node)) work.push_back(std::move(child));
    }
    return false;
}
Decision decide(const std::vector<SOMTParser::Node>& roots, Limits limits, EvidenceRequest evidence) {
    return detail::decide(roots, limits, evidence);
}
} // namespace xolver::pa
