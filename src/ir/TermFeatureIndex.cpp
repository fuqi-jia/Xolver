#include "ir/TermFeatureIndex.h"
#include "base/WorkBudget.h"
#include <stdexcept>

namespace xolver {

uint64_t TermFeatureIndex::bit(Kind kind) {
    // Extending Kind cannot silently turn a present operator into an absence.
    static_assert(static_cast<unsigned>(Kind::BoundVariable) < 64);
    const auto index = static_cast<unsigned>(kind);
    if (index >= 64) throw std::out_of_range("operator exceeds term feature word");
    return uint64_t(1) << index;
}

uint64_t TermFeatureIndex::summarize(ExprId root) {
    if (root == NullExpr) return 0;
    if (root == TrueSentinelExpr || root == FalseSentinelExpr) return bit(Kind::ConstBool);
    if (summaries_.at(root)) return summaries_[root];
    struct Frame { ExprId id; TermExpr node; size_t next = 0; };
    std::vector<Frame> pending;
    pending.push_back({root, terms_.get(root)});
    WorkBudget deadline(0);
    while (!pending.empty()) {
        auto& frame = pending.back();
        if (frame.next < frame.node.children.size()) {
            const auto child = frame.node.children[frame.next++];
            if (!summaries_.at(child)) pending.push_back({child, terms_.get(child)});
        } else {
            uint64_t mask = bit(frame.node.kind);
            for (auto child : frame.node.children) mask |= summaries_[child];
            summaries_[frame.id] = mask;
            pending.pop_back();
            if ((++visitedNodes_ & 255) == 0) deadline.tick(256);
        }
    }
    return summaries_[root];
}

bool TermFeatureIndex::containsAny(std::span<const ExprId> roots,
    std::initializer_list<Kind> kinds) {
    WorkBudget deadline(0);
    deadline.tick();
    uint64_t requested = 0;
    for (auto kind : kinds) requested |= bit(kind);
    if (!requested || roots.empty()) return false;
    const auto identity = terms_.expressionIndexIdentity();
    if (identity_ != identity) {
        summaries_.clear();
        identity_ = identity;
    }
    summaries_.resize(terms_.size());
    for (auto root : roots)
        if (summarize(root) & requested) return true;
    return false;
}

} // namespace xolver
