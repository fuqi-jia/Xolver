#pragma once

#include "ir/NativeTerms.h"
#include <cstdint>
#include <initializer_list>
#include <span>

namespace xolver {

// Operator summaries for an immutable expression DAG. Queries use their
// current roots, so allocated but inactive nodes never keep a feature active.
// Newly appended expressions reuse summaries of their unchanged children.
class TermFeatureIndex {
public:
    explicit TermFeatureIndex(const NativeTerms& terms) : terms_(terms) {}
    bool containsAny(std::span<const ExprId> roots, std::initializer_list<Kind> kinds);
    uint64_t visitedNodes() const { return visitedNodes_; }

private:
    uint64_t summarize(ExprId root);
    static uint64_t bit(Kind kind);
    const NativeTerms& terms_;
    std::shared_ptr<const void> identity_;
    std::vector<uint64_t> summaries_;
    uint64_t visitedNodes_ = 0;
};

} // namespace xolver
