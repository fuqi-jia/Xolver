#pragma once

#include "ir/NativeTerms.h"

namespace xolver {

// Exact key for analyses of immutable indexed expressions and assertion roots.
// Own this with the derived analysis, never in a process/thread-global cache.
// SAT trails, solver settings and mutable theory metadata need separate keys.
class AssertionSnapshot {
public:
    AssertionSnapshot() = default;
    explicit AssertionSnapshot(const NativeTerms& terms)
        : identity_(terms.expressionIndexIdentity()),
          assertions_(terms.getScopedAssertions()) {}

    bool matches(const NativeTerms& terms) const {
        return identity_ && identity_ == terms.expressionIndexIdentity()
            && assertions_ == terms.getScopedAssertions();
    }

private:
    std::shared_ptr<const void> identity_;
    std::vector<std::pair<ScopeLevel, ExprId>> assertions_;
};

} // namespace xolver
