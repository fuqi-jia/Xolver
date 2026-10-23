#pragma once
#include "applications/sv/verification/Solver.h"
#include "ir/NativeSubstitution.h"

namespace xolver::applications::sv::verification::detail {
// Shared state scoping and time-indexing for verification algorithms only.
class Transition {
    const TransitionSystem &system_;
    std::set<native::Node> stateSymbols_, transitionSymbols_;
    std::vector<std::map<native::Node, native::Node>> stateMemo_, transitionMemo_;
    void validate(native::Node, const std::set<native::Node> &, std::set<native::Node> bound = {});

  public:
    native::Nodes nodes;
    std::vector<NativeAssertions> states, inputs;
    Transition(const TransitionSystem &, const NativeAssertions &extra, std::size_t workLimit);
    void statePredicate(native::Node);
    native::Node at(native::Node, std::size_t frame, bool transition = false);
    NativeAssertions at(const NativeAssertions &, std::size_t frame, bool transition = false);
    native::Node next(native::Node);
    native::Node simplePath(std::size_t depth);
};
} // namespace xolver::applications::sv::verification::detail
