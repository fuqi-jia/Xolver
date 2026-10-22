#pragma once
#include "contracts/SolverAnswer.h"
#include "ir/NativeFeatures.h"
#include <span>

namespace xolver::logic::first_order {
using Roots = std::vector<std::shared_ptr<SOMTParser::DAGNode>>;
// Applications provide theory capabilities. The logical layer cannot include
// or construct an application, and has no implicit PA/SL or ground fallback.
class Backend {
public:
    virtual ~Backend() = default;
    // Features are only a coarse profile. A backend must also be able to
    // inspect actual sorts/operators (e.g. QBF versus integers, BV versus arrays).
    virtual bool accepts(const Roots&, const NativeFeatures&) const = 0;
    virtual SolverAnswer solve(const Roots&) = 0;
};
SolverAnswer solve(const Roots&, std::span<Backend* const>);
} // namespace xolver::logic::first_order
