#pragma once

#include "ir/NativeTerms.h"
#include <cstddef>
#include <functional>
#include <optional>
#include <unordered_map>

namespace xolver {

// Interpret Boolean structure under stable, possibly incomplete atom knowledge.
// Unknown atoms stay unknown under negation. The DAG and callback must keep the
// same interpretation for this object's lifetime; create a new evaluator when
// assignments, candidate domains or query scopes change.
class PartialBooleanEvaluation {
public:
    using Truth = std::optional<bool>;
    using AtomValue = std::function<Truth(ExprId)>;

    PartialBooleanEvaluation(const NativeTerms& terms, AtomValue atoms);
    Truth evaluate(ExprId root);
    std::size_t evaluatedNodes() const { return values_.size(); }

private:
    const NativeTerms& terms_;
    AtomValue atoms_;
    std::unordered_map<ExprId, Truth> values_;
};

} // namespace xolver
