#pragma once

#include "base/WorkBudget.h"
#include "contracts/LinearFormKey.h"
#include "contracts/SatSolver.h"
#include <functional>
#include <optional>

namespace xolver {

struct ExplainedLinearBound {
    mpq_class value;
    bool strict = false;
    std::vector<SatLit> reasons;
};

struct LinearBoundRow {
    LinearFormKey lhs;
    Relation rel;
    mpq_class rhs;
    std::vector<SatLit> reasons;
};

enum class LinearBoundUpdate { Unchanged, Changed, Conflict };

struct LinearBoundPropagationResult {
    size_t updates = 0;
    bool conflict = false;
    bool exhausted = false;
};

// Exact interval propagation shared by arithmetic clients. Rows already carry
// their asserted polarity. All row/endpoint explanations must be complete and
// nonempty. The sink owns bounds and detects conflicts; only strict progress
// may return Changed. Partial progress remains valid after budget exhaustion.
class LinearBoundPropagation {
public:
    using Lookup = std::function<std::optional<ExplainedLinearBound>(const std::string&, bool lower)>;
    using Update = std::function<LinearBoundUpdate(const std::string&, bool lower,
                                                  const ExplainedLinearBound&)>;
    using IsInteger = std::function<bool(const std::string&)>;

    static LinearBoundPropagationResult run(const std::vector<LinearBoundRow>& rows,
        const Lookup& lookup, const Update& update, const IsInteger& isInteger,
        WorkBudget& budget);
};

} // namespace xolver
