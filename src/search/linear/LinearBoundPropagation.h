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

struct LinearAggregateConflict {
    // Positive multipliers of source inequalities, after orienting >= and >
    // as <= and <. Their exact sum has zero lhs and a contradictory rhs.
    std::vector<std::pair<size_t, mpq_class>> multipliers;
    mpq_class rhs;
    bool strict = false;
    std::vector<SatLit> reasons;
};

// Exact interval propagation shared by arithmetic clients. Rows already carry
// their asserted polarity. All row/endpoint explanations must be complete;
// an empty set denotes an unconditional fact. Lookup must omit unexplained
// endpoints. The sink owns bounds and detects conflicts; only strict progress
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

    // Cheap exact refutation before interval propagation or Boolean search.
    // Sum non-univariate inequalities with unit or scale-normalizing weights;
    // single-variable rows remain the interval engine's responsibility. A
    // result carries a checkable linear-combination certificate. No result
    // means no conclusion, including when work is exhausted. All source rows
    // must already have their asserted polarity and complete explanations.
    static std::optional<LinearAggregateConflict> aggregateConflict(
        const std::vector<LinearBoundRow>& rows, WorkBudget& budget);
};

} // namespace xolver
