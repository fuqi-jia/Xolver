#pragma once

#include "search/linear/LinearAtomManager.h"
#include <chrono>
#include <memory>
#include <optional>
#include <span>
#include <unordered_map>
#include <vector>

namespace xolver {

struct LinearProbeAssumption {
    LinearFormKey lhs;
    Relation relation = Relation::Eq;
    mpq_class rhs;
    SatLit reason;
};

struct LinearProbeModel {
    std::unordered_map<std::string, DeltaRational> assignments;
    mpq_class delta;
};

class LinearProbeResult {
public:
    LinearProbeResult();
    ~LinearProbeResult();
    LinearProbeResult(LinearProbeResult&&) noexcept;
    LinearProbeResult& operator=(LinearProbeResult&&) noexcept;

    GeneralSimplex::Result status = GeneralSimplex::Result::Unknown;
    // Asserted-true source/assumption literals whose conjunction is impossible.
    // Disequality branches are combined by case analysis, not one Farkas sum.
    std::vector<SatLit> conflictReasons;
    std::size_t simplexChecks = 0;
    std::size_t disequalityBranches = 0;
    std::size_t tableauCopies = 0;

    // Materialize the owned witness only when requested. A refutation caller
    // need not build and discard all variable names and exact model values.
    std::optional<LinearProbeModel> model() const;

private:
    struct State;
    std::shared_ptr<State> state_;
    friend class LinearAssumptionProber;
};

// Retains an independent pivot basis and query-only definitions. Every probe
// replaces its complete bound base, so weakening, withdrawal and changed
// reasons cannot reuse a previous query's assumptions. Equation changes refresh
// the snapshot. Results retain immutable witnesses through copy-on-write.
class LinearAssumptionProber {
public:
    LinearProbeResult probe(
        const GeneralSimplex& source, const LinearAtomManager& manager,
        std::span<const LinearProbeAssumption> assumptions,
        std::chrono::steady_clock::time_point deadline =
            std::chrono::steady_clock::time_point::max());
    void reset() noexcept { state_.reset(); definitions_.reset(); }

private:
    std::shared_ptr<LinearProbeResult::State> state_;
    std::shared_ptr<const void> definitions_;
};

// The manager must describe the supplied simplex's symbols and auxiliary forms.
// All registration, assertions and search happen in an isolated copy. SAT means
// a feasible real linear relaxation, not integer/nonlinear satisfiability.
// Substituting the witness's delta in its exact assignments preserves the
// copied bounds, including strict disequality branches. UNSAT reasons are owned
// and refer to the supplied literals. Only the caller's deadline limits search.
LinearProbeResult probeLinearAssumptions(
    const GeneralSimplex& source, const LinearAtomManager& manager,
    std::span<const LinearProbeAssumption> assumptions,
    std::chrono::steady_clock::time_point deadline =
        std::chrono::steady_clock::time_point::max());

} // namespace xolver
