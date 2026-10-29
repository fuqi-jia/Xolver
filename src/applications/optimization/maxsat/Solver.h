#pragma once

#include "applications/optimization/maxsmt/Solver.h"
#include <cstddef>
#include <utility>
#include <vector>

namespace xolver::applications::optimization::maxsat {

// DIMACS literals: positive/negative variable indices, starting at one.
using Clause = std::vector<int>;
struct SoftClause {
    Clause literals;
    mpq_class weight = 1;
    std::string label;
};
using Limits = maxsmt::Limits;
using Status = maxsmt::Status;
using Answer = maxsmt::Answer;
struct Problem {
    // Zero infers the range. A positive count bounds referenced variables;
    // unused variables require no allocation.
    std::size_t variables = 0;
    std::vector<Clause> hard;
    std::vector<SoftClause> soft;
    Limits limits;
};

// Propositional-clause frontend to the exact weighted optimization engine.
class Solver final : public TypedSolver<Problem, Answer> {
    DecisionOracle decide_;
public:
    explicit Solver(DecisionOracle decide) : decide_(std::move(decide)) {}
    Family family() const noexcept override { return Family::MaxSat; }
    std::string_view name() const noexcept override { return "maxsat"; }
    Answer solve(const Problem&) override;
};

} // namespace xolver::applications::optimization::maxsat
