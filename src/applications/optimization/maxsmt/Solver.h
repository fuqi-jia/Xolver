#pragma once

#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
#include <cstddef>
#include <gmpxx.h>
#include <optional>
#include <stop_token>
#include <string>
#include <utility>
#include <vector>

namespace xolver::applications::optimization::maxsmt {

struct SoftConstraint {
    std::shared_ptr<SOMTParser::DAGNode> formula;
    mpq_class weight = 1; // Exact nonnegative rational penalty when false.
    std::string label;
};

struct Limits {
    std::size_t oracleCalls = 10000;
    std::size_t states = 100000;
    std::size_t formulaWork = 2000000;
    std::stop_token stop;
    // Numeric zero means unlimited, as in the existing application work limits.
};

struct Problem {
    NativeAssertions hard;
    std::vector<SoftConstraint> soft;
    Limits limits;
};

enum class Status { Optimal, Infeasible, Unknown, InvalidInput };

struct Answer {
    Status status = Status::Unknown;
    // A cost on Unknown is only a feasible incumbent, never an optimum.
    std::optional<mpq_class> cost;
    mpq_class lowerBound = 0;
    std::vector<std::size_t> violatedSoft;
    std::optional<TheoryModel> model;
    std::size_t oracleCalls = 0;
    std::size_t generatedStates = 0;
    std::string reason;
};

// Inject any theory-capable decision backend. Each query is a complete native
// assertion snapshot; the backend need not implement optimization or models.
class Solver final : public TypedSolver<Problem, Answer> {
    DecisionOracle decide_;

public:
    explicit Solver(DecisionOracle decide) : decide_(std::move(decide)) {}
    Family family() const noexcept override { return Family::MaxSmt; }
    std::string_view name() const noexcept override { return "maxsmt"; }
    Answer solve(const Problem&) override;
};

} // namespace xolver::applications::optimization::maxsmt
