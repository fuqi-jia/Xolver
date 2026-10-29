#pragma once

#include "applications/Solver.h"
#include "contracts/SatSolver.h"
#include <chrono>
#include <functional>
#include <unordered_map>

namespace xolver::applications::satisfiability::sat {

using Clause = std::vector<int>;
struct Problem {
    // DIMACS indices, starting at one; zero infers the range from the input.
    std::size_t variables = 0;
    std::vector<Clause> clauses;
    Clause assumptions;
    int conflicts = 0, decisions = 0; // Zero means unlimited.
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
};
enum class Status { Sat, Unsat, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    // Only referenced variables need entries; unmentioned variables are free.
    std::unordered_map<unsigned, bool> assignment;
    Clause failedAssumptions;
    std::string reason;
};

class Solver final : public TypedSolver<Problem, Answer> {
public:
    using Factory = std::function<std::unique_ptr<SatSolver>()>;
    explicit Solver(Factory factory = createSatSolver) : factory_(std::move(factory)) {}
    Family family() const noexcept override { return Family::Sat; }
    std::string_view name() const noexcept override { return "sat"; }
    Answer solve(const Problem&) override;
private:
    Factory factory_;
};

} // namespace xolver::applications::satisfiability::sat
