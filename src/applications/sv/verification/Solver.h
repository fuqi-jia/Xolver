#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
namespace xolver::applications::sv::verification {
struct Obligation {
    std::string name;
    NativeAssertions assumptions;
    std::shared_ptr<SOMTParser::DAGNode> conclusion;
};
struct Problem {
    std::vector<Obligation> obligations;
};
enum class Status { Valid, Invalid, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    std::size_t obligation = 0;
    std::optional<TheoryModel> counterexample;
    std::string reason;
};
// Program frontends supply state, memory and arithmetic semantics explicitly.
class Solver final : public TypedSolver<Problem, Answer> {
    DecisionOracle decide_;

  public:
    explicit Solver(DecisionOracle decide) : decide_(std::move(decide)) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "verification-conditions"; }
    Answer solve(const Problem &) override;
};
} // namespace xolver::applications::sv::verification
