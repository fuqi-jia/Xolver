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
struct TransitionSystem {
    // Each pair is (current state, next state), with identical sorts.
    std::vector<
        std::pair<std::shared_ptr<SOMTParser::DAGNode>, std::shared_ptr<SOMTParser::DAGNode>>>
        state;
    NativeAssertions initial, transition;
    std::shared_ptr<SOMTParser::DAGNode> invariant, safety;
    NativeAssertions parameters;
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
class InvariantSolver final : public TypedSolver<TransitionSystem, Answer> {
    DecisionOracle decide_;
    std::size_t workLimit_;

  public:
    explicit InvariantSolver(DecisionOracle decide, std::size_t workLimit = 2000000)
        : decide_(std::move(decide)), workLimit_(workLimit) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "inductive-invariant"; }
    // Obligation indices: 0 initiation, 1 consecution, 2 safety.
    Answer solve(const TransitionSystem &) override;
};
} // namespace xolver::applications::sv::verification
