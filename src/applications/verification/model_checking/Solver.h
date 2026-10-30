#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
namespace xolver::applications::verification::model_checking {
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
    // Fresh nondeterministic inputs for each transition; never state predicates.
    NativeAssertions inputs;
};
enum class Status { Valid, Invalid, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    std::size_t obligation = 0;
    std::optional<TheoryModel> counterexample;
    std::string reason;
};
struct ContextAnswer {
    // The independent verdict for the assumptions, including any model/proof.
    // Unknown does not prevent proving the implication in a second query.
    SolverAnswer context;
    Answer implication;
    std::size_t queries = 0;
};
// Distinguishes an infeasible context from a reachable, valid obligation.
// An UNSAT context makes the implication vacuously valid and needs one query;
// otherwise the second snapshot refutes assumptions AND NOT conclusion.
class ContextSolver final : public TypedSolver<Obligation, ContextAnswer> {
    DecisionOracle decide_;

  public:
    explicit ContextSolver(DecisionOracle decide) : decide_(std::move(decide)) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "context-verification"; }
    ContextAnswer solve(const Obligation &) override;
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
} // namespace xolver::applications::verification::model_checking
