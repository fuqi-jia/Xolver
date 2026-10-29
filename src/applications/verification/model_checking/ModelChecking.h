#pragma once
#include "applications/verification/model_checking/Solver.h"

namespace xolver::applications::verification::model_checking {
struct InferenceProblem {
    TransitionSystem system;
    NativeAssertions candidates;
};
enum class InferenceStatus { Inductive, Unknown, InvalidInput };
struct InferenceAnswer {
    InferenceStatus status = InferenceStatus::Unknown;
    NativeAssertions invariant;
    std::vector<std::size_t> retained, refuted, undecided;
    std::vector<Obligation> obligations;
    std::string reason;
};
struct CheckLimits {
    std::size_t depth = 32, work = 2000000, queries = 10000;
};
class InferenceSolver final : public TypedSolver<InferenceProblem, InferenceAnswer> {
    DecisionOracle decide_;
    CheckLimits limits_;

  public:
    explicit InferenceSolver(DecisionOracle decide, CheckLimits limits = {})
        : decide_(std::move(decide)), limits_(limits) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "houdini-invariants"; }
    InferenceAnswer solve(const InferenceProblem &) override;
};
struct SafetyProblem {
    TransitionSystem system;
    NativeAssertions candidates;
};
enum class SafetyStatus { Safe, Unsafe, Unknown, InvalidInput };
enum class SafetyProof { Invariant, KInduction, ReachabilityDiameter };
struct SafetyCertificate {
    SafetyProof kind = SafetyProof::Invariant;
    std::size_t depth = 0;
    NativeAssertions invariant;
};
struct Counterexample {
    // Frames correspond to system.state; inputs are independently fresh per edge.
    std::vector<NativeAssertions> states, inputs;
    NativeAssertions query;
    std::optional<TheoryModel> model;
};
struct SafetyAnswer {
    SafetyStatus status = SafetyStatus::Unknown;
    std::optional<std::size_t> checkedDepth;
    std::optional<Counterexample> counterexample;
    std::optional<SafetyCertificate> certificate;
    std::size_t queries = 0;
    std::string reason;
};
enum class SafetyMethod { Bounded, Induction };
class SafetySolver final : public TypedSolver<SafetyProblem, SafetyAnswer> {
    DecisionOracle decide_;
    CheckLimits limits_;
    SafetyMethod method_;

  public:
    explicit SafetySolver(DecisionOracle decide, CheckLimits limits = {},
                          SafetyMethod method = SafetyMethod::Induction)
        : decide_(std::move(decide)), limits_(limits), method_(method) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "transition-safety"; }
    SafetyAnswer solve(const SafetyProblem &) override;
};
struct CertificateProblem {
    TransitionSystem system;
    SafetyCertificate certificate;
};
// Rebuilds obligations from the system and certificate; no cached SAT verdicts.
class CertificateSolver final : public TypedSolver<CertificateProblem, Answer> {
    DecisionOracle decide_;
    CheckLimits limits_;

  public:
    explicit CertificateSolver(DecisionOracle decide, CheckLimits limits = {})
        : decide_(std::move(decide)), limits_(limits) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "safety-certificate"; }
    Answer solve(const CertificateProblem &) override;
};
} // namespace xolver::applications::verification::model_checking
