#pragma once
#include "applications/verification/model_checking/ModelChecking.h"

namespace xolver::applications::verification::model_checking {
// Computes exact symbolic images and returns the reached region as an
// inductive invariant when transition closure is proved. No invariant template
// is required. Quantified image queries follow the injected oracle's contract.
class ReachabilitySolver final : public TypedSolver<TransitionSystem, SafetyAnswer> {
    DecisionOracle decide_;
    CheckLimits limits_;

  public:
    explicit ReachabilitySolver(DecisionOracle decide, CheckLimits limits = {})
        : decide_(std::move(decide)), limits_(limits) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "symbolic-reachability"; }
    SafetyAnswer solve(const TransitionSystem &) override;
};
} // namespace xolver::applications::verification::model_checking
