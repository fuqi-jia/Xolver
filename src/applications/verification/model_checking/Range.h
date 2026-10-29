#pragma once
#include "applications/verification/model_checking/Solver.h"
#include "search/arith/IntegerBounds.h"

namespace xolver::applications::verification::model_checking {
// Integer bounds justified by mandatory conjuncts of the original assumptions.
// Native symbol identities and assumption identities are part of the contract.
using RangeBound = integer_bounds::Bound;
using RangeCertificate = integer_bounds::Certificate;
struct RangeAnswer {
    Status status = Status::Unknown;
    std::optional<RangeCertificate> certificate;
    std::string reason;
    std::size_t work = 0;
};
// Proves sufficient integer interval conditions. It never manufactures a SAT
// model or treats an open interval calculation as an invalid obligation.
// Div/mod retain SMT-LIB Euclidean semantics; clients lower C/Rocq arithmetic.
class RangeSolver final : public TypedSolver<Obligation, RangeAnswer> {
    std::size_t workLimit_;

  public:
    explicit RangeSolver(std::size_t workLimit = 2000000) : workLimit_(workLimit) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "integer-range-proof"; }
    RangeAnswer solve(const Obligation &) override;
};
struct RangeCertificateProblem {
    Obligation obligation;
    RangeCertificate certificate;
};
class RangeCertificateSolver final : public TypedSolver<RangeCertificateProblem, RangeAnswer> {
    std::size_t workLimit_;

  public:
    explicit RangeCertificateSolver(std::size_t workLimit = 2000000) : workLimit_(workLimit) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "integer-range-certificate"; }
    RangeAnswer solve(const RangeCertificateProblem &) override;
};
enum class VerificationMethod { Interval, DecisionOracle };
struct RangeAssistedAnswer : Answer {
    VerificationMethod method = VerificationMethod::DecisionOracle;
    std::optional<RangeCertificate> certificate;
    std::size_t intervalWork = 0;
};
// Application composition: replay a sufficient range proof, otherwise submit
// the unchanged obligation to the injected oracle. SAT models come only from
// the oracle. The interval work limit applies to each proof/check phase.
class RangeAssistedSolver final : public TypedSolver<Obligation, RangeAssistedAnswer> {
    DecisionOracle decide_;
    std::size_t workLimit_;

  public:
    explicit RangeAssistedSolver(DecisionOracle decide, std::size_t workLimit = 2000000)
        : decide_(std::move(decide)), workLimit_(workLimit) {}
    Family family() const noexcept override { return Family::SoftwareVerification; }
    std::string_view name() const noexcept override { return "range-assisted-verification"; }
    RangeAssistedAnswer solve(const Obligation &) override;
};
} // namespace xolver::applications::verification::model_checking
