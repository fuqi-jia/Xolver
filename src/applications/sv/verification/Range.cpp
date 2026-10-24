#include "applications/sv/verification/Range.h"
namespace xolver::applications::sv::verification {
RangeAnswer RangeSolver::solve(const Obligation &o) {
    auto proof = integer_bounds::prove(o.assumptions, o.conclusion, workLimit_);
    RangeAnswer answer;
    answer.status = proof.status == integer_bounds::ProofStatus::Proved    ? Status::Valid
                    : proof.status == integer_bounds::ProofStatus::Invalid ? Status::InvalidInput
                                                                           : Status::Unknown;
    answer.certificate = std::move(proof.certificate);
    answer.reason = std::move(proof.reason);
    answer.work = proof.work;
    return answer;
}
RangeAnswer RangeCertificateSolver::solve(const RangeCertificateProblem &p) {
    auto proof = integer_bounds::check(p.obligation.assumptions, p.obligation.conclusion,
                                       p.certificate, workLimit_);
    RangeAnswer answer;
    answer.status = proof.status == integer_bounds::ProofStatus::Proved    ? Status::Valid
                    : proof.status == integer_bounds::ProofStatus::Invalid ? Status::Invalid
                                                                           : Status::Unknown;
    answer.reason = std::move(proof.reason);
    answer.work = proof.work;
    return answer;
}
RangeAssistedAnswer RangeAssistedSolver::solve(const Obligation &o) {
    RangeAssistedAnswer answer;
    auto interval = RangeSolver(workLimit_).solve(o);
    answer.intervalWork = interval.work;
    if (interval.status == Status::InvalidInput) {
        answer.status = interval.status;
        answer.reason = interval.reason;
        return answer;
    }
    if (interval.status == Status::Valid && interval.certificate) {
        auto replay = RangeCertificateSolver(workLimit_).solve({o, *interval.certificate});
        answer.intervalWork += replay.work;
        if (replay.status == Status::Valid) {
            answer.status = Status::Valid;
            answer.method = VerificationMethod::Interval;
            answer.certificate = std::move(interval.certificate);
            return answer;
        }
    }
    static_cast<Answer &>(answer) = verification::Solver(decide_).solve({{o}});
    return answer;
}
} // namespace xolver::applications::sv::verification
