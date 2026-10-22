#pragma once
#include "applications/Solver.h"
#include "contracts/SolverAnswer.h"
#include "contracts/IntegerArithmetic.h"
#include <functional>

namespace xolver::applications::smt {
struct Problem {
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> assertions;
    pa::Limits integerLimits;
    pa::EvidenceRequest integerEvidence;
};
class Solver final : public TypedSolver<Problem, SolverAnswer> {
public:
    // The stateful incremental CDCL(T) session is supplied by the runtime.
    // This callback is used only after the quantifier/spatial boundary check.
    using GroundSolve = std::function<SolverAnswer(const Problem&)>;
    explicit Solver(GroundSolve ground) : ground_(std::move(ground)) {}
    Family family() const noexcept override { return Family::Smt; }
    std::string_view name() const noexcept override { return "smt"; }
    SolverAnswer solve(const Problem&) override;
private:
    GroundSolve ground_;
};
} // namespace xolver::applications::smt
