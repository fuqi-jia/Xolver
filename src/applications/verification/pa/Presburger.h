#pragma once
#include "contracts/IntegerArithmetic.h"
#include "applications/Solver.h"

namespace xolver::pa {
// Exact decision procedure for Boolean combinations of integer affine atoms,
// constant nonzero div/mod (including left-associative n-ary div), indexed
// positive-constant divisibility, integer ite/abs, and arbitrary Int/Bool
// quantifier alternation.
// Free integer/Boolean variables are existentially closed. Unsupported terms
// and exhausted limits produce Unknown. Zero work/residue limits mean unlimited.
// Model reconstruction shares the resource limits. If it exhausts them after a
// decision, SAT remains valid but modelAvailable is false. Trace recording is optional.
Decision decide(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&,
                Limits = {}, EvidenceRequest = {});
bool hasQuantifiers(const std::vector<std::shared_ptr<SOMTParser::DAGNode>>&);
using Problem = std::vector<std::shared_ptr<SOMTParser::DAGNode>>;
class Solver final : public applications::TypedSolver<Problem, Decision> {
    Limits limits;
    EvidenceRequest evidence;
public:
    explicit Solver(Limits l = {}, EvidenceRequest e = {}) : limits(l), evidence(e) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "pa"; }
    Decision solve(const Problem&) override;
};
} // namespace xolver::pa
