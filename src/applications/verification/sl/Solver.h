#pragma once
#include "contracts/SolverAnswer.h"
#include "applications/Solver.h"
#include "applications/verification/sl/NativeInductive.h"

namespace xolver::sl {
enum class RecursiveSemantics { Equations, LeastFixedPoint };
// This is an explicit SL problem, not an arbitrary SMT formula that happens to
// describe memory. A frontend must preserve the declared recursive semantics.
struct Request {
    std::shared_ptr<SOMTParser::Sort> location, data;
    std::vector<std::shared_ptr<SOMTParser::DAGNode>> assertions, declarations;
    std::vector<InductiveDefinition> definitions;
    RecursiveSemantics recursion = RecursiveSemantics::Equations;
    std::vector<PredicateInvariant> invariantCandidates;
};
SolverAnswer solve(const Request&, Limits = {});
class Solver final : public applications::TypedSolver<Request, SolverAnswer> {
    Limits limits;
public:
    explicit Solver(Limits l = {}) : limits(l) {}
    applications::Family family() const noexcept override {
        return applications::Family::SoftwareVerification;
    }
    std::string_view name() const noexcept override { return "sl"; }
    SolverAnswer solve(const Request& request) override;
};
} // namespace xolver::sl
