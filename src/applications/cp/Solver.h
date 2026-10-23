#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
namespace xolver::applications::cp {
struct Domain {
    enum class Kind { Unrestricted, Enumeration, Interval };
    std::shared_ptr<SOMTParser::DAGNode> variable;
    Kind kind=Kind::Unrestricted;
    NativeAssertions values;
    std::shared_ptr<SOMTParser::DAGNode> lower,upper;
};
struct Problem {NativeAssertions constraints;std::vector<Domain> domains;std::vector<NativeAssertions> allDifferent;};
// Oracle injection keeps application families independent. Domain/global
// constraints compile to native formulas, preserving their declared semantics.
class Solver final : public TypedSolver<Problem,SolverAnswer> {
    DecisionOracle decide_;
public:
    explicit Solver(DecisionOracle decide):decide_(std::move(decide)){}
    Family family() const noexcept override {return Family::Cp;}
    std::string_view name() const noexcept override {return "cp";}
    SolverAnswer solve(const Problem&) override;
};
}
