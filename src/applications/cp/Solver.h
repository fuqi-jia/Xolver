#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
namespace xolver::applications::cp {
struct Domain {
    enum class Kind { Unrestricted, Enumeration, Interval };
    std::shared_ptr<SOMTParser::DAGNode> variable;
    Kind kind = Kind::Unrestricted;
    NativeAssertions values;
    std::shared_ptr<SOMTParser::DAGNode> lower, upper;
};
struct Table {
    NativeAssertions variables;
    std::vector<NativeAssertions> tuples;
    bool allowed = true;
};
struct Element {
    std::shared_ptr<SOMTParser::DAGNode> index, value;
    NativeAssertions entries;
    long indexBase = 0;
};
struct Cardinality {
    NativeAssertions propositions;
    std::optional<std::size_t> lower, upper;
};
struct Problem {
    NativeAssertions constraints;
    std::vector<Domain> domains;
    std::vector<NativeAssertions> allDifferent;
    std::vector<Table> tables;
    std::vector<Element> elements;
    std::vector<Cardinality> cardinalities;
};
// Oracle injection keeps application families independent. Domain/global
// constraints compile to native formulas, preserving their declared semantics.
class Solver final : public TypedSolver<Problem, SolverAnswer> {
    DecisionOracle decide_;
    std::size_t workLimit_;

  public:
    explicit Solver(DecisionOracle decide, std::size_t workLimit = 2000000)
        : decide_(std::move(decide)), workLimit_(workLimit) {}
    Family family() const noexcept override { return Family::Cp; }
    std::string_view name() const noexcept override { return "cp"; }
    SolverAnswer solve(const Problem &) override;
};
} // namespace xolver::applications::cp
