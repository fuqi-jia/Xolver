#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
namespace xolver::applications::de {
enum class Kind { Ode, Pde };
struct Jet {
    std::shared_ptr<SOMTParser::DAGNode> symbol;
    std::size_t field = 0;
    std::vector<unsigned> order;
    // Empty means the problem's coordinates. Explicit arguments express
    // initial/boundary data, e.g. y(0), y'(0), or u(0,t).
    NativeAssertions arguments;
};
struct Equation {
    NativeAssertions assumptions;
    std::shared_ptr<SOMTParser::DAGNode> formula;
};
struct Problem {
    NativeAssertions coordinates;
    NativeAssertions parameters;
    std::vector<std::string> fields;
    std::vector<Jet> jets;
    std::vector<Equation> equations;
};
struct Options {
    unsigned polynomialDegree = 2;
    std::size_t monomialLimit = 128;
    quantifiers::Limits limits;
};
enum class Status { Solved, NoSolution, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    // Native expressions in coordinates/parameters, one per field. Solved
    // means these expressions satisfy every obligation, not uniqueness.
    NativeAssertions functions;
    std::string reason;
};
class Solver : public TypedSolver<Problem, Answer> {
    Kind kind_;
    Options options_;

  public:
    explicit Solver(Kind kind, Options options = {}) : kind_(kind), options_(options) {}
    Family family() const noexcept override { return Family::DifferentialEquations; }
    std::string_view name() const noexcept override { return kind_ == Kind::Ode ? "ode" : "pde"; }
    Answer solve(const Problem &) override;
};
} // namespace xolver::applications::de
