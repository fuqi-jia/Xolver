#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
#include <gmpxx.h>
namespace xolver::applications::omt {
enum class Direction { Minimize, Maximize };
enum class Order { Arithmetic, UnsignedBitVector, SignedBitVector };
enum class Priority { Lexicographic, Pareto, Independent };
struct Objective {
    std::shared_ptr<SOMTParser::DAGNode> expression;
    Direction direction = Direction::Minimize;
    Order order = Order::Arithmetic;
};
struct Problem {
    NativeAssertions assertions;
    std::vector<Objective> objectives;
    Priority priority = Priority::Lexicographic;
    quantifiers::Limits limits;
};
enum class Status { Optimal, Infeasible, InfimumNotAttained, Unbounded, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    std::vector<RealValue> objectiveValues;
    std::optional<TheoryModel> model;
    std::string reason;
};
class Solver final : public TypedSolver<Problem, Answer> {
  public:
    Family family() const noexcept override { return Family::Omt; }
    std::string_view name() const noexcept override { return "omt"; }
    Answer solve(const Problem &) override;
};
} // namespace xolver::applications::omt
