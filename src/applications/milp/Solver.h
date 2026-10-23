#pragma once
#include "applications/Solver.h"
#include <gmpxx.h>
#include <optional>
#include <vector>
#include <string>
namespace xolver::applications::milp {
enum class VariableKind { Continuous, Integer, Binary };
struct Variable {std::string name;VariableKind kind=VariableKind::Continuous;std::optional<mpq_class> lower,upper;};
enum class Relation { LessEqual, Equal, GreaterEqual };
struct Constraint {std::vector<mpq_class> coefficients;Relation relation=Relation::LessEqual;mpq_class rhs=0;};
struct Problem {
    std::vector<Variable> variables;
    std::vector<Constraint> constraints;
    std::vector<mpq_class> objective;
    mpq_class objectiveOffset=0;
    bool maximize=false;
    std::size_t workLimit=2000000;
};
enum class Status { Optimal, Infeasible, Unbounded, Unknown, InvalidInput };
struct Answer {
    Status status=Status::Unknown;
    std::optional<mpq_class> objectiveValue;
    std::vector<mpq_class> assignment;
    std::string reason;
};
class Solver final : public TypedSolver<Problem,Answer> {
public:
    Family family() const noexcept override{return Family::Milp;}
    std::string_view name() const noexcept override{return "milp";}
    Answer solve(const Problem&) override;
};
}
