#pragma once
#include <string_view>

namespace xolver::applications {
enum class Family { Smt, Omt, Cp, Milp, DifferentialEquations, SoftwareVerification, Counting, MaxSmt, MaxSat, Sat, Asp };
enum class Category { Satisfiability, Optimization, Counting, Verification, Dynamics };

// Common lifetime and identity for application solvers. Theory callbacks,
// simplex, quantifier projection and SAT search are implementation components,
// not applications, and do not depend on this interface.
class Solver {
public:
    virtual ~Solver() = default;
    virtual Family family() const noexcept = 0;
    virtual std::string_view name() const noexcept = 0;
    Category category() const noexcept {
        switch (family()) {
            case Family::Sat: case Family::Smt: case Family::Asp: return Category::Satisfiability;
            case Family::Omt: case Family::Cp: case Family::Milp:
            case Family::MaxSmt: case Family::MaxSat: return Category::Optimization;
            case Family::Counting: return Category::Counting;
            case Family::SoftwareVerification: return Category::Verification;
            case Family::DifferentialEquations: return Category::Dynamics;
        }
        return Category::Satisfiability;
    }
};

// C++ cannot have virtual function templates. A typed abstract specialization
// supplies solve() while preserving the common non-template Solver base.
// Each application owns its input/output semantics; an optimum or a count is
// never encoded as an SMT satisfiability result.
template<class Input, class Output>
class TypedSolver : public Solver {
public:
    using InputType = Input;
    using OutputType = Output;
    virtual Output solve(const Input&) = 0;
};
} // namespace xolver::applications
