#pragma once
#include "applications/Solver.h"
#include "contracts/DecisionOracle.h"
#include "quantifiers/Resources.h"
#include <gmpxx.h>
namespace xolver::applications::counting {
struct Problem {
    NativeAssertions assertions;
    // Include unused declarations explicitly. Other free symbols are existential;
    // an empty tuple has cardinality zero or one.
    NativeAssertions projection;
    quantifiers::Limits limits;
};
enum class Status { Exact, Infinite, Unknown, InvalidInput };
struct Answer {
    Status status = Status::Unknown;
    mpz_class count = 0;
    std::string reason;
};
class Solver final : public TypedSolver<Problem, Answer> {
  public:
    Family family() const noexcept override { return Family::Counting; }
    std::string_view name() const noexcept override { return "counting"; }
    Answer solve(const Problem &) override;
};
} // namespace xolver::applications::counting
