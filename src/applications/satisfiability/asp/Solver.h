#pragma once

#include "applications/Solver.h"
#include "applications/satisfiability/asp/Program.h"
#include "contracts/SatSolver.h"
#include <functional>
#include <optional>
#include <stop_token>
#include <unordered_map>

namespace xolver::applications::satisfiability::asp {

struct Limits {
    std::size_t formulaWork = 10000000;
    std::size_t satCalls = 100000;
    std::uint64_t satVariables = 2000000;
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max();
    std::stop_token stop;
};
struct Problem {
    Program program;
    Limits limits;
};
enum class Status { Sat, Optimal, Unsat, Unknown, InvalidInput, Unsupported };
struct Answer {
    Status status = Status::Unknown;
    // Present only after independent checking of a stable model. Unknown may
    // retain an incumbent; it must not be treated as an optimality claim.
    std::optional<std::vector<Atom>> model;
    std::vector<Atom> atomIds; // Universe for complete independent witness replay.
    std::vector<std::string> shown;
    std::vector<std::int64_t> priorities;
    std::vector<mpz_class> costs;
    std::size_t provedLevels = 0;
    std::size_t satCalls = 0, unfoundedCuts = 0;
    std::string reason;
};

class Solver final : public TypedSolver<Problem, Answer> {
public:
    using Factory = std::function<std::unique_ptr<SatSolver>()>;
    explicit Solver(Factory factory = createSatSolver) : factory_(std::move(factory)) {}
    Family family() const noexcept override { return Family::Asp; }
    std::string_view name() const noexcept override { return "asp"; }
    Answer solve(const Problem&) override;
private:
    Factory factory_;
};

} // namespace xolver::applications::satisfiability::asp
