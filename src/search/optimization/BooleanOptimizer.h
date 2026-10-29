#pragma once

#include "search/bitblast/PseudoBooleanEncoder.h"
#include <functional>
#include <map>
#include <string>

namespace xolver::optimization {

struct BooleanObjective {
    std::int64_t priority = 0; // Higher priorities are minimized first.
    std::vector<bitblast::WeightedLiteral> terms;
};
struct BooleanOptimum {
    enum class Status { Optimal, Infeasible, Unknown } status = Status::Unknown;
    // Ordered by decreasing priority. Costs describe an incumbent on Unknown.
    std::vector<std::int64_t> priorities;
    std::vector<mpz_class> costs;
    std::size_t provedLevels = 0;
    bool hasIncumbent = false;
    std::string reason;
};

// The feasibility callback can enforce additional semantics (for example ASP
// stability) before returning Sat. ReadValue reads the latest valid candidate;
// Publish retains its witness after the entire cost vector is evaluated.
// All clauses added here are
// objective bounds; the caller owns the SAT instance and the witness lifetime.
using BooleanCheck = std::function<SatSolver::SolveResult(const std::vector<SatLit>&)>;
using BooleanValue = std::function<bool(SatLit)>;
// Publish the candidate atomically. If it throws, the previous published
// witness must remain unchanged. This runs only after complete cost evaluation.
using BooleanPublish = std::function<void()>;
BooleanOptimum minimizeBooleanLex(bitblast::BitBlastEncoder&, WorkBudget&,
    const std::vector<BooleanObjective>&, const BooleanCheck&, const BooleanValue&,
    const BooleanPublish&,
    std::chrono::steady_clock::time_point deadline = std::chrono::steady_clock::time_point::max());

} // namespace xolver::optimization
