#pragma once

#include "search/refute/SignDefinitenessRefuter.h"
#include "search/lra/GeneralSimplex.h"
#include "base/WorkBudget.h"
#include <chrono>
#include <map>
#include <unordered_map>

namespace xolver {

struct PolynomialLinearStatistics {
    size_t constraints = 0;
    size_t variables = 0;
    size_t newRows = 0;
    size_t reusedRows = 0;
    size_t retainedRows = 0;
    bool exhausted = false;
};

// Refute a polynomial assignment by an exact linear relaxation over the reals.
// Each distinct canonical monomial is an unconstrained shared column. This is
// also sound for integer clients; no integrality or product identities are
// assumed. Disequalities are omitted. Feasibility establishes no SAT result.
// Returned literals are the original premises of an exact Simplex conflict.
// Definitions are unconditional s = polynomial equations and survive between
// checks. Every check replaces the complete explained bound base. Call reset
// before reusing variable IDs for a different problem.
class PolynomialLinearRefuter {
public:
    explicit PolynomialLinearRefuter(size_t workLimit = 100000) : workLimit_(workLimit) {}
    std::optional<std::vector<SatLit>> check(
        const std::vector<SignRefuteConstraint>&,
        std::chrono::steady_clock::time_point deadline,
        PolynomialLinearStatistics* = nullptr);
    void reset();
    // Project the current relaxation point onto original variables, completing
    // variables without degree-one columns with zero. This is an UNTRUSTED
    // candidate, even after a feasible relaxation: the caller must check every
    // original constraint, integrality and interface condition before accepting it.
    std::optional<std::unordered_map<VarId, mpq_class>> projectCandidate(
        const std::vector<SignRefuteConstraint>&, WorkBudget&) const;

private:
    struct Row { RationalPolynomial polynomial; int variable; };
    size_t workLimit_;
    GeneralSimplex simplex_;
    std::map<MonomialKey, int> variables_;
    // A source may change polynomial as well as polarity. Compare its entire
    // polynomial before reusing a definition; identity alone is insufficient.
    std::unordered_map<SatVar, Row> rows_;
};

} // namespace xolver
