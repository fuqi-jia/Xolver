#pragma once

#include "expr/types.h"
#include <memory>
#include <vector>

namespace xolver {

/**
 * SAT literal: signed variable.
 * Positive = var true, Negative = var false.
 */
struct SatLit {
    SatVar var = 0;
    bool sign = true;

    SatLit() = default;
    SatLit(SatVar v, bool s) : var(v), sign(s) {}

    static SatLit positive(SatVar v) { return {v, true}; }
    static SatLit negative(SatVar v) { return {v, false}; }
    SatLit negated() const { return {var, !sign}; }

    bool operator==(const SatLit& other) const { return var == other.var && sign == other.sign; }
    bool operator!=(const SatLit& other) const { return !(*this == other); }
};

/**
 * Abstract SAT solver interface.
 *
 * CaDiCaL wrapper — the only supported SAT backend.
 */
class SatSolver {
public:
    virtual ~SatSolver() = default;

    virtual SatVar newVar() = 0;
    virtual void addClause(const std::vector<SatLit>& clause) = 0;

    enum class SolveResult { Sat, Unsat, Unknown };
    virtual SolveResult solve() = 0;
    virtual SolveResult solve(const std::vector<SatLit>& assumptions) = 0;

    virtual bool value(SatVar v) const = 0;
    virtual bool configure(const char* name, int64_t value) { (void)name; (void)value; return false; }

    // Per-solve resource limit (e.g. "conflicts", "decisions"). Bounds the NEXT
    // solve() so a single hard instance cannot consume an unbounded budget; a
    // solve that hits the limit returns Unknown. Default no-op (returns false).
    virtual bool limit(const char* name, int value) { (void)name; (void)value; return false; }

    // Assumption / unsat-core support
    virtual std::vector<SatLit> getFailedAssumptions() const { return {}; }

    // Observed variable support (for CaDiCaL ExternalPropagator)
    virtual void addObservedVar(SatVar /*v*/) {}

    // Force the DEFAULT decision phase of a variable (search heuristic only —
    // never changes satisfiability). Used by Nelson-Oppen combination to default
    // shared-equality atoms to FALSE (the "all-distinct" arrangement), so the SAT
    // core stops freely guessing interface equalities. Default no-op.
    virtual void setDefaultPhase(SatVar /*v*/, bool /*value*/) {}
};

/**
 * Factory: creates the best available SAT backend.
 */
std::unique_ptr<SatSolver> createSatSolver();

} // namespace xolver
