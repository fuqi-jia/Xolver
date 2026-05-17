#pragma once

#include "expr/types.h"
#include <memory>
#include <vector>

namespace nlcolver {

/**
 * SAT literal: signed variable.
 * Positive = var true, Negative = var false.
 */
struct SatLit {
    SatVar var;
    bool sign;

    static SatLit positive(SatVar v) { return {v, true}; }
    static SatLit negative(SatVar v) { return {v, false}; }
    SatLit negated() const { return {var, !sign}; }

    bool operator==(const SatLit& other) const { return var == other.var && sign == other.sign; }
    bool operator!=(const SatLit& other) const { return !(*this == other); }
};

/**
 * Abstract SAT solver interface.
 *
 * P0: Stub implementation (no CaDiCaL).
 * P1: CaDiCaL wrapper when library is available.
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

    // Assumption / unsat-core support
    virtual std::vector<SatLit> getFailedAssumptions() const { return {}; }

    // Observed variable support (for CaDiCaL ExternalPropagator)
    virtual void addObservedVar(SatVar /*v*/) {}
};

/**
 * Factory: creates the best available SAT backend.
 */
std::unique_ptr<SatSolver> createSatSolver();

} // namespace nlcolver
