#pragma once

#include "theory/arith/lra/GeneralSimplex.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <unordered_set>

namespace nlcolver {

/**
 * InternalMilpEngine: Mixed Integer-Linear Programming engine without CDCL coupling.
 *
 * Used by LiraSolver (complete fallback) and NiraSolver (relaxation).
 *
 * checkComplete() reuses the same GeneralSimplex + branch-and-bound core as
 * LiaSolver, but without SatLit/Registry/Lemma dependencies.
 */
class InternalMilpEngine {
public:
    enum class VarKind { Int, Real };

    struct LinearConstraint {
        std::vector<std::pair<int, mpq_class>> terms; // var index -> coeff
        mpq_class rhs;
        Relation rel; // Eq, Le, Lt, Ge, Gt (NOT Neq)
    };

    enum class Result { Sat, Unsat, Unknown };

    void clear();
    int addVar(std::string_view name, VarKind kind);

    void addConstraint(const LinearConstraint& c);

    // Exact LP relaxation (ignores integrality)
    Result checkRelaxation();

    // Branch/cut with budget, may return Unknown
    Result checkFast();

    // Complete check (no artificial branch budget)
    // Completeness is bounded by the underlying GeneralSimplex + branch-and-cut capability.
    Result checkComplete();

    mpq_class value(int var) const;

private:
    GeneralSimplex simplex_;
    std::vector<std::string> varNames_;
    std::vector<VarKind> varKinds_;
    std::vector<LinearConstraint> constraints_;
    std::unordered_set<int> integerVars_;

    // Fast mode budget
    static constexpr int FAST_BRANCH_BUDGET = 100;

    Result solveLpRelaxation();
    Result checkIntegrality(bool useBudget);
    int findBestFractionalVar(mpq_class& outFrac) const;
};

} // namespace nlcolver
