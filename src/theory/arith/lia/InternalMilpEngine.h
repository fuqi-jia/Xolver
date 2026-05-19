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
 * The core is one branch-and-cut solver with different solve policies:
 *   - RelaxationOnly: LP relaxation only, ignores integrality.
 *   - Budgeted:       LP relaxation + bounded branch-and-bound.
 *                     May return NeedBranch with fractional var info.
 *   - Complete:       LP relaxation + exhaustive branch-and-bound.
 */
class InternalMilpEngine {
public:
    enum class VarKind { Int, Real };

    struct LinearConstraint {
        std::vector<std::pair<int, mpq_class>> terms; // var index -> coeff
        mpq_class rhs;
        Relation rel; // Eq, Leq, Lt, Geq, Gt (NOT Neq)
        SatLit reason; // SAT literal that activated this constraint
    };

    enum class MilpMode {
        RelaxationOnly,
        Budgeted,
        Complete
    };

    struct MilpResult {
        enum class Kind { Sat, Unsat, Unknown, NeedBranch };
        Kind kind;
        // Populated when kind == NeedBranch
        int branchVar = -1;
        mpq_class floorVal;
        mpq_class ceilVal;
    };

    void clear();
    int addVar(std::string_view name, VarKind kind);

    void addConstraint(const LinearConstraint& c);

    MilpResult solve(MilpMode mode);

    int numVars() const { return static_cast<int>(varNames_.size()); }
    mpq_class value(int var) const;
    DeltaRational deltaValue(int var) const;
    std::string_view varName(int var) const;

    void push();
    void pop();

    /** Return the set of SAT reasons from the last simplex conflict.
     *  Empty if no conflict has occurred since last solve().
     *  Dummy reasons (var==0) from internal branching bounds are filtered out.
     */
    std::vector<SatLit> getConflictReasons() const;

private:
    GeneralSimplex simplex_;
    std::vector<std::string> varNames_;
    std::vector<VarKind> varKinds_;
    std::vector<LinearConstraint> constraints_;
    std::unordered_set<int> integerVars_;

    // Fast mode budget
    static constexpr int FAST_BRANCH_BUDGET = 100;

    MilpResult solveLpRelaxation();
    MilpResult checkIntegrality(bool useBudget, int& budget);
    MilpResult dfsCheckIntegrality(bool useBudget, int& budget);
    int findBestFractionalVar(mpq_class& outFrac) const;
    void computeFloorCeil(const DeltaRational& val, mpq_class& floorVal, mpq_class& ceilVal) const;
};

} // namespace nlcolver
