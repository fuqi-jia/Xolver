#pragma once

#include "theory/arith/lra/GeneralSimplex.h"
#include "expr/types.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace zolver {

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
    // Drop the active constraint set but KEEP variables and the simplex tableau
    // rows (cached by constraint form). Lets a CDCL(T) caller re-specify the
    // active constraints each check() without recreating rows/vars every time
    // — the expensive part. Bounds are still fully re-asserted on the next
    // solve(), so the verdict is identical to a clear()+rebuild.
    void resetConstraints();
    int addVar(std::string_view name, VarKind kind);

    void addConstraint(const LinearConstraint& c);
    // Pre-declare a row form (terms+rhs) WITHOUT making it an active constraint.
    // Used to front-load all atom rows on a clean basis so later checks avoid
    // clean rebuilds. The rel/reason are irrelevant to the row (set by the
    // active constraint when its bound is asserted).
    void registerForm(const std::vector<std::pair<int, mpq_class>>& terms,
                      const mpq_class& rhs);

    MilpResult solve(MilpMode mode);

    int numVars() const { return static_cast<int>(varNames_.size()); }
    mpq_class value(int var) const;          // real part only (for branching)
    // Concrete value with the infinitesimal δ instantiated to a safe
    // positive rational — for model extraction, so strict bounds (x < r)
    // are reflected as plain rationals rather than collapsing the δ part.
    mpq_class concreteValue(int var) const;
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
    // Cache: constraint form (terms + rhs) -> simplex aux/row index. A row is
    // created in the simplex once per distinct form and reused across solves;
    // resetActiveBounds() (start of every solveLpRelaxation) keeps rows, so the
    // cached aux stays valid. Cleared only by clear(), not resetConstraints().
    std::unordered_map<std::string, int> rowCache_;
    // Every distinct form ever seen (monotonic), so a clean rebuild can recreate
    // all rows on a fresh basis. knownFormKeys_ dedups insertions into allForms_.
    std::vector<LinearConstraint> allForms_;
    std::unordered_set<std::string> knownFormKeys_;
    // SOUNDNESS: GeneralSimplex::addConstraint must run on a CLEAN (un-pivoted)
    // basis. `clean_` is true only right after a full reset, before any check()
    // pivots. If a NEW form appears while the basis is dirty, we defer row
    // creation: needsRebuild_ triggers a clean reset+recreate-all before the next
    // solve(). Creating a row mid-solve on a dirty basis corrupts the tableau
    // (observed as a false UNSAT on QF_LIRA/smtopt).
    bool clean_ = true;
    bool needsRebuild_ = false;
    static std::string formKey(const LinearConstraint& c);
    void noteForm(const LinearConstraint& c);
    void rebuildOnCleanBasis();
    int getOrCreateRow(const LinearConstraint& c);

    // Fast mode budget
    static constexpr int FAST_BRANCH_BUDGET = 100;

    MilpResult solveLpRelaxation();
    MilpResult checkIntegrality(bool useBudget, int& budget);
    MilpResult dfsCheckIntegrality(bool useBudget, int& budget);
    int findBestFractionalVar(mpq_class& outFrac) const;
    void computeFloorCeil(const DeltaRational& val, mpq_class& floorVal, mpq_class& ceilVal) const;
};

} // namespace zolver
