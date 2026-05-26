#pragma once

#include "DeltaRational.h"
#include "SparseTableau.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <optional>
#include <unordered_map>
#include <deque>
#include <unordered_set>
#include <cassert>

namespace zolver {

// ---------------------------------------------------------------------------
// BoundValue: -inf, finite, or +inf
// ---------------------------------------------------------------------------
enum class BoundKind { NegInf, Finite, PosInf };

struct BoundValue {
    BoundKind kind;
    DeltaRational value;  // valid only if kind == Finite

    BoundValue() : kind(BoundKind::PosInf) {}
    explicit BoundValue(const DeltaRational& v) : kind(BoundKind::Finite), value(v) {}

    static BoundValue negInf() { BoundValue v; v.kind = BoundKind::NegInf; return v; }
    static BoundValue posInf() { BoundValue v; v.kind = BoundKind::PosInf; return v; }

    bool isFinite() const { return kind == BoundKind::Finite; }
    bool isNegInf() const { return kind == BoundKind::NegInf; }
    bool isPosInf() const { return kind == BoundKind::PosInf; }

    bool operator<(const BoundValue& rhs) const;
    bool operator>(const BoundValue& rhs) const;
    bool operator<=(const BoundValue& rhs) const;
    bool operator>=(const BoundValue& rhs) const;
};

// ---------------------------------------------------------------------------
// BoundInfo: bound value + optional reason literal
// ---------------------------------------------------------------------------
struct BoundInfo {
    BoundValue bound;
    std::optional<SatLit> reason;  // valid only for finite bounds

    BoundInfo() : bound(BoundValue::posInf()) {}
    explicit BoundInfo(const BoundValue& b) : bound(b) {}
    BoundInfo(const BoundValue& b, SatLit r) : bound(b), reason(r) {}
};

// ---------------------------------------------------------------------------
// GeneralSimplex: Dutertre-de Moura incremental LRA feasibility solver
// ---------------------------------------------------------------------------
class GeneralSimplex {
public:
    GeneralSimplex();

    // -------------------------------------------------------------------------
    // Variable / constraint registration (before any check)
    // -------------------------------------------------------------------------

    /** Add an original (problem) variable. Returns its index. */
    int addVar(const std::string& name);

    /** Add a linear constraint: p(x) ~ c where p(x) = sum a_j * x_j.
     *  Internally creates auxiliary var s = p(x) - c and a tableau row.
     *  Returns the auxiliary var index, or -1 on error.
     *
     *  Semantic contract (preserved from dense version):
     *    addConstraint(terms, rhs) creates aux s with
     *        s = -rhs + Σ terms[i].coeff * terms[i].var
     *    So s = 0  <=>  Σ terms[i].coeff * terms[i].var = rhs
     */
    int addConstraint(const std::vector<std::pair<int, mpq_class>>& terms,
                      const mpq_class& rhs);

    // -------------------------------------------------------------------------
    // Incremental bound assertion
    // -------------------------------------------------------------------------

    /** Assert lower bound. Must be finite with valid reason.
     *  Returns false if immediate bound conflict (lower > upper). */
    bool assertLower(int var, const BoundInfo& info, int level = 0);

    /** Assert upper bound. Must be finite with valid reason.
     *  Returns false if immediate bound conflict (upper < lower). */
    bool assertUpper(int var, const BoundInfo& info, int level = 0);

    /** Backtrack to target decision level. */
    void backtrackToLevel(int level);

    // -------------------------------------------------------------------------
    // Solving
    // -------------------------------------------------------------------------

    enum class Result { Sat, Unsat, Unknown };

    /** Check feasibility under current bounds. */
    Result check();

    /** Whether an immediate bound conflict was recorded by assertLower/Upper. */
    bool hasImmediateConflict() const { return hasImmediateConflict_; }

    /** Get current assignment (valid after Sat). */
    DeltaRational value(int var) const;

    /**
     * Compute a single concrete δ > 0 such that substituting it into every
     * variable's DeltaRational value (a + bδ) keeps all active bounds
     * satisfied (Dutertre & de Moura 2006). Valid after Sat. Used to turn
     * the symbolic-infinitesimal model into a concrete rational model for
     * get-model output. Returns a positive rational; 1 if unconstrained.
     */
    mpq_class computeSafeDelta() const;

    // -------------------------------------------------------------------------
    // Conflict explanation (valid after Unsat)
    // -------------------------------------------------------------------------

    struct BoundReason {
        int var;
        bool isLower;
        SatLit reason;
    };

    /** Return the set of bounds that caused the last conflict. */
    const std::vector<BoundReason>& getConflict() const { return conflict_; }

    // -------------------------------------------------------------------------
    // Scope management (push/pop)
    // -------------------------------------------------------------------------

    void push();
    void pop();

    // -------------------------------------------------------------------------
    // Reset
    // -------------------------------------------------------------------------

    /** Reset active bounds to (-inf, +inf). Keeps tableau. */
    void resetActiveBounds();

    /** Full reset: clears everything including tableau. */
    void reset();

    // -------------------------------------------------------------------------
    // Diagnostics
    // -------------------------------------------------------------------------
    int numVars() const { return static_cast<int>(vars_.size()); }
    int numRows() const { return tab_.numRows(); }
    bool isBasic(int var) const;

    /** Get the name of a variable (original or auxiliary). */
    const std::string& varName(int var) const { return vars_[var].name; }

    /** Return value if lower == upper (fixed), else nullopt. */
    std::optional<DeltaRational> fixedValue(int var) const;

    /** Return bound reasons that fix the variable (lower == upper). */
    std::vector<BoundReason> explainFixedValue(int var) const;

    /** Recursively prove that a variable is fixed by tableau row propagation.
     *  Returns the fixed value and collected bound reasons, or nullopt.
     */
    std::optional<std::pair<DeltaRational, std::vector<BoundReason>>> proveFixedValue(int var) const;

    // -------------------------------------------------------------------------
    // Read-only accessors for bound propagation / conflict explanation
    // -------------------------------------------------------------------------

    const SparseTableau& tableau() const { return tab_; }

    struct VarStateView {
        const std::string& name;
        int basicRow;   // -1 if non-basic
        const BoundInfo& lower;
        const BoundInfo& upper;
    };

    int basicRowOfVar(int var) const {
        assert(var >= 0 && var < static_cast<int>(vars_.size()));
        return vars_[var].basicRow;
    }

    VarStateView varState(int var) const {
        assert(var >= 0 && var < static_cast<int>(vars_.size()));
        const auto& v = vars_[var];
        return VarStateView{v.name, v.basicRow, v.lower, v.upper};
    }

    // -------------------------------------------------------------------------
    // Debug / testing interface
    // -------------------------------------------------------------------------
    /** Verify all sparse tableau invariants. Returns true, or asserts in debug. */
    bool debugCheckInvariants() const;

#ifdef ZOLVER_LRA_PROFILE
    int pivotCount() const { return pivotCount_; }
    void resetPivotCount() { pivotCount_ = 0; }
#endif

private:
    // ========================================================================
    // Variable state
    // ========================================================================
    struct VarState {
        std::string name;
        int basicRow = -1;   // -1 means non-basic
        BoundInfo lower;
        BoundInfo upper;
        DeltaRational beta;
    };

    std::vector<VarState> vars_;

    // ========================================================================
    // Sparse indexed tableau
    // ========================================================================
    SparseTableau tab_;

    // row -> basic var
    std::vector<int> basicVars_;

    // non-basic variable set with O(1) membership and update
    std::vector<int> nonBasicVars_;
    std::vector<int> nonBasicPos_;  // var -> index in nonBasicVars_, -1 if basic

    // ========================================================================
    // Violation queue (lazy)
    // ========================================================================
    std::deque<int> violatedQueue_;
    std::vector<bool> inViolationQueue_;

    // ========================================================================
    // Other state
    // ========================================================================
    bool betaDirty_ = true;
    std::vector<BoundReason> conflict_;
    bool hasImmediateConflict_ = false;

    // ZOLVER_LRA_PIVOT_HEUR: when set, use a largest-|coefficient| entering-var
    // heuristic (with Bland fallback) instead of Bland-only. Read once at
    // construction. Sound regardless of value (pivot choice never changes the
    // verdict); only affects the search path / pivot count.
    bool useHeuristicPivot_ = false;

#ifdef ZOLVER_LRA_PROFILE
    int pivotCount_ = 0;
#endif

    // ========================================================================
    // Trail for push/pop / level-aware backtracking
    // ========================================================================
    struct TrailEntry {
        int level;
        int var;
        bool isLower;
        BoundInfo oldBound;
    };
    std::vector<TrailEntry> trail_;
    std::vector<size_t> scopeStack_;

    // ========================================================================
    // Linear form for rewriteToNonBasic
    // ========================================================================
    struct LinearForm {
        mpq_class constant;
        std::vector<std::pair<int, mpq_class>> terms;  // var, coeff
    };

    // ========================================================================
    // Invariants (debug only)
    // ========================================================================
    void checkInvariants() const;

    // ========================================================================
    // Basis helpers
    // ========================================================================
    void makeBasicWithoutPivot(int var, int row);
    void markBasicSwitch(int leaving, int entering);
    void removeFromNonBasic(int var);

    LinearForm rewriteToNonBasic(const LinearForm& input);

    // ========================================================================
    // Beta computation and helpers
    // ========================================================================
    void recomputeBeta();
    DeltaRational chooseValueWithinBounds(int var) const;

    // Violation checks
    bool violatesLower(int var) const;
    bool violatesUpper(int var) const;
    bool canIncrease(int var) const;
    bool canDecrease(int var) const;
    bool atLower(int var) const;
    bool atUpper(int var) const;

    // Violation queue
    void refreshViolationStatus(int var);
    int pickViolatedBasic();
    void rebuildViolationQueue();

    // Core check loop
    Result checkInternal();

    // Find entering var for violated basic var. When useBland is true, the
    // smallest-index (Bland) rule is used (guarantees termination); otherwise a
    // largest-|coefficient| heuristic is used (ZOLVER_LRA_PIVOT_HEUR).
    int findEnteringVarToIncrease(int basicVar, bool useBland) const;
    int findEnteringVarToDecrease(int basicVar, bool useBland) const;

    // Pivot: entering (non-basic) replaces leaving (basic)
    void pivotAndUpdate(int leavingBasic, int enteringNonBasic, const DeltaRational& target);
    void pivot(int leaving, int entering);

    // Update beta for non-basic var change
    void update(int nonBasicVar, const DeltaRational& value);

    // Conflict explanation
    void explainLowerConflict(int basicVar);
    void explainUpperConflict(int basicVar);
    void explainImmediateConflict(int var, bool newBoundIsLower, SatLit newReason);

    // Row of a basic var
    int rowOfBasic(int var) const;

    std::optional<std::pair<DeltaRational, std::vector<BoundReason>>>
    proveFixedValueImpl(int var, std::unordered_set<int>& visited) const;

#ifdef ZOLVER_LRA_PROFILE
public:
    struct CoeffStats {
        int64_t mpqOpTimeUs = 0;
        int maxCoeffNumBits = 0;
        int maxCoeffDenBits = 0;
        int64_t totalCoeffNumBits = 0;
        int64_t totalCoeffDenBits = 0;
        int64_t totalCoeffSamples = 0;

        void reset() {
            mpqOpTimeUs = 0;
            maxCoeffNumBits = 0;
            maxCoeffDenBits = 0;
            totalCoeffNumBits = 0;
            totalCoeffDenBits = 0;
            totalCoeffSamples = 0;
        }
    };

    const CoeffStats& coeffStats() const { return coeffStats_; }
    void resetCoeffStats() { coeffStats_.reset(); }

private:
    mutable CoeffStats coeffStats_;
#endif
};

} // namespace zolver
