#pragma once

#include "DeltaRational.h"
#include "sat/SatSolver.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <optional>
#include <unordered_map>

namespace nlcolver {

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
     */
    int addConstraint(const std::vector<std::pair<int, mpq_class>>& terms,
                      const mpq_class& rhs);

    // -------------------------------------------------------------------------
    // Incremental bound assertion
    // -------------------------------------------------------------------------

    /** Assert lower bound. Must be finite with valid reason. */
    bool assertLower(int var, const BoundInfo& info);

    /** Assert upper bound. Must be finite with valid reason. */
    bool assertUpper(int var, const BoundInfo& info);

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

    // -------------------------------------------------------------------------
    // Conflict explanation (valid after Unsat)
    // -------------------------------------------------------------------------

    struct BoundReason {
        int var;
        bool isLower;
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
    int numRows() const { return numRows_; }
    bool isBasic(int var) const;

private:
    // -------------------------------------------------------------------------
    // Variable info
    // -------------------------------------------------------------------------
    struct VarInfo {
        std::string name;
    };
    std::vector<VarInfo> vars_;

    // -------------------------------------------------------------------------
    // Tableau state (persistent)
    // -------------------------------------------------------------------------
    // Row r:  basicVars_[r] = rhs_[r] + sum_j matrix_[r][j] * x_j
    // matrix_[r][j] is meaningful for non-basic vars only.
    std::vector<std::vector<mpq_class>> matrix_;  // m x n
    std::vector<mpq_class> rhs_;                  // m
    std::vector<int> basicVars_;                  // m
    std::vector<bool> isBasic_;                   // n
    int numRows_ = 0;
    int numCols_ = 0;

    // Current assignment
    std::vector<DeltaRational> beta_;
    bool betaDirty_ = true;

    // Bounds
    std::vector<BoundInfo> lower_;
    std::vector<BoundInfo> upper_;

    // Conflict
    std::vector<BoundReason> conflict_;
    bool hasImmediateConflict_ = false;

    // -------------------------------------------------------------------------
    // Trail for push/pop
    // -------------------------------------------------------------------------
    struct TrailEntry {
        int var;
        bool isLower;
        BoundInfo oldBound;
    };
    std::vector<std::vector<TrailEntry>> trail_;

    // -------------------------------------------------------------------------
    // Internal helpers
    // -------------------------------------------------------------------------
    void buildInitialTableau(const std::vector<std::vector<std::pair<int, mpq_class>>>& allTerms,
                             const std::vector<mpq_class>& allRhs);
    void refactorizeTableau();  // Gauss-Jordan: basic columns -> identity
    void recomputeBeta();
    DeltaRational chooseValueWithinBounds(int var) const;

    // Violation checks
    bool violatesLower(int var) const;
    bool violatesUpper(int var) const;
    bool canIncrease(int var) const;
    bool canDecrease(int var) const;
    bool atLower(int var) const;
    bool atUpper(int var) const;

    // Core check loop
    Result checkInternal();

    // Find a basic variable that violates its bounds. Returns var index or -1.
    int findViolatedBasicVar() const;

    // Find entering var for violated basic var
    int findEnteringVarToIncrease(int basicVar) const;
    int findEnteringVarToDecrease(int basicVar) const;

    // Pivot: entering (non-basic) replaces leaving (basic)
    void pivotAndUpdate(int leavingBasic, int enteringNonBasic, const DeltaRational& target);
    void pivot(int leaving, int entering);

    // Update beta for non-basic var change
    void update(int nonBasicVar, const DeltaRational& value);

    // Conflict explanation
    void explainLowerConflict(int basicVar);
    void explainUpperConflict(int basicVar);
    void explainImmediateConflict(int var, bool newBoundIsLower);

    // Row of a basic var
    int rowOfBasic(int var) const;
};

} // namespace nlcolver
