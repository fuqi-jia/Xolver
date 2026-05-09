#include "theory/arith/lra/GeneralSimplex.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

// ============================================================================
// BoundValue comparison
// ============================================================================

bool BoundValue::operator<(const BoundValue& rhs) const {
    if (kind == BoundKind::NegInf) return rhs.kind != BoundKind::NegInf;
    if (kind == BoundKind::PosInf) return false;
    // this is finite
    if (rhs.kind == BoundKind::NegInf) return false;
    if (rhs.kind == BoundKind::PosInf) return true;
    return value < rhs.value;
}

bool BoundValue::operator>(const BoundValue& rhs) const {
    return rhs < *this;
}
bool BoundValue::operator<=(const BoundValue& rhs) const {
    return !(rhs < *this);
}
bool BoundValue::operator>=(const BoundValue& rhs) const {
    return !(*this < rhs);
}

// ============================================================================
// GeneralSimplex
// ============================================================================

GeneralSimplex::GeneralSimplex() {
    // Initialize base trail frame
    trail_.push_back({});
}

int GeneralSimplex::addVar(const std::string& name) {
    int id = static_cast<int>(vars_.size());
    vars_.push_back({name});
    lower_.push_back(BoundInfo(BoundValue::negInf()));
    upper_.push_back(BoundInfo(BoundValue::posInf()));
    beta_.push_back(DeltaRational(0));
    isBasic_.push_back(false);
    numCols_ = static_cast<int>(vars_.size());
    // Pad existing tableau rows with a zero column for the new variable.
    for (auto& row : matrix_) {
        row.push_back(mpq_class(0));
    }
    return id;
}

int GeneralSimplex::addConstraint(const std::vector<std::pair<int, mpq_class>>& terms,
                                  const mpq_class& rhs) {
    // Create auxiliary variable s
    int s = addVar("s" + std::to_string(numRows_));

    // Build tableau row: s = -rhs + sum terms_j * x_j
    // In matrix form: s - sum terms_j * x_j = -rhs
    // Tableau stores: s = rhs + sum matrix[r][j] * x_j
    // So matrix[r][j] = coeff (the original coefficient)
    std::vector<mpq_class> row(numCols_, 0);
    row[s] = 1;  // coefficient of s
    for (const auto& [var, coeff] : terms) {
        assert(var >= 0 && var < numCols_);
        row[var] = coeff;
    }
    matrix_.push_back(std::move(row));
    rhs_.push_back(-rhs);
    basicVars_.push_back(s);
    isBasic_[s] = true;
    numRows_++;
    return s;
}

// ============================================================================
// Bound assertion
// ============================================================================

bool GeneralSimplex::assertLower(int var, const BoundInfo& info) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < numCols_);

    if (info.bound <= lower_[var].bound) return true;  // not tighter
    if (info.bound > upper_[var].bound) {
        explainImmediateConflict(var, true);
        hasImmediateConflict_ = true;
        return false;   // conflict
    }

    trail_.back().push_back({var, true, lower_[var]});
    lower_[var] = info;

    if (!isBasic_[var] && violatesLower(var)) {
        update(var, info.bound.value);
    }
    return true;
}

bool GeneralSimplex::assertUpper(int var, const BoundInfo& info) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < numCols_);

    if (info.bound >= upper_[var].bound) return true;  // not tighter
    if (info.bound < lower_[var].bound) {
        explainImmediateConflict(var, false);
        hasImmediateConflict_ = true;
        return false;   // conflict
    }

    trail_.back().push_back({var, false, upper_[var]});
    upper_[var] = info;

    if (!isBasic_[var] && violatesUpper(var)) {
        update(var, info.bound.value);
    }
    return true;
}

// ============================================================================
// Beta computation and helpers
// ============================================================================

void GeneralSimplex::recomputeBeta() {
    // Non-basic vars: choose a value within bounds
    for (int j = 0; j < numCols_; ++j) {
        if (isBasic_[j]) continue;
        beta_[j] = chooseValueWithinBounds(j);
    }
    // Basic vars: compute from tableau
    for (int r = 0; r < numRows_; ++r) {
        int b = basicVars_[r];
        DeltaRational val = DeltaRational(rhs_[r]);
        for (int j = 0; j < numCols_; ++j) {
            if (isBasic_[j]) continue;
            if (matrix_[r][j] != 0) {
                val += matrix_[r][j] * beta_[j];
            }
        }
        beta_[b] = val;
    }
    betaDirty_ = false;
}

DeltaRational GeneralSimplex::chooseValueWithinBounds(int var) const {
    const auto& l = lower_[var].bound;
    const auto& u = upper_[var].bound;

    if (l.isFinite() && u.isFinite()) {
        DeltaRational mid = (l.value + u.value) / 2;
        if (mid >= l.value && mid <= u.value) return mid;
        return l.value;
    }
    if (l.isFinite()) return l.value;
    if (u.isFinite()) return u.value;
    return DeltaRational(0);
}

bool GeneralSimplex::violatesLower(int var) const {
    return lower_[var].bound.isFinite() && beta_[var] < lower_[var].bound.value;
}

bool GeneralSimplex::violatesUpper(int var) const {
    return upper_[var].bound.isFinite() && beta_[var] > upper_[var].bound.value;
}

bool GeneralSimplex::canIncrease(int var) const {
    return !upper_[var].bound.isFinite() || beta_[var] < upper_[var].bound.value;
}

bool GeneralSimplex::canDecrease(int var) const {
    return !lower_[var].bound.isFinite() || beta_[var] > lower_[var].bound.value;
}

bool GeneralSimplex::atLower(int var) const {
    return lower_[var].bound.isFinite() && beta_[var] == lower_[var].bound.value;
}

bool GeneralSimplex::atUpper(int var) const {
    return upper_[var].bound.isFinite() && beta_[var] == upper_[var].bound.value;
}

void GeneralSimplex::update(int nonBasicVar, const DeltaRational& value) {
    assert(!isBasic_[nonBasicVar]);
    DeltaRational delta = value - beta_[nonBasicVar];
    for (int r = 0; r < numRows_; ++r) {
        if (matrix_[r][nonBasicVar] != 0) {
            beta_[basicVars_[r]] += matrix_[r][nonBasicVar] * delta;
        }
    }
    beta_[nonBasicVar] = value;
}

// ============================================================================
// Check
// ============================================================================

GeneralSimplex::Result GeneralSimplex::check() {
    if (hasImmediateConflict_) {
        return Result::Unsat;
    }
    if (betaDirty_) {
        recomputeBeta();
        betaDirty_ = false;
    }
    return checkInternal();
}

GeneralSimplex::Result GeneralSimplex::checkInternal() {
    const int MAX_ITERATIONS = 10000;

    for (int iter = 0; iter < MAX_ITERATIONS; ++iter) {
        int xi = findViolatedBasicVar();
        if (xi == -1) {
            conflict_.clear();
            return Result::Sat;
        }

        if (violatesLower(xi)) {
            int xj = findEnteringVarToIncrease(xi);
            if (xj == -1) {
                explainLowerConflict(xi);
                return Result::Unsat;
            }
            pivotAndUpdate(xi, xj, lower_[xi].bound.value);
        } else if (violatesUpper(xi)) {
            int xj = findEnteringVarToDecrease(xi);
            if (xj == -1) {
                explainUpperConflict(xi);
                return Result::Unsat;
            }
            pivotAndUpdate(xi, xj, upper_[xi].bound.value);
        }
    }

    // Should not reach here with Bland's rule on rational LRA
    std::cerr << "[GeneralSimplex] Warning: iteration limit reached" << std::endl;
    conflict_.clear();
    return Result::Unknown;
}

int GeneralSimplex::findViolatedBasicVar() const {
    for (int r = 0; r < numRows_; ++r) {
        int b = basicVars_[r];
        if (violatesLower(b) || violatesUpper(b)) {
            return b;
        }
    }
    return -1;
}

int GeneralSimplex::findEnteringVarToIncrease(int basicVar) const {
    int r = rowOfBasic(basicVar);
    for (int j = 0; j < numCols_; ++j) {
        if (isBasic_[j]) continue;
        mpq_class a = matrix_[r][j];
        if (a > 0 && canIncrease(j)) return j;
        if (a < 0 && canDecrease(j)) return j;
    }
    return -1;
}

int GeneralSimplex::findEnteringVarToDecrease(int basicVar) const {
    int r = rowOfBasic(basicVar);
    for (int j = 0; j < numCols_; ++j) {
        if (isBasic_[j]) continue;
        mpq_class a = matrix_[r][j];
        if (a < 0 && canIncrease(j)) return j;
        if (a > 0 && canDecrease(j)) return j;
    }
    return -1;
}

// ============================================================================
// Pivot
// ============================================================================

void GeneralSimplex::pivotAndUpdate(int leavingBasic, int enteringNonBasic,
                                    const DeltaRational& target) {
    int r = rowOfBasic(leavingBasic);
    mpq_class aij = matrix_[r][enteringNonBasic];
    assert(aij != 0);

    DeltaRational theta = (target - beta_[leavingBasic]) / aij;

    // Update assignment
    beta_[leavingBasic] = target;
    beta_[enteringNonBasic] += theta;
    for (int k = 0; k < numRows_; ++k) {
        if (basicVars_[k] == leavingBasic) continue;
        if (matrix_[k][enteringNonBasic] != 0) {
            beta_[basicVars_[k]] += matrix_[k][enteringNonBasic] * theta;
        }
    }

    // Pivot in tableau
    pivot(leavingBasic, enteringNonBasic);
}

void GeneralSimplex::pivot(int leaving, int entering) {
    int r = rowOfBasic(leaving);
    mpq_class d = matrix_[r][entering];
    assert(d != 0);

    mpq_class inv_d = 1 / d;

    // Update row r: solve for entering var
    // x_entering = (x_leaving - rhs_r - sum_{k!=entering} a_rk * x_k) / d
    // But we want: x_entering = new_rhs + sum new_coeff * x_k
    // where new_coeff for leaving var is 1/d, others are -a_rk/d
    matrix_[r][entering] = inv_d;  // coefficient of leaving var
    rhs_[r] = -rhs_[r] * inv_d;
    for (int k = 0; k < numCols_; ++k) {
        if (k == entering) continue;
        matrix_[r][k] = -matrix_[r][k] * inv_d;
    }

    // Eliminate entering from all other rows
    for (int p = 0; p < numRows_; ++p) {
        if (p == r) continue;
        mpq_class a = matrix_[p][entering];
        if (a == 0) continue;
        // row_p -= a * row_r
        for (int k = 0; k < numCols_; ++k) {
            if (k == entering) continue;
            matrix_[p][k] -= a * matrix_[r][k];
        }
        rhs_[p] -= a * rhs_[r];
        matrix_[p][entering] = -a * matrix_[r][entering];  // = -a/d
    }

    // Update basic/non-basic tracking
    isBasic_[leaving] = false;
    isBasic_[entering] = true;
    basicVars_[r] = entering;
}

// ============================================================================
// Conflict explanation
// ============================================================================

void GeneralSimplex::explainLowerConflict(int basicVar) {
    conflict_.clear();
    int r = rowOfBasic(basicVar);

    assert(lower_[basicVar].bound.isFinite());
    assert(lower_[basicVar].reason.has_value());
    conflict_.push_back({basicVar, true});

    for (int j = 0; j < numCols_; ++j) {
        if (isBasic_[j]) continue;
        mpq_class a = matrix_[r][j];
        if (a > 0 && atUpper(j)) {
            assert(upper_[j].reason.has_value());
            conflict_.push_back({j, false});
        } else if (a < 0 && atLower(j)) {
            assert(lower_[j].reason.has_value());
            conflict_.push_back({j, true});
        }
    }
}

void GeneralSimplex::explainUpperConflict(int basicVar) {
    conflict_.clear();
    int r = rowOfBasic(basicVar);

    assert(upper_[basicVar].bound.isFinite());
    assert(upper_[basicVar].reason.has_value());
    conflict_.push_back({basicVar, false});

    for (int j = 0; j < numCols_; ++j) {
        if (isBasic_[j]) continue;
        mpq_class a = matrix_[r][j];
        if (a > 0 && atLower(j)) {
            assert(lower_[j].reason.has_value());
            conflict_.push_back({j, true});
        } else if (a < 0 && atUpper(j)) {
            assert(upper_[j].reason.has_value());
            conflict_.push_back({j, false});
        }
    }
}

void GeneralSimplex::explainImmediateConflict(int var, bool newBoundIsLower) {
    conflict_.clear();
    // The conflicting bounds are the new bound (which has a reason) and
    // the opposing existing bound (which also has a reason).
    if (newBoundIsLower) {
        assert(lower_[var].bound.isFinite() || true);  // new lower is finite by contract
        assert(upper_[var].bound.isFinite());
        assert(upper_[var].reason.has_value());
        conflict_.push_back({var, true});   // the new lower bound
        conflict_.push_back({var, false});  // the existing upper bound
    } else {
        assert(upper_[var].bound.isFinite() || true);  // new upper is finite by contract
        assert(lower_[var].bound.isFinite());
        assert(lower_[var].reason.has_value());
        conflict_.push_back({var, false});  // the new upper bound
        conflict_.push_back({var, true});   // the existing lower bound
    }
}

// ============================================================================
// Scope management
// ============================================================================

void GeneralSimplex::push() {
    trail_.push_back({});
}

void GeneralSimplex::pop() {
    assert(!trail_.empty());
    auto& entries = trail_.back();
    for (auto it = entries.rbegin(); it != entries.rend(); ++it) {
        if (it->isLower) lower_[it->var] = it->oldBound;
        else             upper_[it->var] = it->oldBound;
    }
    trail_.pop_back();
    betaDirty_ = true;
}

// ============================================================================
// Reset
// ============================================================================

void GeneralSimplex::resetActiveBounds() {
    for (int i = 0; i < numCols_; ++i) {
        lower_[i] = BoundInfo(BoundValue::negInf());
        upper_[i] = BoundInfo(BoundValue::posInf());
    }
    // Clear active bound trail frame (first frame is base, keep it)
    if (!trail_.empty()) {
        trail_[0].clear();
    }
    betaDirty_ = true;
    conflict_.clear();
    hasImmediateConflict_ = false;
}

void GeneralSimplex::reset() {
    vars_.clear();
    matrix_.clear();
    rhs_.clear();
    basicVars_.clear();
    isBasic_.clear();
    beta_.clear();
    lower_.clear();
    upper_.clear();
    conflict_.clear();
    trail_.clear();
    trail_.push_back({});  // base frame
    numRows_ = 0;
    numCols_ = 0;
    betaDirty_ = true;
    hasImmediateConflict_ = false;
}

// ============================================================================
// Accessors
// ============================================================================

DeltaRational GeneralSimplex::value(int var) const {
    assert(var >= 0 && var < numCols_);
    return beta_[var];
}

bool GeneralSimplex::isBasic(int var) const {
    assert(var >= 0 && var < numCols_);
    return isBasic_[var];
}

int GeneralSimplex::rowOfBasic(int var) const {
    for (int r = 0; r < numRows_; ++r) {
        if (basicVars_[r] == var) return r;
    }
    assert(false && "Variable is not basic");
    return -1;
}

} // namespace nlcolver
