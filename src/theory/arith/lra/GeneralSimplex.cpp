#include "theory/arith/lra/GeneralSimplex.h"
#include <cassert>
#include <chrono>
#include <algorithm>
#include <iostream>

namespace nlcolver {

// ============================================================================
// BoundValue comparison
// ============================================================================

bool BoundValue::operator<(const BoundValue& rhs) const {
    if (kind == BoundKind::NegInf) return rhs.kind != BoundKind::NegInf;
    if (kind == BoundKind::PosInf) return false;
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
    trail_.push_back({});
}

// ---------------------------------------------------------------------------
// Variable registration
// ---------------------------------------------------------------------------

int GeneralSimplex::addVar(const std::string& name) {
    int id = static_cast<int>(vars_.size());
    VarState vs;
    vs.name = name;
    vs.lower = BoundInfo(BoundValue::negInf());
    vs.upper = BoundInfo(BoundValue::posInf());
    vs.beta = DeltaRational(0);
    vs.basicRow = -1;
    vars_.push_back(std::move(vs));
    tab_.addEmptyCol();

    nonBasicPos_.push_back(static_cast<int>(nonBasicVars_.size()));
    nonBasicVars_.push_back(id);

    inViolationQueue_.push_back(false);
    return id;
}

// ---------------------------------------------------------------------------
// Basis helpers
// ---------------------------------------------------------------------------

void GeneralSimplex::removeFromNonBasic(int var) {
    assert(vars_[var].basicRow == -1);
    int pos = nonBasicPos_[var];
    assert(pos >= 0);
    int last = nonBasicVars_.back();
    nonBasicVars_[pos] = last;
    nonBasicPos_[last] = pos;
    nonBasicVars_.pop_back();
    nonBasicPos_[var] = -1;
}

void GeneralSimplex::makeBasicWithoutPivot(int var, int row) {
    assert(vars_[var].basicRow == -1);
    removeFromNonBasic(var);
    vars_[var].basicRow = row;
    basicVars_[row] = var;
    tab_.row(row).basicVar = var;
}

void GeneralSimplex::markBasicSwitch(int leaving, int entering) {
    // entering was non-basic, remove it
    // Note: pivot() has already set vars_[entering].basicRow before calling this.
    removeFromNonBasic(entering);

    // leaving becomes non-basic
    assert(vars_[leaving].basicRow != -1);
    vars_[leaving].basicRow = -1;
    nonBasicPos_[leaving] = static_cast<int>(nonBasicVars_.size());
    nonBasicVars_.push_back(leaving);
}

// ---------------------------------------------------------------------------
// rewriteToNonBasic
// ---------------------------------------------------------------------------

GeneralSimplex::LinearForm GeneralSimplex::rewriteToNonBasic(const LinearForm& input) {
    LinearForm out;
    out.constant = input.constant;

    std::unordered_map<int, mpq_class> coeffs;

    auto addTerm = [&](int v, const mpq_class& a) {
        if (a == 0) return;
        coeffs[v] += a;
        if (coeffs[v] == 0) {
            coeffs.erase(v);
        }
    };

    for (const auto& [v, a] : input.terms) {
        int row = vars_[v].basicRow;
        if (row == -1) {
            addTerm(v, a);
        } else {
            out.constant += a * tab_.row(row).rhs;
            for (const auto& e : tab_.row(row).entries) {
                addTerm(e.col, a * e.coeff);
            }
        }
    }

    out.terms.reserve(coeffs.size());
    for (auto& [v, a] : coeffs) {
        if (a != 0) out.terms.push_back({v, a});
    }

    std::sort(out.terms.begin(), out.terms.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    return out;
}

// ---------------------------------------------------------------------------
// Constraint registration
// ---------------------------------------------------------------------------
//
// Semantic contract (the ONLY interpretation):
//   addConstraint(terms, rhs_input) creates an auxiliary variable s with row:
//       s = Σ coeff_i * x_i - rhs_input
//   Internally stored as:
//       row.rhs  = -rhs_input
//       row.entries[var_i] = coeff_i
//   Therefore:
//       s = 0  <=>  Σ coeff_i * x_i = rhs_input
//       s <= 0 <=>  Σ coeff_i * x_i <= rhs_input
//       s >= 0 <=>  Σ coeff_i * x_i >= rhs_input
//
int GeneralSimplex::addConstraint(const std::vector<std::pair<int, mpq_class>>& terms,
                                  const mpq_class& rhs) {
    // Step 1: Build raw linear form.
    //   s = Σ coeff_i * x_i - rhs
    LinearForm raw;
    raw.constant = -rhs;
    for (const auto& [var, coeff] : terms) {
        if (coeff != 0) raw.terms.push_back({var, coeff});
    }

    // Step 2: Rewrite to non-basic variables. Must happen BEFORE aux is basic.
    LinearForm f = rewriteToNonBasic(raw);

    // Step 3: Create auxiliary variable (initially non-basic).
    int aux = addVar("s" + std::to_string(tab_.numRows()));

    // Step 4: Create empty row.
    int row = tab_.addEmptyRow();

    // Step 5: Make aux the basic variable of this row.
    basicVars_.push_back(aux);
    makeBasicWithoutPivot(aux, row);

    // Step 6: Fill row with rewritten coefficients (all non-basic).
    tab_.row(row).rhs = f.constant;
    for (const auto& [var, coeff] : f.terms) {
        assert(vars_[var].basicRow == -1);
        if (coeff != 0) {
            tab_.setCoeff(row, var, coeff);
        }
    }

    betaDirty_ = true;
    return aux;
}

// ============================================================================
// Invariants (debug only)
// ============================================================================

void GeneralSimplex::checkInvariants() const {
#ifndef NDEBUG
    std::vector<int> basicRowOfVar;
    basicRowOfVar.resize(vars_.size(), -1);
    for (int v = 0; v < static_cast<int>(vars_.size()); ++v) {
        basicRowOfVar[v] = vars_[v].basicRow;
    }
    tab_.checkInvariants(basicRowOfVar);

    // nonBasicVars_ / nonBasicPos_ consistency
    assert(static_cast<int>(nonBasicVars_.size()) + tab_.numRows() == static_cast<int>(vars_.size()));
    for (int i = 0; i < static_cast<int>(nonBasicVars_.size()); ++i) {
        int v = nonBasicVars_[i];
        assert(nonBasicPos_[v] == i);
        assert(vars_[v].basicRow == -1);
    }
    for (int v = 0; v < static_cast<int>(vars_.size()); ++v) {
        if (vars_[v].basicRow == -1) {
            assert(nonBasicPos_[v] >= 0);
        } else {
            assert(nonBasicPos_[v] == -1);
        }
    }
#endif
}

// ============================================================================
// Bound assertion
// ============================================================================

bool GeneralSimplex::assertLower(int var, const BoundInfo& info, int level) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < static_cast<int>(vars_.size()));

    if (info.bound <= vars_[var].lower.bound) return true;
    if (info.bound > vars_[var].upper.bound) {
        explainImmediateConflict(var, true, info.reason.value());
        hasImmediateConflict_ = true;
        return false;
    }

    trail_.push_back({level, var, true, vars_[var].lower});
    vars_[var].lower = info;

    if (vars_[var].basicRow == -1 && violatesLower(var)) {
        update(var, info.bound.value);
    } else {
        refreshViolationStatus(var);
    }
    return true;
}

bool GeneralSimplex::assertUpper(int var, const BoundInfo& info, int level) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < static_cast<int>(vars_.size()));

    if (info.bound >= vars_[var].upper.bound) return true;
    if (info.bound < vars_[var].lower.bound) {
        explainImmediateConflict(var, false, info.reason.value());
        hasImmediateConflict_ = true;
        return false;
    }

    trail_.push_back({level, var, false, vars_[var].upper});
    vars_[var].upper = info;

    if (vars_[var].basicRow == -1 && violatesUpper(var)) {
        update(var, info.bound.value);
    } else {
        refreshViolationStatus(var);
    }
    return true;
}

// ============================================================================
// Beta computation and helpers
// ============================================================================

void GeneralSimplex::recomputeBeta() {
#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t0 = std::chrono::steady_clock::now();
#endif
    for (int x : nonBasicVars_) {
        vars_[x].beta = chooseValueWithinBounds(x);
    }

    for (int r = 0; r < tab_.numRows(); ++r) {
        const SparseRow& row = tab_.row(r);
        int xb = row.basicVar;

        DeltaRational v(row.rhs);
        for (const auto& e : row.entries) {
            v += e.coeff * vars_[e.col].beta;
        }
        vars_[xb].beta = v;
    }

    betaDirty_ = false;
    rebuildViolationQueue();
#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    coeffStats_.mpqOpTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
#endif
}

DeltaRational GeneralSimplex::chooseValueWithinBounds(int var) const {
    const auto& l = vars_[var].lower.bound;
    const auto& u = vars_[var].upper.bound;

    DeltaRational zero(0);

    if ((!l.isFinite() || zero >= l.value) &&
        (!u.isFinite() || zero <= u.value)) {
        return zero;
    }

    if (l.isFinite() && u.isFinite()) {
        DeltaRational mid = (l.value + u.value) / 2;
        if (mid >= l.value && mid <= u.value) return mid;
        return l.value;
    }

    if (l.isFinite()) return l.value;
    if (u.isFinite()) return u.value;
    return zero;
}

bool GeneralSimplex::violatesLower(int var) const {
    return vars_[var].lower.bound.isFinite() && vars_[var].beta < vars_[var].lower.bound.value;
}

bool GeneralSimplex::violatesUpper(int var) const {
    return vars_[var].upper.bound.isFinite() && vars_[var].beta > vars_[var].upper.bound.value;
}

bool GeneralSimplex::canIncrease(int var) const {
    return !vars_[var].upper.bound.isFinite() || vars_[var].beta < vars_[var].upper.bound.value;
}

bool GeneralSimplex::canDecrease(int var) const {
    return !vars_[var].lower.bound.isFinite() || vars_[var].beta > vars_[var].lower.bound.value;
}

bool GeneralSimplex::atLower(int var) const {
    return vars_[var].lower.bound.isFinite() && vars_[var].beta == vars_[var].lower.bound.value;
}

bool GeneralSimplex::atUpper(int var) const {
    return vars_[var].upper.bound.isFinite() && vars_[var].beta == vars_[var].upper.bound.value;
}

void GeneralSimplex::update(int nonBasicVar, const DeltaRational& value) {
#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t0 = std::chrono::steady_clock::now();
#endif
    assert(vars_[nonBasicVar].basicRow == -1);
    DeltaRational delta = value - vars_[nonBasicVar].beta;
    if (delta.isZero()) return;

    const auto& colEntries = tab_.col(nonBasicVar).entries;
    // snapshot copy to avoid issues if column is mutated (it shouldn't be here)
    std::vector<ColEntry> affected(colEntries);

    for (const auto& ce : affected) {
        int row = ce.row;
        int xb = tab_.row(row).basicVar;
        mpq_class a = tab_.row(row).entries[ce.rowPos].coeff;
        vars_[xb].beta += a * delta;
        refreshViolationStatus(xb);
    }

    vars_[nonBasicVar].beta = value;
#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    coeffStats_.mpqOpTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
#endif
}

// ============================================================================
// Violation queue (lazy enqueue only)
// ============================================================================

void GeneralSimplex::refreshViolationStatus(int var) {
    if (vars_[var].basicRow == -1) return;
    bool violated = violatesLower(var) || violatesUpper(var);
    if (violated && !inViolationQueue_[var]) {
        violatedQueue_.push_back(var);
        inViolationQueue_[var] = true;
    }
}

int GeneralSimplex::pickViolatedBasic() {
    while (!violatedQueue_.empty()) {
        int x = violatedQueue_.front();
        violatedQueue_.pop_front();
        inViolationQueue_[x] = false;

        if (vars_[x].basicRow != -1 &&
            (violatesLower(x) || violatesUpper(x))) {
            return x;
        }
    }

    // Fallback scan (mainly after recomputeBeta)
    for (int xb : basicVars_) {
        if (violatesLower(xb) || violatesUpper(xb)) {
            return xb;
        }
    }
    return -1;
}

void GeneralSimplex::rebuildViolationQueue() {
    violatedQueue_.clear();
    std::fill(inViolationQueue_.begin(), inViolationQueue_.end(), false);
    for (int xb : basicVars_) {
        if (violatesLower(xb) || violatesUpper(xb)) {
            violatedQueue_.push_back(xb);
            inViolationQueue_[xb] = true;
        }
    }
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
    }
    auto r = checkInternal();
#ifdef NLCOLVER_LRA_PROFILE
    if (r == Result::Sat) {
        // Sample coefficient bit sizes from tableau
        for (int row = 0; row < tab_.numRows(); ++row) {
            const auto& sr = tab_.row(row);
            if (sr.rhs != 0) {
                int numBits = mpz_sizeinbase(sr.rhs.get_num().get_mpz_t(), 2);
                int denBits = mpz_sizeinbase(sr.rhs.get_den().get_mpz_t(), 2);
                coeffStats_.maxCoeffNumBits = std::max(coeffStats_.maxCoeffNumBits, numBits);
                coeffStats_.maxCoeffDenBits = std::max(coeffStats_.maxCoeffDenBits, denBits);
                coeffStats_.totalCoeffNumBits += numBits;
                coeffStats_.totalCoeffDenBits += denBits;
                coeffStats_.totalCoeffSamples++;
            }
            for (const auto& e : sr.entries) {
                if (e.coeff != 0) {
                    int numBits = mpz_sizeinbase(e.coeff.get_num().get_mpz_t(), 2);
                    int denBits = mpz_sizeinbase(e.coeff.get_den().get_mpz_t(), 2);
                    coeffStats_.maxCoeffNumBits = std::max(coeffStats_.maxCoeffNumBits, numBits);
                    coeffStats_.maxCoeffDenBits = std::max(coeffStats_.maxCoeffDenBits, denBits);
                    coeffStats_.totalCoeffNumBits += numBits;
                    coeffStats_.totalCoeffDenBits += denBits;
                    coeffStats_.totalCoeffSamples++;
                }
            }
        }
    }
#endif
    return r;
}

GeneralSimplex::Result GeneralSimplex::checkInternal() {
    const int MAX_ITERATIONS = 10000;

    for (int iter = 0; iter < MAX_ITERATIONS; ++iter) {
        int xi = pickViolatedBasic();
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
            pivotAndUpdate(xi, xj, vars_[xi].lower.bound.value);
        } else if (violatesUpper(xi)) {
            int xj = findEnteringVarToDecrease(xi);
            if (xj == -1) {
                explainUpperConflict(xi);
                return Result::Unsat;
            }
            pivotAndUpdate(xi, xj, vars_[xi].upper.bound.value);
        }
    }

    std::cerr << "[GeneralSimplex] Warning: iteration limit reached" << std::endl;
    conflict_.clear();
    return Result::Unknown;
}

// ============================================================================
// Entering variable selection
// ============================================================================

int GeneralSimplex::findEnteringVarToIncrease(int basicVar) const {
    int r = rowOfBasic(basicVar);
    int best = -1;

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;

        bool eligible = (a > 0 && canIncrease(xj)) || (a < 0 && canDecrease(xj));
        if (!eligible) continue;

        if (best == -1 || xj < best) {
            best = xj;  // Bland's rule
        }
    }
    return best;
}

int GeneralSimplex::findEnteringVarToDecrease(int basicVar) const {
    int r = rowOfBasic(basicVar);
    int best = -1;

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;

        bool eligible = (a < 0 && canIncrease(xj)) || (a > 0 && canDecrease(xj));
        if (!eligible) continue;

        if (best == -1 || xj < best) {
            best = xj;  // Bland's rule
        }
    }
    return best;
}

// ============================================================================
// Pivot
// ============================================================================

void GeneralSimplex::pivotAndUpdate(int leavingBasic, int enteringNonBasic,
                                    const DeltaRational& target) {
    int r = rowOfBasic(leavingBasic);
    mpq_class aij = tab_.getCoeff(r, enteringNonBasic);
    assert(aij != 0);

    DeltaRational theta = (target - vars_[leavingBasic].beta) / aij;

    // Update beta using snapshot of entering column
    std::vector<ColEntry> affected(tab_.col(enteringNonBasic).entries);

    for (const auto& ce : affected) {
        int row = ce.row;
        int xb = tab_.row(row).basicVar;
        mpq_class a = tab_.row(row).entries[ce.rowPos].coeff;

        if (xb == leavingBasic) {
            vars_[xb].beta = target;
        } else {
            vars_[xb].beta += a * theta;
        }
        refreshViolationStatus(xb);
    }

    vars_[enteringNonBasic].beta += theta;

    pivot(leavingBasic, enteringNonBasic);

    refreshViolationStatus(leavingBasic);  // now non-basic, harmless
    refreshViolationStatus(enteringNonBasic);  // now basic
}

void GeneralSimplex::pivot(int leaving, int entering) {
#ifdef NLCOLVER_LRA_PROFILE
    ++pivotCount_;
    auto prof_t0 = std::chrono::steady_clock::now();
#endif
    int r = rowOfBasic(leaving);
    mpq_class d = tab_.getCoeff(r, entering);
    assert(d != 0);

    mpq_class inv_d = 1 / d;

    // Copy old pivot row
    SparseRow oldPivot = tab_.row(r);

    // Build new pivot row: entering = -rhs/a + (1/a)*leaving + Σ(-coeff/a)*x
    std::vector<std::pair<int, mpq_class>> newEntries;
    newEntries.reserve(oldPivot.entries.size());

    mpq_class newRhs = -oldPivot.rhs * inv_d;
    newEntries.push_back({leaving, inv_d});

    for (const auto& e : oldPivot.entries) {
        int col = e.col;
        if (col == entering) continue;
        mpq_class coeff = -e.coeff * inv_d;
        if (coeff != 0) {
            newEntries.push_back({col, coeff});
        }
    }

    // Snapshot of rows containing entering before any mutation
    std::vector<ColEntry> affected(tab_.col(entering).entries);

    // Update all affected non-pivot rows
    for (const auto& ce : affected) {
        int row = ce.row;
        if (row == r) continue;

        mpq_class c = tab_.getCoeff(row, entering);
        if (c == 0) continue;

        tab_.eraseCoeff(row, entering);

        // row_rhs += c * newRhs
        tab_.row(row).rhs += c * newRhs;

        // row += c * newEntries
        for (const auto& [col, coeff] : newEntries) {
            tab_.addCoeff(row, col, c * coeff);
        }

        tab_.row(row).version++;

        int xb = tab_.row(row).basicVar;
        refreshViolationStatus(xb);
    }

    // Replace pivot row
    tab_.replaceRow(r, entering, newRhs, newEntries);

    // Update basis metadata
    // markBasicSwitch assumes entering is still non-basic (basicRow == -1)
    markBasicSwitch(leaving, entering);
    vars_[entering].basicRow = r;
    basicVars_[r] = entering;
    tab_.row(r).basicVar = entering;

    // Invariant: entering is now basic, so its column must be empty
    assert(tab_.col(entering).entries.empty());

#ifdef NLCOLVER_LRA_PROFILE
    auto prof_t1 = std::chrono::steady_clock::now();
    coeffStats_.mpqOpTimeUs += std::chrono::duration_cast<std::chrono::microseconds>(prof_t1 - prof_t0).count();
#endif

    checkInvariants();
}

// ============================================================================
// Conflict explanation
// ============================================================================

void GeneralSimplex::explainLowerConflict(int basicVar) {
    conflict_.clear();
    int r = rowOfBasic(basicVar);

    assert(vars_[basicVar].lower.bound.isFinite());
    assert(vars_[basicVar].lower.reason.has_value());
    conflict_.push_back({basicVar, true, vars_[basicVar].lower.reason.value()});

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;
        if (a > 0 && atUpper(xj)) {
            assert(vars_[xj].upper.reason.has_value());
            conflict_.push_back({xj, false, vars_[xj].upper.reason.value()});
        } else if (a < 0 && atLower(xj)) {
            assert(vars_[xj].lower.reason.has_value());
            conflict_.push_back({xj, true, vars_[xj].lower.reason.value()});
        }
    }
}

void GeneralSimplex::explainUpperConflict(int basicVar) {
    conflict_.clear();
    int r = rowOfBasic(basicVar);

    assert(vars_[basicVar].upper.bound.isFinite());
    assert(vars_[basicVar].upper.reason.has_value());
    conflict_.push_back({basicVar, false, vars_[basicVar].upper.reason.value()});

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;
        if (a > 0 && atLower(xj)) {
            assert(vars_[xj].lower.reason.has_value());
            conflict_.push_back({xj, true, vars_[xj].lower.reason.value()});
        } else if (a < 0 && atUpper(xj)) {
            assert(vars_[xj].upper.reason.has_value());
            conflict_.push_back({xj, false, vars_[xj].upper.reason.value()});
        }
    }
}

void GeneralSimplex::explainImmediateConflict(int var, bool newBoundIsLower, SatLit newReason) {
    conflict_.clear();
    if (newBoundIsLower) {
        assert(vars_[var].upper.bound.isFinite());
        assert(vars_[var].upper.reason.has_value());
        conflict_.push_back({var, true, newReason});
        conflict_.push_back({var, false, vars_[var].upper.reason.value()});
    } else {
        assert(vars_[var].lower.bound.isFinite());
        assert(vars_[var].lower.reason.has_value());
        conflict_.push_back({var, false, newReason});
        conflict_.push_back({var, true, vars_[var].lower.reason.value()});
    }
}

// ============================================================================
// Scope management
// ============================================================================

void GeneralSimplex::push() {
    scopeStack_.push_back(trail_.size());
}

void GeneralSimplex::pop() {
    assert(!scopeStack_.empty());
    size_t target = scopeStack_.back();
    scopeStack_.pop_back();
    while (trail_.size() > target) {
        const auto& e = trail_.back();
        if (e.isLower) vars_[e.var].lower = e.oldBound;
        else           vars_[e.var].upper = e.oldBound;
        trail_.pop_back();
    }
    betaDirty_ = true;
}

void GeneralSimplex::backtrackToLevel(int level) {
    while (!trail_.empty() && trail_.back().level > level) {
        const auto& e = trail_.back();
        if (e.isLower) vars_[e.var].lower = e.oldBound;
        else           vars_[e.var].upper = e.oldBound;
        trail_.pop_back();
    }
    betaDirty_ = true;
    hasImmediateConflict_ = false;
    conflict_.clear();
    violatedQueue_.clear();
    std::fill(inViolationQueue_.begin(), inViolationQueue_.end(), false);
}

// ============================================================================
// Reset
// ============================================================================

void GeneralSimplex::resetActiveBounds() {
    for (int i = 0; i < static_cast<int>(vars_.size()); ++i) {
        vars_[i].lower = BoundInfo(BoundValue::negInf());
        vars_[i].upper = BoundInfo(BoundValue::posInf());
    }
    trail_.clear();
    scopeStack_.clear();
    betaDirty_ = true;
    conflict_.clear();
    hasImmediateConflict_ = false;
    violatedQueue_.clear();
    std::fill(inViolationQueue_.begin(), inViolationQueue_.end(), false);
}

void GeneralSimplex::reset() {
    vars_.clear();
    tab_ = SparseTableau();
    basicVars_.clear();
    nonBasicVars_.clear();
    nonBasicPos_.clear();
    violatedQueue_.clear();
    inViolationQueue_.clear();
    conflict_.clear();
    trail_.clear();
    scopeStack_.clear();
    betaDirty_ = true;
    hasImmediateConflict_ = false;
}

std::optional<DeltaRational> GeneralSimplex::fixedValue(int var) const {
    assert(var >= 0 && var < static_cast<int>(vars_.size()));
    const auto& v = vars_[var];
    if (v.lower.bound.isFinite() && v.upper.bound.isFinite() &&
        v.lower.bound.value == v.upper.bound.value) {
        return v.lower.bound.value;
    }
    return std::nullopt;
}

std::vector<GeneralSimplex::BoundReason> GeneralSimplex::explainFixedValue(int var) const {
    assert(var >= 0 && var < static_cast<int>(vars_.size()));
    std::vector<BoundReason> reasons;
    const auto& v = vars_[var];
    if (v.lower.bound.isFinite() && v.upper.bound.isFinite() &&
        v.lower.bound.value == v.upper.bound.value) {
        if (v.lower.reason.has_value()) {
            reasons.push_back({var, true, v.lower.reason.value()});
        }
        if (v.upper.reason.has_value()) {
            reasons.push_back({var, false, v.upper.reason.value()});
        }
    }
    return reasons;
}

static thread_local int proveFixedValueDepth = 0;
static constexpr int MAX_PROVE_FIXED_VALUE_DEPTH = 10000;

std::optional<std::pair<DeltaRational, std::vector<GeneralSimplex::BoundReason>>>
GeneralSimplex::proveFixedValue(int var) const {
    if (var < 0 || var >= static_cast<int>(vars_.size())) {
        return std::nullopt;
    }
    if (++proveFixedValueDepth > MAX_PROVE_FIXED_VALUE_DEPTH) {
        --proveFixedValueDepth;
        return std::nullopt;
    }

    struct DepthGuard {
        ~DepthGuard() { --proveFixedValueDepth; }
    } guard;

    // Direct bound fix
    auto direct = fixedValue(var);
    if (direct) {
        return std::make_pair(*direct, explainFixedValue(var));
    }

    // If var is basic, check whether all non-basic entries in its row are fixed.
    int row = basicRowOfVar(var);
    if (row < 0 || row >= tableau().numRows()) {
        return std::nullopt;
    }

    const auto& tabRow = tableau().row(row);
    DeltaRational value(tabRow.rhs);
    std::vector<BoundReason> reasons;
    for (const auto& e : tabRow.entries) {
        if (e.col < 0 || e.col >= static_cast<int>(vars_.size())) {
            return std::nullopt;
        }
        auto sub = proveFixedValue(e.col);
        if (!sub) return std::nullopt;
        value += e.coeff * sub->first;
        reasons.insert(reasons.end(), sub->second.begin(), sub->second.end());
    }

    // Deduplicate reasons
    std::sort(reasons.begin(), reasons.end(), [](const BoundReason& a, const BoundReason& b) {
        if (a.var != b.var) return a.var < b.var;
        if (a.isLower != b.isLower) return a.isLower < b.isLower;
        if (a.reason.var != b.reason.var) return a.reason.var < b.reason.var;
        return a.reason.sign < b.reason.sign;
    });
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [](const BoundReason& a, const BoundReason& b) {
        return a.var == b.var && a.isLower == b.isLower && a.reason.var == b.reason.var && a.reason.sign == b.reason.sign;
    }), reasons.end());

    return std::make_pair(value, std::move(reasons));
}

// ============================================================================
// Accessors
// ============================================================================

DeltaRational GeneralSimplex::value(int var) const {
    assert(var >= 0 && var < static_cast<int>(vars_.size()));
    return vars_[var].beta;
}

bool GeneralSimplex::isBasic(int var) const {
    assert(var >= 0 && var < static_cast<int>(vars_.size()));
    return vars_[var].basicRow != -1;
}

bool GeneralSimplex::debugCheckInvariants() const {
    checkInvariants();
    return true;
}

int GeneralSimplex::rowOfBasic(int var) const {
    assert(vars_[var].basicRow != -1);
    return vars_[var].basicRow;
}

} // namespace nlcolver
