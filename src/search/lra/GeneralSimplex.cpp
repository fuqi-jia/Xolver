#include "base/RuntimeConfig.h"
#include "search/lra/GeneralSimplex.h"
#include "base/EnvParam.h"
#include <cassert>
#include <chrono>
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <array>
#include <cstdio>
#include <stdexcept>

namespace xolver {

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
    noteAnalysisChange();
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

    // A definition adds no restriction to the old variables. Preserve a clean
    // current assignment by initializing only this row; bound assertion can
    // then update its incident rows without rebuilding the entire tableau.
    if (!betaDirty_) {
        DeltaRational value(f.constant);
        for (const auto& [var, coefficient] : f.terms)
            value += coefficient * vars_[var].beta;
        vars_[aux].beta = std::move(value);
    }
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
    // beta-consistency verifier (env XOLVER_LRA_VERIFY_BETA, works in release): every
    // basic var's beta must equal its row evaluation (rhs + Σ coeff*nonbasic.beta) —
    // the invariant the incremental-beta paths (backtrack-skip / new-var) must
    // preserve. A mismatch means the incremental beta is WRONG (then the slowness is
    // pivot-repair, i.e. a BUG, not a genuine drift tradeoff).
    const bool verifyBeta = xolver::config::read<xolver::config::ReadKind::Presence>("XOLVER_LRA_VERIFY_BETA");
    if (verifyBeta && !betaDirty_) {
        for (int r = 0; r < tab_.numRows(); ++r) {
            const SparseRow& row = tab_.row(r);
            DeltaRational v(row.rhs);
            for (const auto& e : row.entries) v += e.coeff * vars_[e.col].beta;
            if (!(vars_[row.basicVar].beta == v)) {
                std::cerr << "[BETA-INCONSISTENT] row=" << r << " basic=" << row.basicVar
                          << " stored beta != row eval" << std::endl;
            }
        }
    }
}

// ============================================================================
// Bound assertion
// ============================================================================

bool GeneralSimplex::assertLower(int var, const BoundInfo& info, int level) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < static_cast<int>(vars_.size()));

    if (info.bound <= vars_[var].lower.bound) return true;
    const auto retainedAnalysis = fixedValueAnalysis_;
    noteBoundChange();
    const auto boundAnalysisRevision = analysisRevision();
    if (info.bound > vars_[var].upper.bound) {
        explainImmediateConflict(var, true, info.reason.value());
        hasImmediateConflict_ = true;
        return false;
    }

    trail_.push_back({level, var, true, vars_[var].lower});
    vars_[var].lower = info;
    boundedVars_.insert(var);

    if (vars_[var].basicRow == -1 && violatesLower(var)) {
        update(var, info.bound.value);
    } else {
        refreshViolationStatus(var);
    }
    // An accepted tightening cannot remove an existing pin. If it creates no
    // pin either, all sources of the fixed-value closure remain unchanged.
    if (retainedAnalysis && !fixedValue(var) && boundAnalysisRevision &&
        analysisRevision() == boundAnalysisRevision)
        fixedValueAnalysis_ = retainedAnalysis;
    return true;
}

bool GeneralSimplex::assertUpper(int var, const BoundInfo& info, int level) {
    assert(info.bound.isFinite());
    assert(info.reason.has_value());
    assert(var >= 0 && var < static_cast<int>(vars_.size()));

    if (info.bound >= vars_[var].upper.bound) return true;
    const auto retainedAnalysis = fixedValueAnalysis_;
    noteBoundChange();
    const auto boundAnalysisRevision = analysisRevision();
    if (info.bound < vars_[var].lower.bound) {
        explainImmediateConflict(var, false, info.reason.value());
        hasImmediateConflict_ = true;
        return false;
    }

    trail_.push_back({level, var, false, vars_[var].upper});
    vars_[var].upper = info;
    boundedVars_.insert(var);

    if (vars_[var].basicRow == -1 && violatesUpper(var)) {
        update(var, info.bound.value);
    } else {
        refreshViolationStatus(var);
    }
    if (retainedAnalysis && !fixedValue(var) && boundAnalysisRevision &&
        analysisRevision() == boundAnalysisRevision)
        fixedValueAnalysis_ = retainedAnalysis;
    return true;
}

// ============================================================================
// Beta computation and helpers
// ============================================================================

void GeneralSimplex::recomputeBeta() {
    // recomputeBeta is a full O(rows*nnz) rebuild fired on every backtrack /
    // new-var / reset (betaDirty_). The diagnostic below (env XOLVER_LRA_BETA_EVERY=N:
    // dump call count + cumulative time every N calls) confirms whether it — not
    // pivoting — is the LIA/LRA theory-throughput hot path. It is env-driven (not
    // compile-gated) so it works on the shipped binary; zero-overhead when unset.
    const int betaEvery = []() {
        return config::read<config::ReadKind::Int>("XOLVER_LRA_BETA_EVERY", 0);
    }();
    bool betaTimed = (betaEvery > 0);
#ifdef XOLVER_LRA_PROFILE
    betaTimed = true;
#endif
    std::chrono::steady_clock::time_point bt0;
    if (betaTimed) bt0 = std::chrono::steady_clock::now();

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

    if (betaTimed) {
        auto bt1 = std::chrono::steady_clock::now();
        long long us = std::chrono::duration_cast<std::chrono::microseconds>(bt1 - bt0).count();
#ifdef XOLVER_LRA_PROFILE
        coeffStats_.mpqOpTimeUs += us;
#endif
        if (betaEvery > 0) {
            static thread_local long long gBetaCalls = 0;
            static thread_local long long gBetaUs = 0;
            ++gBetaCalls;
            gBetaUs += us;
            if (gBetaCalls % betaEvery == 0) {
                long long nnz = 0;
                for (int r = 0; r < tab_.numRows(); ++r) nnz += static_cast<long long>(tab_.row(r).entries.size());
                std::cerr << "[LRA-BETA] calls=" << gBetaCalls
                          << " cumUs=" << gBetaUs
                          << " rows=" << tab_.numRows()
                          << " vars=" << vars_.size()
                          << " nnz=" << nnz << std::endl;
            }
        }
    }
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
#ifdef XOLVER_LRA_PROFILE
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
#ifdef XOLVER_LRA_PROFILE
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

int GeneralSimplex::pickViolatedBasicBland() const {
    int best = -1;
    for (int xb : basicVars_) {
        if (xb < 0) continue;
        if (violatesLower(xb) || violatesUpper(xb)) {
            if (best == -1 || xb < best) best = xb;
        }
    }
    return best;
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
#ifdef XOLVER_LRA_PROFILE
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
    // LRA is decidable: check() must never self-return Unknown from an internal
    // iteration cap (that would be giving up on a solvable, decidable instance —
    // only the external wall-clock may stop a solve). Termination is guaranteed
    // instead by Bland's anti-cycling rule:
    //   - iter < kHeuristicPivotBudget: heuristic entering.
    //   - iter >= kHeuristicPivotBudget: Bland entering (smallest index).
    //   - iter >= kStrictBlandThreshold: STRICT Bland — smallest-index leaving AND
    //     entering, which provably terminates (Dutertre–de Moura). The fast queue
    //     leaving is used before that, so default performance is unchanged.
    // The huge guard below is a last-resort against a genuine non-termination
    // bug, not a normal exit; under strict Bland it is unreachable in practice.
    const int kHeuristicPivotBudget = 4000;
    const long long kStrictBlandThreshold = 10000;
    const long long kSafetyGuard = 1LL << 34;  // ~1.7e10 pivots; external timeout fires first

    // Reuse the existing diagnostic destination. These counters describe
    // sparse elimination work, independently of the entering-variable rule.
    const auto profilePath = config::read<config::ReadKind::ProfilePath>(
        "ARITH_STAGE_PROF", "/tmp/xolver_stageprof.txt");
    auto recordPivotChoice = [&](int basic, int entering, bool increase) {
        if (profilePath.empty()) return;
        struct WorkProfile {
            unsigned long long pivots = 0, cheaperChoices = 0;
            unsigned long long chosenDegree = 0, minimumDegree = 0;
            unsigned long long chosenUpdates = 0, minimumUpdates = 0;
            std::chrono::steady_clock::time_point lastDump{};
        };
        static thread_local WorkProfile profile;
        const auto& row = tab_.row(rowOfBasic(basic));
        const size_t chosen = tab_.col(entering).entries.size();
        size_t minimum = chosen;
        for (const auto& entry : row.entries) {
            const bool eligible = increase
                ? ((entry.coeff > 0 && canIncrease(entry.col)) ||
                   (entry.coeff < 0 && canDecrease(entry.col)))
                : ((entry.coeff < 0 && canIncrease(entry.col)) ||
                   (entry.coeff > 0 && canDecrease(entry.col)));
            if (eligible) minimum = std::min(minimum, tab_.col(entry.col).entries.size());
        }
        ++profile.pivots;
        profile.cheaperChoices += minimum < chosen;
        profile.chosenDegree += chosen;
        profile.minimumDegree += minimum;
        profile.chosenUpdates += (chosen - 1) * row.entries.size();
        profile.minimumUpdates += (minimum - 1) * row.entries.size();
        const auto now = std::chrono::steady_clock::now();
        if (now - profile.lastDump < std::chrono::seconds(2)) return;
        profile.lastDump = now;
        auto outputPath = profilePath;
        outputPath += ".simplex.json";
        if (FILE* output = std::fopen(outputPath.c_str(), "w")) {
            std::fprintf(output,
                "{\"pivots\":%llu,\"cheaper_choices\":%llu,"
                "\"chosen_column_degree\":%llu,\"minimum_column_degree\":%llu,"
                "\"chosen_update_estimate\":%llu,\"minimum_update_estimate\":%llu}\n",
                profile.pivots, profile.cheaperChoices, profile.chosenDegree,
                profile.minimumDegree, profile.chosenUpdates, profile.minimumUpdates);
            std::fclose(output);
        }
    };

    for (long long iter = 0; iter < kSafetyGuard; ++iter) {
        bool strictBland = iter >= kStrictBlandThreshold;
        int xi = strictBland ? pickViolatedBasicBland() : pickViolatedBasic();
        if (xi == -1) {
            conflict_.clear();
            return Result::Sat;
        }

        bool useBland = strictBland || iter >= kHeuristicPivotBudget;

        if (violatesLower(xi)) {
            int xj = findEnteringVarToIncrease(xi, useBland);
            if (xj == -1) {
                explainLowerConflict(xi);
                return Result::Unsat;
            }
            recordPivotChoice(xi, xj, true);
            pivotAndUpdate(xi, xj, vars_[xi].lower.bound.value);
        } else if (violatesUpper(xi)) {
            int xj = findEnteringVarToDecrease(xi, useBland);
            if (xj == -1) {
                explainUpperConflict(xi);
                return Result::Unsat;
            }
            recordPivotChoice(xi, xj, false);
            pivotAndUpdate(xi, xj, vars_[xi].upper.bound.value);
        }
    }

    std::cerr << "[GeneralSimplex] safety guard hit (probable non-termination bug)" << std::endl;
    conflict_.clear();
    return Result::Unknown;
}

// ============================================================================
// Entering variable selection
// ============================================================================

int GeneralSimplex::findEnteringVar(int basicVar, bool increase, bool useBland) const {
    const auto& row = tab_.row(rowOfBasic(basicVar));
    int best = -1;
    size_t bestDegree = 0;
    mpq_class bestMagnitude(0);
    for (const auto& entry : row.entries) {
        const int variable = entry.col;
        const auto& coefficient = entry.coeff;
        const bool eligible = increase
            ? ((coefficient > 0 && canIncrease(variable)) ||
               (coefficient < 0 && canDecrease(variable)))
            : ((coefficient < 0 && canIncrease(variable)) ||
               (coefficient > 0 && canDecrease(variable)));
        if (!eligible) continue;
        if (useBland) {
            if (best == -1 || variable < best) best = variable;
            continue;
        }
        // Each incident non-pivot row must eliminate this column against the
        // entire pivot row. Its degree predicts exact sparse arithmetic work;
        // floating-point numerical stability is irrelevant to rational pivots.
        const size_t degree = tab_.col(variable).entries.size();
        const mpq_class magnitude = coefficient < 0 ? mpq_class(-coefficient) : coefficient;
        if (best == -1 || degree < bestDegree ||
            (degree == bestDegree && (magnitude > bestMagnitude ||
             (magnitude == bestMagnitude && variable < best)))) {
            best = variable;
            bestDegree = degree;
            bestMagnitude = magnitude;
        }
    }
    return best;
}

int GeneralSimplex::findEnteringVarToIncrease(int basicVar, bool useBland) const {
    return findEnteringVar(basicVar, true, useBland);
}

int GeneralSimplex::findEnteringVarToDecrease(int basicVar, bool useBland) const {
    return findEnteringVar(basicVar, false, useBland);
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

#ifdef XOLVER_LRA_PROFILE
    if (theta.isZero()) ++degeneratePivots_;
#endif

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
    noteAnalysisChange();
#ifdef XOLVER_LRA_PROFILE
    ++pivotCount_;
    auto prof_t0 = std::chrono::steady_clock::now();
    // Live trajectory dump (env XOLVER_LRA_PROFILE_EVERY=N): every N pivots,
    // report cumulative pivot count and the largest coefficient bit-widths in
    // the tableau. Distinguishes pivot-count explosion (pivots climb, bits
    // stay small) from rational coefficient blow-up (bits explode) on cases
    // that time out before check() returns. Diagnostic-only, profile-gated.
    {
        int dumpEvery = []() {
            return config::read<config::ReadKind::Int>("XOLVER_LRA_PROFILE_EVERY", 0);
        }();
        // Process-global pivot counter so the modulo dump works across the many
        // short check() calls of a CDCL(T) solve (per-call pivotCount_ resets).
        static long long gTotalPivots = 0;
        ++gTotalPivots;
        if (dumpEvery > 0 && gTotalPivots % dumpEvery == 0) {
            int maxNum = 0, maxDen = 0;
            long long nnz = 0;
            long long sumNum = 0, sumDen = 0, samples = 0;
            for (int row = 0; row < tab_.numRows(); ++row) {
                const auto& sr = tab_.row(row);
                maxNum = std::max<int>(maxNum, mpz_sizeinbase(sr.rhs.get_num().get_mpz_t(), 2));
                maxDen = std::max<int>(maxDen, mpz_sizeinbase(sr.rhs.get_den().get_mpz_t(), 2));
                nnz += static_cast<long long>(sr.entries.size());
                for (const auto& e : sr.entries) {
                    int nb = mpz_sizeinbase(e.coeff.get_num().get_mpz_t(), 2);
                    int db = mpz_sizeinbase(e.coeff.get_den().get_mpz_t(), 2);
                    maxNum = std::max(maxNum, nb);
                    maxDen = std::max(maxDen, db);
                    sumNum += nb; sumDen += db; ++samples;
                }
            }
            int rows = tab_.numRows();
            double density = rows ? static_cast<double>(nnz) / rows : 0.0;
            double avgNum = samples ? static_cast<double>(sumNum) / samples : 0.0;
            double avgDen = samples ? static_cast<double>(sumDen) / samples : 0.0;
            std::cerr << "[LRA-PROF] gpivots=" << gTotalPivots
                      << " degen=" << degeneratePivots_
                      << " rows=" << rows
                      << " vars=" << vars_.size()
                      << " nnz=" << nnz
                      << " density=" << density
                      << " maxNumBits=" << maxNum
                      << " maxDenBits=" << maxDen
                      << " avgNumBits=" << avgNum
                      << " avgDenBits=" << avgDen << std::endl;
        }
    }
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

#ifdef XOLVER_LRA_PROFILE
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
#ifdef XOLVER_ENABLE_PROOFS
    conflictCoeffs_.clear();
#endif
    int r = rowOfBasic(basicVar);

    assert(vars_[basicVar].lower.bound.isFinite());
    if (vars_[basicVar].lower.reason.has_value()) {
        conflict_.push_back({basicVar, true, vars_[basicVar].lower.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
        conflictCoeffs_.push_back(1);  // violated basic bound: multiplier 1
#endif
    }

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;
        if (a > 0 && atUpper(xj)) {
            if (vars_[xj].upper.reason.has_value()) {
                conflict_.push_back({xj, false, vars_[xj].upper.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
                conflictCoeffs_.push_back(a);  // |row coeff|, a > 0
#endif
            }
        } else if (a < 0 && atLower(xj)) {
            if (vars_[xj].lower.reason.has_value()) {
                conflict_.push_back({xj, true, vars_[xj].lower.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
                conflictCoeffs_.push_back(-a);  // |row coeff|, a < 0
#endif
            }
        }
    }
}

void GeneralSimplex::explainUpperConflict(int basicVar) {
    conflict_.clear();
#ifdef XOLVER_ENABLE_PROOFS
    conflictCoeffs_.clear();
#endif
    int r = rowOfBasic(basicVar);

    assert(vars_[basicVar].upper.bound.isFinite());
    if (vars_[basicVar].upper.reason.has_value()) {
        conflict_.push_back({basicVar, false, vars_[basicVar].upper.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
        conflictCoeffs_.push_back(1);  // violated basic bound: multiplier 1
#endif
    }

    for (const auto& e : tab_.row(r).entries) {
        int xj = e.col;
        const mpq_class& a = e.coeff;
        if (a > 0 && atLower(xj)) {
            if (vars_[xj].lower.reason.has_value()) {
                conflict_.push_back({xj, true, vars_[xj].lower.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
                conflictCoeffs_.push_back(a);  // |row coeff|, a > 0
#endif
            }
        } else if (a < 0 && atUpper(xj)) {
            if (vars_[xj].upper.reason.has_value()) {
                conflict_.push_back({xj, false, vars_[xj].upper.reason.value()});
#ifdef XOLVER_ENABLE_PROOFS
                conflictCoeffs_.push_back(-a);  // |row coeff|, a < 0
#endif
            }
        }
    }
}

void GeneralSimplex::explainImmediateConflict(int var, bool newBoundIsLower, SatLit newReason) {
    conflict_.clear();
#ifdef XOLVER_ENABLE_PROOFS
    conflictCoeffs_.clear();
#endif
    if (newBoundIsLower) {
        assert(vars_[var].upper.bound.isFinite());
        conflict_.push_back({var, true, newReason});
        if (vars_[var].upper.reason.has_value()) {
            conflict_.push_back({var, false, vars_[var].upper.reason.value()});
        }
    } else {
        assert(vars_[var].lower.bound.isFinite());
        conflict_.push_back({var, false, newReason});
        if (vars_[var].lower.reason.has_value()) {
            conflict_.push_back({var, true, vars_[var].lower.reason.value()});
        }
    }
#ifdef XOLVER_ENABLE_PROOFS
    // Two contradictory bounds on `var` (same simplex column => coeff 1): unit
    // multipliers refute. Mirror conflict_'s size (1 or 2 entries).
    conflictCoeffs_.assign(conflict_.size(), mpq_class(1));
#endif
}

// ============================================================================
// Scope management
// ============================================================================

void GeneralSimplex::push() {
    Scope scope{trail_.size(), hasImmediateConflict_, conflict_
#ifdef XOLVER_ENABLE_PROOFS
        , conflictCoeffs_
#endif
    };
    scopeStack_.push_back(std::move(scope));
}

void GeneralSimplex::pop(AssignmentPolicy policy) {
    noteBoundChange();
    assert(!scopeStack_.empty());
    auto scope = std::move(scopeStack_.back());
    const size_t target = scope.trailSize;
    scopeStack_.pop_back();
    // A contradictory bound is rejected before entering the bound trail.
    // Restore its status explicitly, including an already-conflicting parent.
    hasImmediateConflict_ = scope.immediateConflict;
    conflict_ = std::move(scope.conflict);
#ifdef XOLVER_ENABLE_PROOFS
    conflictCoeffs_ = std::move(scope.conflictCoeffs);
#endif
    while (trail_.size() > target) {
        const auto& e = trail_.back();
        if (e.isLower) vars_[e.var].lower = e.oldBound;
        else           vars_[e.var].upper = e.oldBound;
        if (!vars_[e.var].lower.bound.isFinite() && !vars_[e.var].upper.bound.isFinite())
            boundedVars_.erase(e.var);
        trail_.pop_back();
    }
    if (policy == AssignmentPolicy::Reinitialize) betaDirty_ = true;
    else if (!betaDirty_) rebuildViolationQueue();
}

void GeneralSimplex::backtrackToLevel(int level, AssignmentPolicy policy) {
    noteBoundChange();
    while (!trail_.empty() && trail_.back().level > level) {
        const auto& e = trail_.back();
        if (e.isLower) vars_[e.var].lower = e.oldBound;
        else           vars_[e.var].upper = e.oldBound;
        if (!vars_[e.var].lower.bound.isFinite() && !vars_[e.var].upper.bound.isFinite())
            boundedVars_.erase(e.var);
        trail_.pop_back();
    }
    hasImmediateConflict_ = false;
    conflict_.clear();
    violatedQueue_.clear();
    std::fill(inViolationQueue_.begin(), inViolationQueue_.end(), false);
    // Withdrawing bounds does not change any tableau equation. A retained
    // point may violate a remaining bound after an infeasible child, so rebuild
    // the violation queue while preserving its exact row-consistent values.
    if (policy == AssignmentPolicy::Reinitialize) betaDirty_ = true;
    else if (!betaDirty_) rebuildViolationQueue();
}

// ============================================================================
// Reset
// ============================================================================

void GeneralSimplex::resetActiveBounds(AssignmentPolicy policy) {
    noteBoundChange();
    for (int i : boundedVars_) {
        vars_[i].lower = BoundInfo(BoundValue::negInf());
        vars_[i].upper = BoundInfo(BoundValue::posInf());
    }
    boundedVars_.clear();
    trail_.clear();
    scopeStack_.clear();
    // Assignment selection is explicit: nonlinear clients retain their
    // centering behavior; incremental feasibility checks can keep a valid point.
    if (policy == AssignmentPolicy::Reinitialize) betaDirty_ = true;
    conflict_.clear();
    hasImmediateConflict_ = false;
    violatedQueue_.clear();
    std::fill(inViolationQueue_.begin(), inViolationQueue_.end(), false);
}

void GeneralSimplex::reset() {
    noteBoundChange();
    vars_.clear();
    boundedVars_.clear();
    boundMergeSlots_.clear();
    boundMergeSources_.clear();
    boundMergeViolations_.clear();
    boundMergeChanged_.clear();
    boundMergeValues_.clear();
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

bool GeneralSimplex::replaceActiveBounds(const std::vector<ActiveBound>& bounds,
                                         AssignmentPolicy policy) {
    std::vector<ActiveBoundView> views;
    views.reserve(bounds.size());
    for (const auto& input : bounds) {
        if (!input.info.bound.isFinite() || !input.info.reason)
            throw std::invalid_argument("replacement bounds need a finite explained endpoint");
        views.push_back({input.var, input.isLower, &input.info.bound.value, *input.info.reason});
    }
    return replaceActiveBoundViews(views, policy);
}

bool GeneralSimplex::replaceActiveBoundViews(std::span<const ActiveBoundView> bounds,
                                             AssignmentPolicy policy) {
    // Clear the previous sparse index, including partial scratch from a rejected
    // call. No bound, revision, conflict or proof state changes until validation.
    for (int var : boundMergeSources_) boundMergeSlots_[var] = -1;
    boundMergeSources_.clear();
    boundMergeViolations_.clear();
    boundMergeChanged_.clear();
    boundMergeSlots_.resize(vars_.size(), -1);
    auto& sourceOrder = boundMergeSources_;
    auto& violatedSourceOrder = boundMergeViolations_;
    for (const auto& input : bounds) {
        if (input.var < 0 || input.var >= numVars() || !input.value)
            throw std::invalid_argument("replacement bounds need an existing column and a finite endpoint");
        const auto* endpoint = input.value;
        if (mpz_sgn(mpq_denref(endpoint->a.get_mpq_t())) == 0 ||
            mpz_sgn(mpq_denref(endpoint->b.get_mpq_t())) == 0)
            throw std::invalid_argument("replacement bounds need nonzero rational denominators");
        std::optional<DeltaRational> normalized;
        if (mpz_cmp_ui(mpq_denref(endpoint->a.get_mpq_t()), 1) != 0 ||
            mpz_cmp_ui(mpq_denref(endpoint->b.get_mpq_t()), 1) != 0) {
            normalized = *endpoint;
            normalized->a.canonicalize();
            normalized->b.canonicalize();
            endpoint = &*normalized;
        }
        if (policy == AssignmentPolicy::Preserve && !betaDirty_ && vars_[input.var].basicRow >= 0) {
            const auto& point = vars_[input.var].beta;
            if (input.isLower ? point < *endpoint : point > *endpoint)
                violatedSourceOrder.push_back(input.var);
        }
        int slot = boundMergeSlots_[input.var];
        if (slot < 0) {
            slot = static_cast<int>(sourceOrder.size());
            if (boundMergeValues_.size() <= static_cast<size_t>(slot)) boundMergeValues_.emplace_back();
            sourceOrder.push_back(input.var);
            boundMergeSlots_[input.var] = slot;
            auto& values = boundMergeValues_[slot];
            values[0].bound.kind = BoundKind::NegInf;
            values[1].bound.kind = BoundKind::PosInf;
            values[0].reason.reset();
            values[1].reason.reset();
        }
        auto& current = boundMergeValues_[slot][input.isLower ? 0 : 1];
        if (!current.bound.isFinite() || (input.isLower ? *endpoint > current.bound.value : *endpoint < current.bound.value)) {
            current.bound.kind = BoundKind::Finite;
            current.bound.value = *endpoint;
            current.reason = input.reason;
        }
    }
    // Allocation belongs to the validation phase; storage is retained for the
    // next restoration rather than repeatedly freeing small GMP endpoints.
    boundMergeChanged_.reserve(boundedVars_.size() + sourceOrder.size());
    std::vector<std::unordered_set<int>::node_type> membership(sourceOrder.size());
    const auto retainedAnalysis = fixedValueAnalysis_;
    bool fixedSourcesChanged = false;
    noteBoundChange();
    const auto replacementRevision = analysisRevision();
    trail_.clear();
    scopeStack_.clear();
    hasImmediateConflict_ = false;
    conflict_.clear();
    auto& changed = boundMergeChanged_;
    auto assign = [&](int var, const BoundInfo& lower, const BoundInfo& upper) {
        auto& state = vars_[var];
        if (state.lower.bound.kind != lower.bound.kind || state.upper.bound.kind != upper.bound.kind ||
            (lower.bound.isFinite() && (state.lower.bound.value != lower.bound.value || state.lower.reason != lower.reason)) ||
            (upper.bound.isFinite() && (state.upper.bound.value != upper.bound.value || state.upper.reason != upper.reason))) {
            if (retainedAnalysis && !fixedSourcesChanged) {
                const bool wasFixed = state.lower.bound.isFinite() && state.upper.bound.isFinite() &&
                    state.lower.bound.value == state.upper.bound.value;
                const bool nowFixed = lower.bound.isFinite() && upper.bound.isFinite() &&
                    lower.bound.value == upper.bound.value;
                fixedSourcesChanged = wasFixed != nowFixed || (wasFixed &&
                    (state.lower.bound.value != lower.bound.value || state.lower.reason != lower.reason ||
                     state.upper.reason != upper.reason));
            }
            state.lower = lower;
            state.upper = upper;
            changed.push_back(var);
        }
        if (!hasImmediateConflict_ && lower.bound > upper.bound) {
            explainImmediateConflict(var, true, *lower.reason);
            hasImmediateConflict_ = true;
        }
    };
    for (auto it = boundedVars_.begin(); it != boundedVars_.end();) {
        const auto current = it++;
        const int var = *current;
        const int slot = boundMergeSlots_[var];
        if (slot >= 0) membership[slot] = boundedVars_.extract(current);
        else {
            assign(var, BoundInfo(BoundValue::negInf()), BoundInfo(BoundValue::posInf()));
            boundedVars_.erase(current);
        }
    }
    // Relink retained nodes in the same source order as complete reconstruction.
    // This preserves hash iteration and fixed-proof seed order without freeing
    // and reallocating a node for every unchanged parent column.
    for (int var : sourceOrder) {
        const int slot = boundMergeSlots_[var];
        const auto& endpoints = boundMergeValues_[slot];
        assign(var, endpoints[0], endpoints[1]);
        if (membership[slot].empty()) boundedVars_.insert(var);
        else boundedVars_.insert(std::move(membership[slot]));
    }
    if (policy == AssignmentPolicy::Reinitialize) betaDirty_ = true;
    if (!betaDirty_ && !hasImmediateConflict_) {
        // Preserve the first violated bound EVENT, not the first occurrence of
        // its column: an early weak bound must not move a later strong bound
        // ahead of another column. Withdrawing child bounds normally leaves
        // non-basic points unchanged, matching incremental parent replay.
        bool pointMoved = false;
        for (const int var : changed) {
            if (vars_[var].basicRow >= 0) continue;
            if (violatesLower(var)) { update(var, vars_[var].lower.bound.value); pointMoved = true; }
            else if (violatesUpper(var)) { update(var, vars_[var].upper.bound.value); pointMoved = true; }
        }
        for (int var : violatedQueue_) inViolationQueue_[var] = false;
        violatedQueue_.clear();
        for (int var : violatedSourceOrder) refreshViolationStatus(var);
        // A new non-basic point can expose additional violations.
        if (pointMoved) for (int var : sourceOrder) refreshViolationStatus(var);
    }
    // Fixed-value closure uses only equality pins, their explanations and the
    // tableau equations. Other interval changes do not change those proofs.
    // The bound/scan revision still changes; outstanding snapshots stay immutable.
    if (retainedAnalysis && !fixedSourcesChanged && replacementRevision &&
        analysisRevision() == replacementRevision)
        fixedValueAnalysis_ = retainedAnalysis;
    return !hasImmediateConflict_;
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
    reasons.reserve(2);
    const auto& v = vars_[var];
    if (v.lower.bound.isFinite() && v.upper.bound.isFinite() &&
        v.lower.bound.value == v.upper.bound.value) {
        if (v.lower.reason.has_value()) {
            reasons.emplace_back(BoundReason{var, true, v.lower.reason.value()});
        }
        if (v.upper.reason.has_value()) {
            reasons.emplace_back(BoundReason{var, false, v.upper.reason.value()});
        }
    }
    return reasons;
}

GeneralSimplex::FixedValueAnalysis GeneralSimplex::analyzeFixedValues() const {
    FixedValueAnalysis result;
    result.values_.resize(vars_.size());
    result.dependencies_.resize(vars_.size());
    result.premises_.resize(vars_.size());
    for (int var : boundedVars_) {
        if (auto value = fixedValue(var)) {
            result.values_[var] = *value;
            result.premises_[var] = explainFixedValue(var);
        }
    }

    // Row equation: basic - sum(coeff * nonbasic) = rhs. Count unknowns
    // without rational arithmetic; evaluate only rows that can determine a
    // value. Most partially known rows never fire during a closure pass.
    std::vector<size_t> unknown(tab_.numRows());
    std::vector<int> pending;
    for (int r = 0; r < tab_.numRows(); ++r) {
        const auto& row = tab_.row(r);
        if (!result.values_[row.basicVar]) ++unknown[r];
        for (const auto& entry : row.entries) {
            if (!result.values_[entry.col]) ++unknown[r];
        }
        if (unknown[r] == 1) pending.push_back(r);
    }
    while (!pending.empty()) {
        const int r = pending.back(); pending.pop_back();
        if (unknown[r] != 1) continue;
        const auto& row = tab_.row(r);
        int var = -1;
        mpq_class coefficient = 1;
        DeltaRational residual(row.rhs);
        if (result.values_[row.basicVar]) residual -= *result.values_[row.basicVar];
        else var = row.basicVar;
        for (const auto& entry : row.entries) {
            if (result.values_[entry.col]) residual += entry.coeff * *result.values_[entry.col];
            else {
                assert(var == -1);
                var = entry.col;
                coefficient = -entry.coeff;
            }
        }
        assert(var >= 0 && coefficient != 0);
        result.values_[var] = residual / coefficient;
        auto& dependencies = result.dependencies_[var];
        if (row.basicVar != var) dependencies.push_back(row.basicVar);
        for (const auto& entry : row.entries)
            if (entry.col != var) dependencies.push_back(entry.col);

        auto updateRow = [&](int affected) {
            assert(unknown[affected] > 0);
            --unknown[affected];
            if (unknown[affected] == 1) pending.push_back(affected);
        };
        if (isBasic(var)) updateRow(basicRowOfVar(var));
        for (const auto& entry : tab_.col(var).entries)
            updateRow(entry.row);
    }
    return result;
}

std::optional<DeltaRational>
GeneralSimplex::FixedValueAnalysis::fixedValue(int var) const {
    if (var < 0 || static_cast<size_t>(var) >= values_.size()) return std::nullopt;
    return values_[var];
}

std::shared_ptr<const GeneralSimplex::FixedValueAnalysis>
GeneralSimplex::sharedFixedValueAnalysis() const {
    if (!fixedValueAnalysis_)
        fixedValueAnalysis_ = std::make_shared<const FixedValueAnalysis>(analyzeFixedValues());
    return fixedValueAnalysis_;
}

std::optional<GeneralSimplex::FixedValueProof>
GeneralSimplex::FixedValueAnalysis::prove(int var) const {
    if (var < 0 || static_cast<size_t>(var) >= values_.size() || !values_[var])
        return std::nullopt;
    std::vector<BoundReason> reasons;
    std::vector<int> pending{var};
    std::unordered_set<int> visited;
    while (!pending.empty()) {
        const int current = pending.back(); pending.pop_back();
        if (!visited.insert(current).second) continue;
        reasons.insert(reasons.end(), premises_[current].begin(), premises_[current].end());
        pending.insert(pending.end(), dependencies_[current].begin(), dependencies_[current].end());
    }
    auto less = [](const BoundReason& a, const BoundReason& b) {
        if (a.var != b.var) return a.var < b.var;
        if (a.isLower != b.isLower) return a.isLower < b.isLower;
        if (a.reason.var != b.reason.var) return a.reason.var < b.reason.var;
        return a.reason.sign < b.reason.sign;
    };
    std::sort(reasons.begin(), reasons.end(), less);
    reasons.erase(std::unique(reasons.begin(), reasons.end(), [&](const auto& a, const auto& b) {
        return !less(a, b) && !less(b, a);
    }), reasons.end());
    return FixedValueProof{*values_[var], std::move(reasons)};
}

std::optional<GeneralSimplex::FixedValueProof> GeneralSimplex::proveFixedValue(int var) const {
    if (var < 0 || var >= numVars()) return std::nullopt;
    if (auto direct = fixedValue(var)) return FixedValueProof{*direct, explainFixedValue(var)};
    return sharedFixedValueAnalysis()->prove(var);
}

// ============================================================================
// Accessors
// ============================================================================

DeltaRational GeneralSimplex::value(int var) const {
    assert(var >= 0 && var < static_cast<int>(vars_.size()));
    return vars_[var].beta;
}

mpq_class GeneralSimplex::computeSafeDelta() const {
    // For each variable x with β(x) = a + bδ and a finite bound c + dδ that
    // x satisfies, substituting a concrete δ must preserve the inequality.
    // The only binding case is when the real parts differ and the δ-parts
    // push the wrong way:
    //   lower l = lₐ + l_b·δ, need a + bδ ≥ lₐ + l_b·δ:
    //     if a > lₐ and b < l_b  →  δ ≤ (a − lₐ) / (l_b − b)
    //   upper u = uₐ + u_b·δ, need a + bδ ≤ uₐ + u_b·δ:
    //     if a < uₐ and b > u_b  →  δ ≤ (uₐ − a) / (b − u_b)
    // (When real parts are equal, feasibility already fixed the δ-ordering,
    // so any δ > 0 works.) Take half the tightest bound, or 1 if none.
    mpq_class delta = 1;
    bool bounded = false;
    auto tighten = [&](const mpq_class& cand) {
        if (cand <= 0) return;  // defensive; feasibility should preclude this
        if (!bounded || cand < delta) { delta = cand; bounded = true; }
    };
    for (const auto& v : vars_) {
        const DeltaRational& beta = v.beta;
        if (v.lower.bound.kind == BoundKind::Finite) {
            const DeltaRational& l = v.lower.bound.value;
            if (beta.a > l.a && beta.b < l.b) {
                tighten((beta.a - l.a) / (l.b - beta.b));
            }
        }
        if (v.upper.bound.kind == BoundKind::Finite) {
            const DeltaRational& u = v.upper.bound.value;
            if (beta.a < u.a && beta.b > u.b) {
                tighten((u.a - beta.a) / (beta.b - u.b));
            }
        }
    }
    return bounded ? delta / 2 : mpq_class(1);
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

} // namespace xolver
