#include "LraPropagationEngine.h"
#include <cassert>
#include <algorithm>

namespace zolver {

// ============================================================================
// Public API
// ============================================================================

std::vector<LraPropagationEngine::ExplainedBound>
LraPropagationEngine::propagateAll(const GeneralSimplex& gs,
                                   const PropagationBudget& budget) {
    gs_ = &gs;
    budget_ = &budget;
    workQueue_.clear();
    workPos_ = 0;
    iterationCount_ = 0;
    derivedCount_ = 0;
    strongestDerived_.clear();
    startTime_ = std::chrono::steady_clock::now();

    // Seed: enqueue every basic var (forward derivation).
    // Also enqueue basic vars that have an active bound (backward derivation).
    int n = gs.numVars();
    for (int v = 0; v < n; ++v) {
        if (gs.basicRowOfVar(v) >= 0) {
            enqueue(v, true);   // will do forward lower + backward from lower if present
            enqueue(v, false);  // will do forward upper + backward from upper if present
        }
    }

    std::vector<ExplainedBound> accepted;

    while (workPos_ < workQueue_.size() && !shouldStop()) {
        WorkItem item = workQueue_[workPos_++];
        ++iterationCount_;

        int row = gs.basicRowOfVar(item.var);
        if (row < 0) {
            // Non-basic var with a new bound: enqueue every basic var whose row
            // contains this non-basic var.
            const auto& col = gs.tableau().col(item.var);
            for (const auto& ce : col.entries) {
                int basicVar = gs.tableau().row(ce.row).basicVar;
                if (basicVar >= 0) {
                    enqueue(basicVar, true);
                    enqueue(basicVar, false);
                }
            }
            continue;
        }

        const auto& tabRow = gs.tableau().row(row);

        if (item.isLower) {
            // --- Forward: lower(basic) from non-basic bounds ---
            {
                DeltaRational numer(tabRow.rhs);
                std::vector<std::pair<int, SatLit>> reasonAcc;
                bool ok = true;
                for (const auto& e : tabRow.entries) {
                    auto st = gs.varState(e.col);
                    if (e.coeff > 0) {
                        if (!st.lower.bound.isFinite()) { ok = false; break; }
                        numer += e.coeff * st.lower.bound.value;
                        if (!st.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                        reasonAcc.push_back({e.col, *st.lower.reason});
                    } else {
                        if (!st.upper.bound.isFinite()) { ok = false; break; }
                        numer += e.coeff * st.upper.bound.value;
                        if (!st.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                        reasonAcc.push_back({e.col, *st.upper.reason});
                    }
                }
                if (ok) {
                    auto reasons = collectReasons(reasonAcc);
                    if (tryDeriveBound(item.var, true, numer, reasons)) {
                        accepted.push_back({item.var, true, numer, std::move(reasons)});
                    }
                }
            }
            // --- Backward from lower(basic) ---
            // Only if basicVar actually has a lower bound.
            {
                auto basicSt = gs.varState(item.var);
                if (!basicSt.lower.bound.isFinite()) goto skip_backward_lower;
            }
            for (const auto& e : tabRow.entries) {
                int otherVar = e.col;
                const mpq_class& coeff = e.coeff;
                bool deriveLower = (coeff > 0);  // coeff>0 -> lower; coeff<0 -> upper

                DeltaRational numer = DeltaRational(tabRow.rhs);
                std::vector<std::pair<int, SatLit>> reasonAcc;
                bool ok = true;

                {
                    auto basicSt = gs.varState(item.var);
                    numer = basicSt.lower.bound.value - numer;
                    if (!basicSt.lower.reason) ok = false;  // consumed finite bound must be explained
                    else reasonAcc.push_back({item.var, *basicSt.lower.reason});
                }

                for (const auto& e2 : tabRow.entries) {
                    if (e2.col == otherVar) continue;
                    auto st2 = gs.varState(e2.col);
                    if (deriveLower) {
                        // minimize numerator for lower(x_j) with coeff > 0
                        if (e2.coeff > 0) {
                            if (!st2.upper.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.upper.bound.value;
                            if (!st2.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.upper.reason});
                        } else {
                            if (!st2.lower.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.lower.bound.value;
                            if (!st2.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.lower.reason});
                        }
                    } else {
                        // maximize numerator for upper(x_j) with coeff < 0
                        if (e2.coeff > 0) {
                            if (!st2.lower.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.lower.bound.value;
                            if (!st2.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.lower.reason});
                        } else {
                            if (!st2.upper.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.upper.bound.value;
                            if (!st2.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.upper.reason});
                        }
                    }
                }
                if (ok) {
                    DeltaRational newBound = numer / coeff;
                    auto reasons = collectReasons(reasonAcc);
                    if (tryDeriveBound(otherVar, deriveLower, newBound, reasons)) {
                        accepted.push_back({otherVar, deriveLower, newBound, std::move(reasons)});
                    }
                }
            }
        skip_backward_lower:;
        } else {
            // --- Forward: upper(basic) from non-basic bounds ---
            {
                DeltaRational numer(tabRow.rhs);
                std::vector<std::pair<int, SatLit>> reasonAcc;
                bool ok = true;
                for (const auto& e : tabRow.entries) {
                    auto st = gs.varState(e.col);
                    if (e.coeff > 0) {
                        if (!st.upper.bound.isFinite()) { ok = false; break; }
                        numer += e.coeff * st.upper.bound.value;
                        if (!st.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                        reasonAcc.push_back({e.col, *st.upper.reason});
                    } else {
                        if (!st.lower.bound.isFinite()) { ok = false; break; }
                        numer += e.coeff * st.lower.bound.value;
                        if (!st.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                        reasonAcc.push_back({e.col, *st.lower.reason});
                    }
                }
                if (ok) {
                    auto reasons = collectReasons(reasonAcc);
                    if (tryDeriveBound(item.var, false, numer, reasons)) {
                        accepted.push_back({item.var, false, numer, std::move(reasons)});
                    }
                }
            }
            // --- Backward from upper(basic) ---
            {
                auto basicSt = gs.varState(item.var);
                if (!basicSt.upper.bound.isFinite()) goto skip_backward_upper;
            }
            for (const auto& e : tabRow.entries) {
                int otherVar = e.col;
                const mpq_class& coeff = e.coeff;
                bool deriveLower = (coeff < 0);  // coeff>0 -> upper; coeff<0 -> lower

                DeltaRational numer = DeltaRational(tabRow.rhs);
                std::vector<std::pair<int, SatLit>> reasonAcc;
                bool ok = true;

                {
                    auto basicSt = gs.varState(item.var);
                    numer = basicSt.upper.bound.value - numer;
                    if (!basicSt.upper.reason) ok = false;  // consumed finite bound must be explained
                    else reasonAcc.push_back({item.var, *basicSt.upper.reason});
                }

                for (const auto& e2 : tabRow.entries) {
                    if (e2.col == otherVar) continue;
                    auto st2 = gs.varState(e2.col);
                    if (!deriveLower) {
                        // coeff > 0, derive upper(x_j): maximize numerator
                        if (e2.coeff > 0) {
                            if (!st2.lower.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.lower.bound.value;
                            if (!st2.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.lower.reason});
                        } else {
                            if (!st2.upper.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.upper.bound.value;
                            if (!st2.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.upper.reason});
                        }
                    } else {
                        // coeff < 0, derive lower(x_j): minimize numerator
                        if (e2.coeff > 0) {
                            if (!st2.upper.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.upper.bound.value;
                            if (!st2.upper.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.upper.reason});
                        } else {
                            if (!st2.lower.bound.isFinite()) { ok = false; break; }
                            numer -= e2.coeff * st2.lower.bound.value;
                            if (!st2.lower.reason) { ok = false; break; }  // consumed finite bound must be explained
                            reasonAcc.push_back({e2.col, *st2.lower.reason});
                        }
                    }
                }
                if (ok) {
                    DeltaRational newBound = numer / coeff;
                    auto reasons = collectReasons(reasonAcc);
                    if (tryDeriveBound(otherVar, deriveLower, newBound, reasons)) {
                        accepted.push_back({otherVar, deriveLower, newBound, std::move(reasons)});
                    }
                }
            }
        skip_backward_upper:;
        }
    }

    gs_ = nullptr;
    budget_ = nullptr;
    return accepted;
}

// ============================================================================
// Private helpers
// ============================================================================

void LraPropagationEngine::enqueue(int var, bool isLower) {
    workQueue_.push_back({var, isLower});
}

bool LraPropagationEngine::shouldStop() const {
    if (iterationCount_ >= budget_->maxIterations) return true;
    if (derivedCount_ >= budget_->maxDerivedBounds) return true;
    auto now = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(now - startTime_).count();
    if (elapsed >= budget_->maxTimeMs) return true;
    return false;
}

void LraPropagationEngine::computeRowLower(int basicVar) {
    (void)basicVar;
}

void LraPropagationEngine::computeRowUpper(int basicVar) {
    (void)basicVar;
}

bool LraPropagationEngine::tryDeriveBound(int var, bool isLower,
                                          const DeltaRational& value,
                                          const std::vector<SatLit>& reasons) {
    if (derivedCount_ >= budget_->maxDerivedBounds) return false;
    if (static_cast<int>(reasons.size()) > budget_->maxReasonSize) return false;

    auto st = gs_->varState(var);
    if (isLower) {
        if (st.lower.bound.isFinite() && value <= st.lower.bound.value) {
            return false;
        }
    } else {
        if (st.upper.bound.isFinite() && value >= st.upper.bound.value) {
            return false;
        }
    }

    DerivedBoundKey key{var, isLower};
    auto it = strongestDerived_.find(key);
    if (it != strongestDerived_.end()) {
        if (isLower) {
            if (value <= it->second) return false;
        } else {
            if (value >= it->second) return false;
        }
    }

    strongestDerived_[key] = value;
    ++derivedCount_;
    enqueue(var, isLower);
    return true;
}

std::vector<SatLit> LraPropagationEngine::collectReasons(
    const std::vector<std::pair<int, SatLit>>& reasons) {
    std::vector<SatLit> result;
    result.reserve(reasons.size());
    for (const auto& p : reasons) {
        result.push_back(p.second);
    }
    std::sort(result.begin(), result.end(), satLitLess);
    result.erase(std::unique(result.begin(), result.end(), satLitEqual), result.end());
    return result;
}

} // namespace zolver
