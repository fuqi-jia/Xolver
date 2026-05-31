#include "theory/arith/nia/search/NiaLocalSearch.h"
#include <random>
#include <algorithm>
#include <functional>
#include <chrono>
#include <cstdlib>

namespace xolver {

// LS-IA-style linear distance for a single atom evaluated at `val` =
// p(model). Returns 0 when the atom is satisfied; otherwise the
// "distance to satisfaction" in integer steps.
//
// NOT squared. The original implementation summed val² across atoms,
// which made high-magnitude polynomials (e.g. y² + y⁴ + y⁶ …) dominate
// the entire cost — search direction got hijacked by the largest
// monomial. LS-IA (arXiv:2211.10219) defines the cost as a sum of
// LINEAR distances; strict integer inequalities use ε = 1.
//
// This is the load-bearing correctness fix for NIA local search per
// the master review.
static mpz_class atomDistance(Relation rel, const mpz_class& val) {
    switch (rel) {
        case Relation::Eq:  return abs(val);
        case Relation::Neq: return (val == 0) ? mpz_class(1) : mpz_class(0);
        case Relation::Lt:  return (val <  0) ? mpz_class(0) : (val + 1);
        case Relation::Leq: return (val <= 0) ? mpz_class(0) : val;
        case Relation::Gt:  return (val >  0) ? mpz_class(0) : (-val + 1);
        case Relation::Geq: return (val >= 0) ? mpz_class(0) : -val;
    }
    return mpz_class(0);
}

NiaLocalSearch::NiaLocalSearch(PolynomialKernel& kernel)
    // Dev defaults were 200ms/1000ms (24s-screening). Competition has 1200s, so
    // give SLS a real budget: 5s per call, 60s cumulative. Candidate-only +
    // validator-gated, so raising is SOUND (no model found = just unknown).
    : kernel_(kernel), budgetMs_(5000), totalBudgetMs_(60000) {
    if (const char* e = std::getenv("XOLVER_NIA_LS_BUDGET_MS")) {
        budgetMs_ = std::atol(e);   // 0 or negative = unlimited
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_TOTAL_MS")) {
        totalBudgetMs_ = std::atol(e);   // 0 or negative = unlimited
    }
    if (const char* e = std::getenv("XOLVER_NIA_LOCALSEARCH"); e && *e && *e != '0') {
        enhanced_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_TWO_LEVEL"); e && *e && *e != '0') {
        twoLevel_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_WARM_START"); e && *e && *e != '0') {
        warmStart_ = true;
    }
}

// Stable signature of the current constraint set used by the warm-start
// context to detect "structurally same" calls vs the assertion stack
// having changed under us. We hash (poly-id, rel) pairs in order — order
// matters because normalized_ is index-stable in NiaSolver's pipeline.
static uint64_t computeConstraintSignature(
    const std::vector<NormalizedNiaConstraint>& constraints) {
    uint64_t h = 1469598103934665603ULL;  // FNV-1a basis
    for (const auto& c : constraints) {
        uint64_t p = static_cast<uint64_t>(c.poly);
        uint64_t r = static_cast<uint64_t>(c.rel);
        h ^= p;
        h *= 1099511628211ULL;
        h ^= r;
        h *= 1099511628211ULL;
    }
    return h;
}

// Stable hash for a single constraint — used as a PAWS-weight key that
// survives across cb_check calls. Same (poly, rel) ⇒ same hash; once a
// clause becomes hard, its weight persists even if its position in
// `constraints` shifts.
static uint64_t hashConstraint(const NormalizedNiaConstraint& c) {
    uint64_t h = 1469598103934665603ULL;
    h ^= static_cast<uint64_t>(c.poly);
    h *= 1099511628211ULL;
    h ^= static_cast<uint64_t>(c.rel);
    h *= 1099511628211ULL;
    return h;
}

mpz_class NiaLocalSearch::violation(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {

    // LS-IA linear-distance sum. NOT squared (see atomDistance comment).
    // For strict inequalities at integer arithmetic, ε = 1.
    mpz_class total = 0;
    for (const auto& c : constraints) {
        auto valOpt = kernel_.evalInteger(c.poly, model);
        if (!valOpt) continue;
        total += atomDistance(c.rel, *valOpt);
    }
    return total;
}

std::optional<IntegerModel> NiaLocalSearch::tryFindModel(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains) {

    if (constraints.empty()) return IntegerModel{};

    // Per-solve cumulative budget exhausted: skip the search entirely.
    if (totalBudgetMs_ > 0 && cumulativeMs_ >= totalBudgetMs_) return std::nullopt;

    const auto t0 = std::chrono::steady_clock::now();
    struct Accum {  // record this call's wall time into cumulativeMs_ on exit
        std::chrono::steady_clock::time_point t0; long& acc;
        ~Accum() {
            acc += std::chrono::duration_cast<std::chrono::milliseconds>(
                       std::chrono::steady_clock::now() - t0).count();
        }
    } accum{t0, cumulativeMs_};
    auto timedOut = [&]() -> bool {
        if (budgetMs_ <= 0) return false;
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                      std::chrono::steady_clock::now() - t0).count();
        return ms >= budgetMs_;
    };

    // Collect variables in deterministic order
    std::vector<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            if (std::find(vars.begin(), vars.end(), v) == vars.end()) {
                vars.push_back(v);
            }
        }
    }

    // Enhanced WalkSAT (XOLVER_NIA_LOCALSEARCH): try the accelerated search
    // first; on success the model is validated by the caller (sound). On
    // failure fall through to the basic candidate sweep below.
    if (enhanced_ && !vars.empty()) {
        // Phase L1: when XOLVER_NIA_LS_TWO_LEVEL is on, run the LS-IA
        // + Yices2LS-style variant (incremental score, PAWS weights,
        // adaptive step). On miss, fall through to the original walkSat
        // (covers cases the L1 heuristic misses) and then the candidate
        // sweep.
        if (twoLevel_) {
            if (auto m = walkSatTwoLevel(constraints, vars, domains)) return m;
            if (timedOut()) return std::nullopt;
        }
        if (auto m = walkSat(constraints, vars, domains)) return m;
        if (timedOut()) return std::nullopt;
    }

    std::vector<IntegerModel> candidates;

    // Candidate 1: all zeros
    {
        IntegerModel m;
        for (const auto& v : vars) m[v] = 0;
        candidates.push_back(m);
    }

    // Candidate 2: domain bounds and midpoints
    for (const auto& v : vars) {
        const auto* d = domains.getDomain(v);
        if (d && d->hasLower && d->hasUpper) {
            mpz_class lb = d->lower.value;
            mpz_class ub = d->upper.value;
            mpz_class mid = (lb + ub) / 2;
            for (const auto& val : {lb, ub, mid}) {
                IntegerModel m;
                for (const auto& vv : vars) m[vv] = 0;
                m[v] = val;
                candidates.push_back(m);
            }
        }
    }

    // Candidate 3: enumerate small finite domains
    bool allFinite = true;
    mpz_class totalSize = 1;
    for (const auto& v : vars) {
        const auto* d = domains.getDomain(v);
        if (!d || !d->hasLower || !d->hasUpper) {
            allFinite = false;
            break;
        }
        mpz_class sz = d->upper.value - d->lower.value + 1;
        if (sz <= 0) {
            allFinite = false;
            break;
        }
        totalSize *= sz;
        if (totalSize > 200) {
            allFinite = false;
            break;
        }
    }

    if (allFinite && totalSize <= 200) {
        // Full enumeration for tiny domains
        auto enumerate = [&](auto&& self, size_t idx, IntegerModel& cur) -> void {
            if (idx == vars.size()) {
                candidates.push_back(cur);
                return;
            }
            const auto* d = domains.getDomain(vars[idx]);
            mpz_class lb = d->lower.value;
            mpz_class ub = d->upper.value;
            for (mpz_class val = lb; val <= ub; ++val) {
                cur[vars[idx]] = val;
                self(self, idx + 1, cur);
            }
        };
        IntegerModel cur;
        for (const auto& v : vars) cur[v] = 0;
        enumerate(enumerate, 0, cur);
    } else {
        // Candidate 4: small integers [-5, 5] for few variables
        if (vars.size() <= 2) {
            if (vars.size() == 1) {
                for (int i = -5; i <= 5; ++i) {
                    IntegerModel m;
                    m[vars[0]] = i;
                    candidates.push_back(m);
                }
            } else if (vars.size() == 2) {
                for (int i = -3; i <= 3; ++i) {
                    for (int j = -3; j <= 3; ++j) {
                        IntegerModel m;
                        m[vars[0]] = i;
                        m[vars[1]] = j;
                        candidates.push_back(m);
                    }
                }
            }
        }

        // Candidate 5: deterministic sampling across domain
        for (int s = 0; s < 20; ++s) {
            IntegerModel m;
            for (const auto& v : vars) {
                const auto* d = domains.getDomain(v);
                if (d && d->hasLower && d->hasUpper) {
                    mpz_class lb = d->lower.value;
                    mpz_class ub = d->upper.value;
                    mpz_class range = ub - lb;
                    if (range > 0) {
                        mpz_class step = range / 20 + 1;
                        m[v] = lb + step * s;
                        if (m[v] > ub) m[v] = ub;
                    } else {
                        m[v] = lb;
                    }
                } else {
                    m[v] = s - 10;
                }
            }
            candidates.push_back(m);
        }
    }

    // Evaluate candidates
    std::optional<IntegerModel> best;
    mpz_class bestViol;
    bool first = true;

    for (const auto& m : candidates) {
        if (timedOut()) return std::nullopt;   // budget spent, no model this call
        mpz_class v = violation(m, constraints);
        if (v == 0) {
            return m; // Found satisfying assignment
        }
        if (first || v < bestViol) {
            best = m;
            bestViol = v;
            first = false;
        }
    }

    // Hill-climbing local search from the best candidate
    if (best) {
        IntegerModel cur = *best;
        mpz_class curViol = bestViol;
        const int MAX_STEPS = 100;
        for (int step = 0; step < MAX_STEPS; ++step) {
            if (timedOut()) break;
            bool improved = false;
            for (const auto& v : vars) {
                for (int delta : {-1, 1}) {
                    IntegerModel next = cur;
                    next[v] += delta;
                    // Respect domain bounds if available
                    const auto* d = domains.getDomain(v);
                    if (d && d->hasLower && next[v] < d->lower.value) continue;
                    if (d && d->hasUpper && next[v] > d->upper.value) continue;

                    mpz_class vNext = violation(next, constraints);
                    if (vNext == 0) {
                        return next;
                    }
                    if (vNext <= curViol) {
                        cur = next;
                        curViol = vNext;
                        improved = true;
                        break; // accept first improving or equal move
                    }
                }
                if (improved) break;
            }
            if (!improved) break; // local minimum
        }
    }

    // No satisfying assignment found
    return std::nullopt;
}

std::optional<IntegerModel> NiaLocalSearch::walkSat(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const std::vector<std::string>& vars,
    const DomainStore& domains) {

    const auto t0 = std::chrono::steady_clock::now();
    auto timedOut = [&]() -> bool {
        if (budgetMs_ <= 0) return false;
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                      std::chrono::steady_clock::now() - t0).count();
        return ms >= budgetMs_;
    };

    std::mt19937_64 rng(0x9e3779b97f4a7c15ULL);  // deterministic (SMT-COMP)
    const mpz_class RANGE = mpz_class(1) << 20;   // clamp for unbounded vars

    auto clampVar = [&](const std::string& v, mpz_class val) -> mpz_class {
        const auto* d = domains.getDomain(v);
        if (d && d->hasLower && val < d->lower.value) val = d->lower.value;
        if (d && d->hasUpper && val > d->upper.value) val = d->upper.value;
        if (!(d && d->hasLower) && val < -RANGE) val = -RANGE;
        if (!(d && d->hasUpper) && val >  RANGE) val =  RANGE;
        return val;
    };

    const int RESTARTS = 20;
    const int MAX_FLIPS = 400;
    const int NOISE = 3;  // out of 10: random-move probability (escape minima)

    for (int restart = 0; restart < RESTARTS && !timedOut(); ++restart) {
        IntegerModel cur;
        for (const auto& v : vars) {
            const auto* d = domains.getDomain(v);
            if (restart == 0) {
                cur[v] = clampVar(v, 0);
            } else if (d && d->hasLower && d->hasUpper) {
                mpz_class span = d->upper.value - d->lower.value;
                cur[v] = (span <= 0) ? d->lower.value
                                     : d->lower.value + mpz_class(rng()) % (span + 1);
            } else {
                cur[v] = clampVar(v, mpz_class((long)(rng() % 4001) - 2000));
            }
        }
        mpz_class curViol = violation(cur, constraints);
        if (curViol == 0) return cur;

        for (int flip = 0; flip < MAX_FLIPS; ++flip) {
            if ((flip & 31) == 0 && timedOut()) return std::nullopt;

            // collect violated constraints
            std::vector<const NormalizedNiaConstraint*> violated;
            for (const auto& c : constraints) {
                auto vOpt = kernel_.evalInteger(c.poly, cur);
                if (!vOpt) continue;
                const mpz_class& val = *vOpt;
                bool sat = true;
                switch (c.rel) {
                    case Relation::Eq:  sat = (val == 0); break;
                    case Relation::Neq: sat = (val != 0); break;
                    case Relation::Lt:  sat = (val <  0); break;
                    case Relation::Leq: sat = (val <= 0); break;
                    case Relation::Gt:  sat = (val >  0); break;
                    case Relation::Geq: sat = (val >= 0); break;
                }
                if (!sat) violated.push_back(&c);
            }
            if (violated.empty()) return cur;  // all satisfied

            const NormalizedNiaConstraint* C = violated[rng() % violated.size()];
            std::vector<std::string> cvars = kernel_.variables(C->poly);
            if (cvars.empty()) break;  // constant-violated: nothing to flip

            // accelerated critical move: jump a variable toward the value that
            // satisfies C (discrete Newton step), keeping the move that most
            // reduces total violation; with probability NOISE/10, random-walk.
            mpz_class bestViol = curViol, bestVal;
            std::string bestVar;
            bool haveBest = false;
            for (const auto& v : cvars) {
                const mpz_class orig = cur[v];
                auto p0 = kernel_.evalInteger(C->poly, cur);
                cur[v] = orig + 1;
                auto p1 = kernel_.evalInteger(C->poly, cur);
                cur[v] = orig;
                std::vector<mpz_class> targets = {orig + 1, orig - 1, orig + 2, orig - 2};
                if (p0 && p1) {
                    mpz_class slope = *p1 - *p0;
                    if (slope != 0) {
                        mpz_class step = -(*p0) / slope;  // root of the linearization
                        targets.push_back(orig + step);
                        targets.push_back(orig + step + 1);
                        targets.push_back(orig + step - 1);
                    }
                }
                for (mpz_class t : targets) {
                    t = clampVar(v, t);
                    if (t == orig) continue;
                    cur[v] = t;
                    mpz_class nv = violation(cur, constraints);
                    cur[v] = orig;
                    if (nv == 0) { cur[v] = t; return cur; }
                    if (!haveBest || nv < bestViol) {
                        bestViol = nv; bestVar = v; bestVal = t; haveBest = true;
                    }
                }
            }

            if (((int)(rng() % 10) < NOISE) || !haveBest) {
                const std::string& v = cvars[rng() % cvars.size()];
                long nudge = (long)(rng() % 21) - 10;
                if (nudge == 0) nudge = 1;
                cur[v] = clampVar(v, cur[v] + nudge);
                curViol = violation(cur, constraints);
            } else {
                cur[bestVar] = bestVal;
                curViol = bestViol;
            }
            if (curViol == 0) return cur;
        }
    }
    return std::nullopt;
}

// Phase L1 — LS-IA + Yices2LS-style enhanced WalkSAT.
//
// The three load-bearing engineering improvements over walkSat:
//
// (1) Incremental per-clause violation tracking. The base walkSat re-evaluates
//     the FULL constraint list per candidate move (line ~354) which is O(n)
//     per try and O(n²) over a flip. Here we keep `cviol[i]` = current
//     violation of constraint i, and a `varToClauses[v]` index. When we
//     change variable v, only clauses in varToClauses[v] need re-evaluation;
//     totalCost = Σ cviol[i] * weight[i] updates by Δ_v alone. This is the
//     standard LS engineering fix (LS-NRA paper: "without incremental, perf
//     collapses").
//
// (2) PAWS clause weights. Every plateau (no improvement for K=20 consecutive
//     flips) bumps the weight of every currently-falsified constraint by 1.
//     totalCost weights hard clauses heavier, so search prefers attacking
//     them. The classical PAWS recipe.
//
// (3) Accelerated hill-climb with adaptive step. Successive step sizes
//     k = 1, ⌊1.2⌋, ⌊1.44⌋, ⌊1.728⌋, ... up to a cap; keep the best, fall
//     back on failure. Combined with the discrete-Newton step (slope-based
//     target) this catches both small refinements and large jumps.
//
// Soundness: candidate-only, validator-gated. Never returns UNSAT;
// returns Sat ONLY when total cost reaches 0 (all clauses satisfied with
// the kernel's exact integer arithmetic) — the caller still validates.
std::optional<IntegerModel> NiaLocalSearch::walkSatTwoLevel(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const std::vector<std::string>& vars,
    const DomainStore& domains) {

    const auto t0 = std::chrono::steady_clock::now();
    auto timedOut = [&]() -> bool {
        if (budgetMs_ <= 0) return false;
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                      std::chrono::steady_clock::now() - t0).count();
        return ms >= budgetMs_;
    };

    std::mt19937_64 rng(0x9e3779b97f4a7c15ULL);
    const mpz_class RANGE = mpz_class(1) << 20;

    auto clampVar = [&](const std::string& v, mpz_class val) -> mpz_class {
        const auto* d = domains.getDomain(v);
        if (d && d->hasLower && val < d->lower.value) val = d->lower.value;
        if (d && d->hasUpper && val > d->upper.value) val = d->upper.value;
        if (!(d && d->hasLower) && val < -RANGE) val = -RANGE;
        if (!(d && d->hasUpper) && val >  RANGE) val =  RANGE;
        return val;
    };

    const std::size_t nC = constraints.size();

    // Build variable → clause-indices index. Variables not appearing in any
    // constraint are simply absent; constants get an empty entry.
    std::unordered_map<std::string, std::vector<std::size_t>> varToClauses;
    for (std::size_t i = 0; i < nC; ++i) {
        for (const auto& v : kernel_.variables(constraints[i].poly)) {
            varToClauses[v].push_back(i);
        }
    }

    // Per-constraint violation of the current assignment, LS-IA linear
    // distance. NOT squared — the original implementation summed val²
    // which let high-magnitude monomials dominate cost direction. See
    // atomDistance() at file scope.
    auto evalCviol = [&](std::size_t i, const IntegerModel& cur) -> mpz_class {
        auto valOpt = kernel_.evalInteger(constraints[i].poly, cur);
        if (!valOpt) return mpz_class(0);   // unsupported → treat as 0
        return atomDistance(constraints[i].rel, *valOpt);
    };

    const int RESTARTS = 20;
    const int MAX_FLIPS = 800;          // L1 raises max-flips to amortise PAWS
    const int PLATEAU_K = 20;           // PAWS bump every K flips w/o improve
    const int NOISE = 3;                // out of 10
    const mpz_class STEP_CAP = mpz_class(1) << 24;  // cap accelerated step

    // ── Phase L1 step 2 — persistent context (warm-start) integration ──
    //
    // When XOLVER_NIA_LS_WARM_START is on, we resume from lsContext_'s
    // best assignment + PAWS weights as long as the constraint set's
    // signature matches the last call. On structural change we reset the
    // assignment but keep weights (clauses still hash-stable; carryover
    // is a no-op for genuinely-new clauses).
    //
    // SOUNDNESS: lsContext_ holds heuristic bias only. Every Sat is
    // validated by the caller against the ORIGINAL constraints; UNSAT
    // is never claimed from LS. A stale context just wastes search
    // effort; it cannot cause a wrong verdict.
    // Only touch lsContext_ when warm-start is enabled. With warmStart_
    // off, the entire persistence path is a no-op — tests pin this.
    uint64_t sig = 0;
    bool warmHit = false;
    if (warmStart_) {
        sig = computeConstraintSignature(constraints);
        warmHit = (lsContext_.lastSignature == sig &&
                   !lsContext_.bestAssignment.empty());
        if (lsContext_.lastSignature != sig) {
            // Signature changed: drop the cached assignment but KEEP
            // weights (PAWS hardness is keyed by constraint hash; unrelated
            // old entries are harmless; matching entries still boost
            // current hard clauses).
            lsContext_.bestAssignment.clear();
            lsContext_.currentAssignment.clear();
            lsContext_.bestValid = false;
            lsContext_.bestCost = 0;
        }
        lsContext_.lastSignature = sig;
    }
    // Best-overall trajectory across all restarts in THIS call. Mirrored
    // into lsContext_ at function exit.
    IntegerModel bestOverallModel;
    mpz_class bestOverallCost = 0;
    bool haveBestOverall = false;

    for (int restart = 0; restart < RESTARTS && !timedOut(); ++restart) {
        IntegerModel cur;
        // restart 0 warm-starts from lsContext_.bestAssignment when
        // available; later restarts diversify (random/restart 0 zeros).
        if (restart == 0 && warmHit) {
            cur = lsContext_.bestAssignment;
            // Fill in any vars that weren't present in the cached best.
            for (const auto& v : vars) {
                if (cur.find(v) == cur.end()) cur[v] = clampVar(v, 0);
            }
        } else {
            for (const auto& v : vars) {
                const auto* d = domains.getDomain(v);
                if (restart == 0) {
                    cur[v] = clampVar(v, 0);
                } else if (d && d->hasLower && d->hasUpper) {
                    mpz_class span = d->upper.value - d->lower.value;
                    cur[v] = (span <= 0) ? d->lower.value
                                         : d->lower.value + mpz_class(rng()) % (span + 1);
                } else {
                    cur[v] = clampVar(v, mpz_class((long)(rng() % 4001) - 2000));
                }
            }
        }

        // Initial incremental state.
        std::vector<mpz_class> cviol(nC), weight(nC, mpz_class(1));
        // Phase L1 step 2: restore PAWS weights from the persistent
        // context when the constraint hash matches. New clauses (no
        // hash entry) start at 1.
        if (warmStart_) {
            for (std::size_t i = 0; i < nC; ++i) {
                uint64_t ch = hashConstraint(constraints[i]);
                auto it = lsContext_.clauseWeight.find(ch);
                if (it != lsContext_.clauseWeight.end() && it->second > 1) {
                    weight[i] = it->second;
                }
            }
        }
        mpz_class totalCost = 0;
        for (std::size_t i = 0; i < nC; ++i) {
            cviol[i] = evalCviol(i, cur);
            totalCost += cviol[i];
        }
        if (totalCost == 0) return cur;

        // weightedCost accounts for PAWS clause weights.
        auto computeWeightedCost = [&]() -> mpz_class {
            mpz_class wc = 0;
            for (std::size_t i = 0; i < nC; ++i) wc += cviol[i] * weight[i];
            return wc;
        };
        mpz_class weightedCost = computeWeightedCost();

        // For a candidate `v := newVal`, return the delta to weightedCost
        // by re-evaluating only the affected clauses.
        auto tryMoveCost = [&](const std::string& v, mpz_class newVal,
                                mpz_class& deltaOut) -> mpz_class {
            auto it = varToClauses.find(v);
            if (it == varToClauses.end()) { deltaOut = 0; return weightedCost; }
            const mpz_class orig = cur[v];
            cur[v] = newVal;
            mpz_class delta = 0;
            mpz_class newTotalRaw = 0;
            for (std::size_t i : it->second) {
                mpz_class nv = evalCviol(i, cur);
                delta += (nv - cviol[i]) * weight[i];
                newTotalRaw += nv;
            }
            cur[v] = orig;
            deltaOut = delta;
            (void)newTotalRaw;
            return weightedCost + delta;
        };

        // Commit a move: update cviol[], totalCost, weightedCost in place.
        auto commitMove = [&](const std::string& v, mpz_class newVal) {
            auto it = varToClauses.find(v);
            cur[v] = newVal;
            if (it == varToClauses.end()) return;
            for (std::size_t i : it->second) {
                mpz_class nv = evalCviol(i, cur);
                weightedCost += (nv - cviol[i]) * weight[i];
                totalCost += (nv - cviol[i]);
                cviol[i] = nv;
            }
        };

        int sinceImprove = 0;
        for (int flip = 0; flip < MAX_FLIPS; ++flip) {
            if ((flip & 31) == 0 && timedOut()) return std::nullopt;
            if (totalCost == 0) return cur;

            // Find any currently-falsified constraint set.
            std::vector<std::size_t> falsified;
            for (std::size_t i = 0; i < nC; ++i) if (cviol[i] > 0) falsified.push_back(i);
            if (falsified.empty()) return cur;

            // Pick a random falsified constraint; collect its variables.
            std::size_t ci = falsified[rng() % falsified.size()];
            const NormalizedNiaConstraint& C = constraints[ci];
            std::vector<std::string> cvars = kernel_.variables(C.poly);
            if (cvars.empty()) break;

            // Critical-move search with discrete-Newton + adaptive
            // accelerated step. Try targets: ±1, ±2, slope-based root, and
            // a geometric series at acc=1.2 around each slope-target.
            std::string bestVar;
            mpz_class bestVal = 0;
            mpz_class bestCost = weightedCost;
            bool haveBest = false;
            for (const auto& v : cvars) {
                const mpz_class orig = cur[v];
                // Slope estimate from two probes (orig, orig+1).
                auto p0 = kernel_.evalInteger(C.poly, cur);
                cur[v] = orig + 1;
                auto p1 = kernel_.evalInteger(C.poly, cur);
                cur[v] = orig;
                std::vector<mpz_class> targets = {orig + 1, orig - 1,
                                                   orig + 2, orig - 2};
                if (p0 && p1) {
                    mpz_class slope = *p1 - *p0;
                    if (slope != 0) {
                        mpz_class step = -(*p0) / slope;  // discrete Newton
                        if (step < -STEP_CAP) step = -STEP_CAP;
                        if (step >  STEP_CAP) step =  STEP_CAP;
                        // Accelerated series around the Newton step:
                        // step * (1.2^k) for k = 0..3. Implemented in
                        // integer math via successive 6/5 multiplies.
                        mpz_class s = step;
                        for (int k = 0; k < 4; ++k) {
                            targets.push_back(orig + s);
                            targets.push_back(orig + s + 1);
                            targets.push_back(orig + s - 1);
                            if (s == 0) break;
                            s = (s * 6) / 5;  // ≈ ×1.2; integer rounding ok
                            if (s < -STEP_CAP) s = -STEP_CAP;
                            if (s >  STEP_CAP) s =  STEP_CAP;
                        }
                    }
                }
                for (mpz_class t : targets) {
                    t = clampVar(v, t);
                    if (t == orig) continue;
                    mpz_class delta;
                    mpz_class nc = tryMoveCost(v, t, delta);
                    if (!haveBest || nc < bestCost) {
                        bestCost = nc; bestVar = v; bestVal = t; haveBest = true;
                    }
                }
            }

            // Noise: with prob NOISE/10, ignore the best move and random-nudge.
            if (((int)(rng() % 10) < NOISE) || !haveBest ||
                bestCost >= weightedCost) {
                const std::string& v = cvars[rng() % cvars.size()];
                long nudge = (long)(rng() % 21) - 10;
                if (nudge == 0) nudge = 1;
                mpz_class newVal = clampVar(v, cur[v] + nudge);
                commitMove(v, newVal);
                sinceImprove++;
            } else {
                commitMove(bestVar, bestVal);
                sinceImprove = 0;
                // Phase L1 step 2: variable activity boost (heuristic
                // hint for Phase L1 step 3 NIA decide-priority feedback).
                // Cheap counter; no soundness implication.
                if (warmStart_) lsContext_.varActivity[bestVar]++;
            }

            // Track best-overall across THIS call for write-back to context.
            if (warmStart_ && (!haveBestOverall || totalCost < bestOverallCost)) {
                bestOverallModel = cur;
                bestOverallCost = totalCost;
                haveBestOverall = true;
            }

            // PAWS plateau: bump every falsified clause's weight.
            if (sinceImprove >= PLATEAU_K) {
                for (std::size_t i = 0; i < nC; ++i) {
                    if (cviol[i] > 0) {
                        weight[i] += 1;
                        weightedCost += cviol[i];  // delta from weight bump
                    }
                }
                sinceImprove = 0;
            }
            if (totalCost == 0) {
                if (warmStart_) {
                    // Persist a successful trajectory's PAWS profile +
                    // record the satisfying assignment as the best seen.
                    for (std::size_t i = 0; i < nC; ++i) {
                        if (weight[i] > 1) {
                            lsContext_.clauseWeight[hashConstraint(constraints[i])] = weight[i];
                        }
                    }
                    lsContext_.bestAssignment = cur;
                    lsContext_.currentAssignment = cur;
                    lsContext_.bestCost = 0;
                    lsContext_.bestValid = true;
                }
                return cur;
            }
        }
        // End of restart: write-back the per-restart weights to context.
        if (warmStart_) {
            for (std::size_t i = 0; i < nC; ++i) {
                if (weight[i] > 1) {
                    auto& w = lsContext_.clauseWeight[hashConstraint(constraints[i])];
                    if (weight[i] > w) w = weight[i];
                }
            }
        }
    }
    // Persist best-overall trajectory for the next cb_check warm-start.
    // The best-overall may still violate some clauses (totalCost > 0);
    // it's the LOWEST-cost assignment LS reached this call. Heuristic
    // bias only — never affects soundness.
    if (warmStart_ && haveBestOverall) {
        lsContext_.bestAssignment = bestOverallModel;
        lsContext_.currentAssignment = bestOverallModel;
        lsContext_.bestCost = bestOverallCost;
        lsContext_.bestValid = (bestOverallCost == 0);
    }
    return std::nullopt;
}

} // namespace xolver
