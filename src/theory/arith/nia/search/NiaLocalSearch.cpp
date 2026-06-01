#include "theory/arith/nia/search/NiaLocalSearch.h"
#include <random>
#include <algorithm>
#include <functional>
#include <chrono>
#include <cstdlib>
#include <cstdio>
#include <map>

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
    if (const char* e = std::getenv("XOLVER_NIA_LS_MULTI_SCALE"); e && *e && *e != '0') {
        multiScale_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_QUAD_CRITICAL"); e && *e && *e != '0') {
        quadCritical_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_FS_JUMP"); e && *e && *e != '0') {
        fsJump_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_DIVERSE_INIT"); e && *e && *e != '0') {
        diverseInit_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_BILINEAR_PAIR"); e && *e && *e != '0') {
        bilinearPair_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_BILINEAR_SUBST"); e && *e && *e != '0') {
        bilinearSubst_ = true;
    }
    if (const char* e = std::getenv("XOLVER_NIA_LS_PIN_EQ"); e && *e && *e != '0') {
        pinEq_ = true;
    }
}

// Integer square root (floor). Used by multi-scale step to generate
// targets for x²=N-style atoms: if violation is v at orig, a candidate
// near orig + sign·√v often satisfies a quadratic atom in one move.
// Newton iteration; mpz_sqrt would also work but we keep the routine
// header-free here.
static mpz_class isqrt(mpz_class n) {
    if (n < 0) n = -n;
    if (n < 2) return n;
    mpz_class x = n, y = (x + 1) / 2;
    while (y < x) {
        x = y;
        y = (x + n / x) / 2;
    }
    return x;
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

    // LS-VM1 (master 2026-06-02): detect single-var linear Eq atoms
    // (c*v + k = 0 with c|k) and pin v = -k/c. Pinned vars are skipped
    // by the move-search and pre-loaded into every restart's starting
    // assignment. Sound: the equality already forces v's value; pinning
    // is just an LS-side acknowledgement that doesn't change
    // satisfiability. CInteger has these in every case (Farkas chains
    // + initial-state defs); ITS/SAT14 have them in initial-state defs.
    std::unordered_map<std::string, mpz_class> pinned;
    if (pinEq_) {
        for (const auto& c : constraints) {
            if (c.rel != Relation::Eq) continue;
            auto termsOpt = kernel_.terms(c.poly);
            if (!termsOpt) continue;
            mpz_class constSum = 0;
            std::string singleVar;
            mpz_class singleCoef = 0;
            bool ok = true;
            for (const auto& t : *termsOpt) {
                if (t.powers.empty()) { constSum += t.coefficient; continue; }
                if (t.powers.size() != 1 || t.powers[0].second != 1) { ok = false; break; }
                std::string nm(kernel_.varName(t.powers[0].first));
                if (singleVar.empty()) { singleVar = nm; singleCoef = t.coefficient; }
                else if (singleVar == nm) { singleCoef += t.coefficient; }
                else { ok = false; break; }
            }
            if (!ok || singleVar.empty() || singleCoef == 0) continue;
            // c*v + k = 0 -> v = -k/c (must be exact integer)
            mpz_class neg = -constSum;
            if ((neg % singleCoef) != 0) continue;
            mpz_class root = neg / singleCoef;
            // Respect existing domain bounds.
            const auto* d = domains.getDomain(singleVar);
            if (d) {
                if (d->hasLower && root < d->lower.value) continue;
                if (d->hasUpper && root > d->upper.value) continue;
            }
            // If a prior pin disagrees, drop both — the formula has
            // conflicting linear pins, so let the main LS / theory
            // engine handle it (we only pin when a single value forces).
            auto pit = pinned.find(singleVar);
            if (pit != pinned.end()) {
                if (pit->second != root) {
                    pinned.erase(pit);
                }
            } else {
                pinned[singleVar] = root;
            }
        }
    }

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
        } else if (diverseInit_) {
            // P5 diversified restart probes — rotate initial-assignment
            // strategies across restarts so LS visits multiple basins of
            // attraction instead of always starting from zero. SAT14
            // z3-extracted models show many cases satisfy at anchor
            // values 100-300; probing those anchors at restart time
            // gives LS a credible trajectory toward them.
            //
            // Probe rotation by restart index:
            //   r == 0  → all zeros (legacy)
            //   r == 1  → lo for every bounded var, 0 otherwise
            //   r == 2  → hi for every bounded var, 0 otherwise
            //   r == 3  → midpoint (lo + hi) / 2 for bounded, 0 otherwise
            //   r == 4  → one var pinned to ±100, others zero
            //   r == 5  → one var pinned to ±500, others zero
            //   r == 6  → small random in [-10, 10] for every var
            //   r >= 7  → existing random sweep (boundary-respecting or
            //             ±2000 for unbounded)
            int strategy = restart % 8;
            std::size_t pinIdx = (restart / 8) % std::max<std::size_t>(vars.size(), 1);
            for (std::size_t i = 0; i < vars.size(); ++i) {
                const auto& v = vars[i];
                const auto* d = domains.getDomain(v);
                mpz_class val;
                switch (strategy) {
                    case 0:
                        val = 0;
                        break;
                    case 1:
                        val = (d && d->hasLower) ? d->lower.value : mpz_class(0);
                        break;
                    case 2:
                        val = (d && d->hasUpper) ? d->upper.value : mpz_class(0);
                        break;
                    case 3:
                        if (d && d->hasLower && d->hasUpper) {
                            val = (d->lower.value + d->upper.value) / 2;
                        } else {
                            val = 0;
                        }
                        break;
                    case 4:
                        val = (i == pinIdx) ? mpz_class((restart % 2 == 0) ? 100 : -100)
                                            : mpz_class(0);
                        break;
                    case 5:
                        val = (i == pinIdx) ? mpz_class((restart % 2 == 0) ? 500 : -500)
                                            : mpz_class(0);
                        break;
                    case 6:
                        val = mpz_class((long)(rng() % 21) - 10);
                        break;
                    default:
                        if (d && d->hasLower && d->hasUpper) {
                            mpz_class span = d->upper.value - d->lower.value;
                            val = (span <= 0) ? d->lower.value
                                              : d->lower.value + mpz_class(rng()) % (span + 1);
                        } else {
                            val = mpz_class((long)(rng() % 4001) - 2000);
                        }
                        break;
                }
                cur[v] = clampVar(v, val);
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

        // LS-VM1: pre-load pinned values into cur. The pinned-eq detection
        // ran ONCE above; here we apply the fixed values per restart so
        // every restart's starting trajectory respects the linear-equality
        // pins. Sound: pinning v to its forced value is verdict-preserving.
        for (const auto& [pv, pval] : pinned) {
            cur[pv] = pval;
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

            // LS-VM1: filter pinned vars out of the move-search candidate
            // set. A pinned var's value is forced by a linear equality;
            // perturbing it would just violate that equality without
            // helping the falsified atom (other moves toward the falsified
            // atom's satisfaction are tried via the remaining cvars).
            if (!pinned.empty()) {
                std::vector<std::string> filtered;
                filtered.reserve(cvars.size());
                for (const auto& v : cvars) {
                    if (!pinned.count(v)) filtered.push_back(v);
                }
                if (!filtered.empty()) cvars = std::move(filtered);
                // If EVERY var in cvars is pinned, leave cvars as-is so
                // the noise branch can still try a random nudge — the LS
                // is then effectively stuck on this atom, but we don't
                // skip the falsified atom (preserves walkSat semantics).
            }

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
                // P4 feasible-set jump (XOLVER_NIA_LS_FS_JUMP). Pull the
                // variable's DomainStore intervals into the candidate
                // set: boundaries, midpoint, finite-set elements, and
                // ±1 neighbours of excluded values. Yices2LS-style lazy
                // cell jump — sound because every candidate still
                // passes through the bestCost selection.
                if (fsJump_) {
                    const IntDomain* d = domains.getDomain(v);
                    if (d) {
                        if (d->hasLower) {
                            targets.push_back(d->lower.value);
                            targets.push_back(d->lower.value + 1);
                        }
                        if (d->hasUpper) {
                            targets.push_back(d->upper.value);
                            targets.push_back(d->upper.value - 1);
                        }
                        if (d->hasLower && d->hasUpper) {
                            mpz_class mid = (d->lower.value + d->upper.value) / 2;
                            targets.push_back(mid);
                            targets.push_back(mid - 1);
                            targets.push_back(mid + 1);
                        }
                        if (d->finiteValues) {
                            // Cap the finite-set contribution to keep the
                            // candidate loop bounded on pathological wide
                            // sets; small finite domains hit the limit far
                            // less than the cap.
                            std::size_t fcap = 64;
                            for (const auto& fv : *d->finiteValues) {
                                targets.push_back(fv);
                                if (--fcap == 0) break;
                            }
                        }
                        // ±1 neighbours of excluded values (jump OUT of
                        // the forbidden cell into the adjacent feasible
                        // one).
                        for (const auto& [ex, _r] : d->excludedValues) {
                            targets.push_back(ex - 1);
                            targets.push_back(ex + 1);
                        }
                    }
                }
                // P3 quadratic critical move (XOLVER_NIA_LS_QUAD_CRITICAL).
                // Three probes (orig, orig+1, orig+2) fit
                //   q(t) = a t² + b t + c   with t = (value - orig).
                // Solve at² + bt + c = 0 (and the inequality form) by the
                // discriminant; add integer-floor and -ceiling roots to
                // the candidate set. For a = 0 the polynomial is linear in
                // this variable and the Newton step below already handles
                // it; skip.
                if (quadCritical_ && p0 && p1) {
                    cur[v] = orig + 2;
                    auto p2 = kernel_.evalInteger(C.poly, cur);
                    cur[v] = orig;
                    if (p2) {
                        // 2a = p(2) - 2 p(1) + p(0).
                        mpz_class twoA = (*p2) - 2 * (*p1) + (*p0);
                        if (twoA != 0 && (twoA % 2 == 0)) {
                            mpz_class a = twoA / 2;
                            mpz_class b = (*p1) - (*p0) - a;
                            mpz_class c = *p0;
                            mpz_class D = b * b - 4 * a * c;
                            if (D >= 0) {
                                mpz_class sqD = isqrt(D);
                                mpz_class twoa = 2 * a;
                                auto pushRoot = [&](const mpz_class& numer) {
                                    if (twoa == 0) return;
                                    // Integer-floor of numer / twoa via
                                    // mpz fdiv (handles negative correctly).
                                    mpz_class q;
                                    mpz_fdiv_q(q.get_mpz_t(),
                                               numer.get_mpz_t(),
                                               twoa.get_mpz_t());
                                    for (int k = -1; k <= 1; ++k) {
                                        mpz_class t = q + k;
                                        if (t < -STEP_CAP) t = -STEP_CAP;
                                        if (t >  STEP_CAP) t =  STEP_CAP;
                                        targets.push_back(orig + t);
                                    }
                                    // Also the integer-ceiling root.
                                    mpz_class qc = q;
                                    mpz_class rem = numer - q * twoa;
                                    if (rem != 0) ++qc;
                                    if (qc < -STEP_CAP) qc = -STEP_CAP;
                                    if (qc >  STEP_CAP) qc =  STEP_CAP;
                                    targets.push_back(orig + qc);
                                };
                                pushRoot(-b - sqD);
                                pushRoot(-b + sqD);
                            }
                        }
                    }
                }
                if (p0 && p1) {
                    mpz_class slope = *p1 - *p0;
                    if (slope != 0) {
                        mpz_class step = -(*p0) / slope;  // discrete Newton
                        if (step < -STEP_CAP) step = -STEP_CAP;
                        if (step >  STEP_CAP) step =  STEP_CAP;
                        if (multiScale_) {
                            // P2 multi-scale: doubling series ±1, ±2, ±4,
                            // ±8, ... up to STEP_CAP. Exponential coverage
                            // for big jumps; also adds the discrete-Newton
                            // step and ±1 neighbours. NIA-distance LS-IA
                            // analog of LS-NRA's accelerated step.
                            for (int k = 0; (mpz_class(1) << k) <= STEP_CAP; ++k) {
                                mpz_class d = mpz_class(1) << k;
                                targets.push_back(orig + d);
                                targets.push_back(orig - d);
                            }
                            // Newton anchor + ±1 neighbours.
                            targets.push_back(orig + step);
                            targets.push_back(orig + step + 1);
                            targets.push_back(orig + step - 1);
                            // P2 √|val| target — for x²=N-style atoms,
                            // the satisfying x sits near ±√|val|. Cheap
                            // to add and dramatically helps on quadratic
                            // monomials that Newton-on-slope can miss.
                            if (*p0 != 0) {
                                mpz_class rt = isqrt(*p0);
                                if (rt > 0) {
                                    targets.push_back(orig + rt);
                                    targets.push_back(orig - rt);
                                    targets.push_back(orig + rt + 1);
                                    targets.push_back(orig - rt - 1);
                                }
                            }
                        } else {
                            // Legacy accelerated series around Newton step:
                            // step * (1.2^k) for k = 0..3 via ×6/5.
                            mpz_class s = step;
                            for (int k = 0; k < 4; ++k) {
                                targets.push_back(orig + s);
                                targets.push_back(orig + s + 1);
                                targets.push_back(orig + s - 1);
                                if (s == 0) break;
                                s = (s * 6) / 5;
                                if (s < -STEP_CAP) s = -STEP_CAP;
                                if (s >  STEP_CAP) s =  STEP_CAP;
                            }
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

            // P5 bilinear pair move (XOLVER_NIA_LS_BILINEAR_PAIR). For each
            // falsified atom's polynomial, look for a bilinear monomial
            // `coef * x * y` (two distinct variables each at exponent 1).
            // The current single-variable critical-move iterates one of x
            // or y at a time; for bilinear systems the SINGLE-var Newton
            // step is misleading because both factors interact. Joint
            // (x', y') candidates respect that interaction directly.
            //
            // Strategy for picking joint candidates:
            //   * Compute the bilinear product's "target value": the value
            //     `x*y` would need to take so the atom evaluates close to
            //     zero. The first-order linear estimate is
            //         target ≈ x_orig * y_orig - p(orig) / coef
            //     (1-step Newton on the product as a single quantity).
            //   * Iterate small divisors of |target| as factor pairs.
            //     For each divisor d, try (x = d, y = target / d) and
            //     (x = -d, y = -target / d). Caps at the first 16 pairs
            //     to bound per-flip cost.
            //   * Evaluate joint cost via a two-var move trial that
             //    incrementally re-evaluates only clauses containing
            //     either x or y.
            //
            // Soundness: every joint candidate still passes through the
            // bestCost selection; no verdict change.
            std::string bestPairVarX, bestPairVarY;
            mpz_class bestPairValX = 0, bestPairValY = 0;
            mpz_class bestPairCost = bestCost;
            bool havePairBest = false;
            if (bilinearPair_) {
                auto termsOpt = kernel_.terms(C.poly);
                if (termsOpt) {
                    // Locate first bilinear monomial: 2 distinct vars,
                    // each with exponent 1.
                    for (const auto& mono : *termsOpt) {
                        if (mono.powers.size() != 2) continue;
                        if (mono.powers[0].second != 1 ||
                            mono.powers[1].second != 1) continue;
                        std::string xname(kernel_.varName(mono.powers[0].first));
                        std::string yname(kernel_.varName(mono.powers[1].first));
                        if (xname == yname || xname.empty() || yname.empty())
                            continue;
                        // Only act on vars that appear in cvars (the
                        // current falsified constraint's variable set).
                        bool xIn = false, yIn = false;
                        for (const auto& cv : cvars) {
                            if (cv == xname) xIn = true;
                            if (cv == yname) yIn = true;
                        }
                        if (!xIn || !yIn) continue;
                        const mpz_class& coef = mono.coefficient;
                        if (coef == 0) continue;

                        const mpz_class xOrig = cur[xname];
                        const mpz_class yOrig = cur[yname];
                        auto pOrigOpt = kernel_.evalInteger(C.poly, cur);
                        if (!pOrigOpt) break;
                        const mpz_class pOrig = *pOrigOpt;
                        // Target: where coef*x*y should land so atom ≈ 0.
                        //   p(orig) ≈ coef * x_o * y_o + rest_o
                        //   want    : 0 = coef * x' * y' + rest_o
                        //   ⇒        x' * y' ≈ x_o * y_o - p(orig)/coef
                        mpz_class target = xOrig * yOrig;
                        // Integer-divide; mpz_class operator/ is truncation.
                        if (coef != 0) target -= pOrig / coef;
                        if (target == 0) {
                            // Trivial: one of x', y' = 0 satisfies the
                            // product. Try both single-zero candidates.
                            mpz_class delta;
                            mpz_class nc = tryMoveCost(xname, 0, delta);
                            if (nc < bestPairCost) {
                                bestPairCost = nc; bestPairVarX = xname;
                                bestPairValX = 0; havePairBest = true;
                                bestPairVarY.clear();  // single-var commit
                            }
                            continue;
                        }
                        // Helper: evaluate joint (x = a, y = b) cost via
                        // incremental clause re-eval on union of var
                        // clause sets.
                        auto tryJointCost = [&](const mpz_class& a,
                                                 const mpz_class& b) {
                            const mpz_class cxOrig = cur[xname];
                            const mpz_class cyOrig = cur[yname];
                            cur[xname] = a;
                            cur[yname] = b;
                            // Affected clauses = union(varToClauses[x],
                            //                          varToClauses[y]).
                            std::unordered_set<std::size_t> affected;
                            auto itx = varToClauses.find(xname);
                            auto ity = varToClauses.find(yname);
                            if (itx != varToClauses.end())
                                for (auto i : itx->second) affected.insert(i);
                            if (ity != varToClauses.end())
                                for (auto i : ity->second) affected.insert(i);
                            mpz_class delta = 0;
                            for (auto i : affected) {
                                mpz_class nv = evalCviol(i, cur);
                                delta += (nv - cviol[i]) * weight[i];
                            }
                            cur[xname] = cxOrig;
                            cur[yname] = cyOrig;
                            return weightedCost + delta;
                        };
                        // Iterate small-divisor factor pairs of |target|.
                        mpz_class absT = (target < 0) ? -target : target;
                        std::vector<std::pair<mpz_class, mpz_class>> pairs;
                        for (long d = 1; d <= 32; ++d) {
                            if (absT % d != 0) continue;
                            mpz_class a = d;
                            mpz_class b = target / d;
                            pairs.push_back({a, b});
                            pairs.push_back({-a, -b});
                            if (pairs.size() >= 16) break;
                        }
                        for (const auto& [a, b] : pairs) {
                            mpz_class ax = clampVar(xname, a);
                            mpz_class by = clampVar(yname, b);
                            if (ax == xOrig && by == yOrig) continue;
                            mpz_class nc = tryJointCost(ax, by);
                            if (nc < bestPairCost) {
                                bestPairCost = nc;
                                bestPairVarX = xname; bestPairValX = ax;
                                bestPairVarY = yname; bestPairValY = by;
                                havePairBest = true;
                            }
                        }
                        // Only consider the FIRST bilinear monomial per
                        // atom to keep per-flip cost bounded.
                        break;
                    }
                }
            }

            // Phase B (VeryMax PRIMARY) — bilinear-substitution move
            // (XOLVER_NIA_LS_BILINEAR_SUBST). For each (x, y) appearing
            // together in a monomial of the falsified atom, fix one at
            // its current value and treat the atom as univariate in the
            // other. If the residual is linear (a*v + b), solve directly
            // for v = -b/a; if quadratic (a*v^2 + b*v + c), test the
            // discriminant and admit integer roots. The candidates enter
            // the same bestCost selection as the discrete-Newton search
            // — soundness unchanged (validator-gated at function exit).
            //
            // Why it complements bilinearPair_: the pair move treats
            // `coef*x*y` as a single quantity and probes factor pairs of
            // its target. Substitution exploits the LINEAR structure left
            // when one factor is pinned, so atoms like `2*x*y + 3*x + y - 5`
            // (the `(2y+3)*x + (y-5)` residual is linear in x) get an
            // exact closed-form candidate that the product-pair strategy
            // misses entirely.
            if (bilinearSubst_) {
                // I3-derisk diagnostic. XOLVER_NIA_LS_DIAG=1 prints
                // per-flip the count of (var-pair, direction) attempts +
                // accepted candidate roots. Lets us confirm bilinearSubst
                // fires on real VeryMax atoms before claiming the lever
                // is broken vs just outbudget.
                static const bool diag = std::getenv("XOLVER_NIA_LS_DIAG") != nullptr;
                int diag_pairs = 0, diag_lin_roots = 0, diag_quad_roots = 0,
                    diag_cands = 0, diag_accepted = 0;
                auto termsOpt = kernel_.terms(C.poly);
                if (termsOpt) {
                    // Collect candidate (solveVarName) values across all
                    // distinct pairs of vars appearing together in a
                    // monomial, in both substitution directions. Cap on
                    // total pairs per flip to bound per-flip cost.
                    std::vector<std::pair<std::string,std::string>> bilPairs;
                    {
                        std::unordered_set<std::string> seen;
                        for (const auto& mono : *termsOpt) {
                            if (mono.powers.size() < 2) continue;
                            // For each ordered pair (xi, xj) with i < j
                            // record one canonical sorted (min,max) entry.
                            for (size_t i = 0; i + 1 < mono.powers.size(); ++i) {
                                for (size_t j = i + 1; j < mono.powers.size(); ++j) {
                                    std::string a = std::string(kernel_.varName(mono.powers[i].first));
                                    std::string b = std::string(kernel_.varName(mono.powers[j].first));
                                    if (a.empty() || b.empty() || a == b) continue;
                                    if (a > b) std::swap(a, b);
                                    std::string key = a + "\x00" + b;
                                    if (seen.insert(key).second) bilPairs.push_back({a, b});
                                    if (bilPairs.size() >= 8) break;
                                }
                                if (bilPairs.size() >= 8) break;
                            }
                            if (bilPairs.size() >= 8) break;
                        }
                    }
                    // For each pair (a, b), try fixing a and solving for
                    // b, then fixing b and solving for a. Track BOTH
                    // directions' roots so that a joint (root_x, root_y)
                    // candidate can be proposed at the end — derisk
                    // diagnostic showed single-var roots fire structurally
                    // but lose to existing moves on the GLOBAL weighted
                    // cost. A joint move respects the bilinear interaction
                    // in both dimensions and is much more likely to
                    // globally improve.
                    for (const auto& pair : bilPairs) {
                        std::vector<mpz_class> rootsFirst, rootsSecond;
                        for (int dir = 0; dir < 2; ++dir) {
                            const std::string& solveVar = (dir == 0) ? pair.first : pair.second;
                            // Both pair members must be in cvars (they
                            // are by construction — they appeared in
                            // C.poly's terms — but guard anyway).
                            bool inCvars = false;
                            for (const auto& cv : cvars) if (cv == solveVar) { inCvars = true; break; }
                            if (!inCvars) continue;
                            // Group residual polynomial by exponent of
                            // solveVar after substituting current values
                            // for every other variable. Resulting map:
                            //   exp -> sum of (coef * prod(other_var^e))
                            // where the product is over the term's
                            // non-solveVar factors evaluated at cur.
                            std::map<int, mpz_class> byDeg;
                            int maxDeg = 0;
                            bool subFailed = false;
                            for (const auto& mono : *termsOpt) {
                                int d = 0;
                                mpz_class coef = mono.coefficient;
                                for (const auto& [vid, e] : mono.powers) {
                                    std::string vn(kernel_.varName(vid));
                                    if (vn == solveVar) {
                                        d += e;
                                    } else {
                                        auto it = cur.find(vn);
                                        if (it == cur.end()) { subFailed = true; break; }
                                        mpz_class pw;
                                        mpz_pow_ui(pw.get_mpz_t(),
                                                   it->second.get_mpz_t(),
                                                   static_cast<unsigned long>(e));
                                        coef *= pw;
                                    }
                                }
                                if (subFailed) break;
                                byDeg[d] += coef;
                                if (d > maxDeg) maxDeg = d;
                            }
                            if (subFailed) continue;
                            // Solve residual == 0 for integer roots.
                            std::vector<mpz_class> roots;
                            mpz_class c0 = byDeg.count(0) ? byDeg[0] : mpz_class(0);
                            mpz_class c1 = byDeg.count(1) ? byDeg[1] : mpz_class(0);
                            if (diag) ++diag_pairs;
                            if (maxDeg <= 1) {
                                // a*v + b = 0 -> v = -b/a.
                                if (c1 != 0) {
                                    mpz_class neg = -c0;
                                    if ((neg % c1) == 0) { roots.push_back(neg / c1); if (diag) ++diag_lin_roots; }
                                }
                            } else if (maxDeg == 2) {
                                mpz_class c2 = byDeg.count(2) ? byDeg[2] : mpz_class(0);
                                if (c2 == 0) {
                                    // degenerate linear
                                    if (c1 != 0) {
                                        mpz_class neg = -c0;
                                        if ((neg % c1) == 0) { roots.push_back(neg / c1); if (diag) ++diag_lin_roots; }
                                    }
                                } else {
                                    // a*v^2 + b*v + c = 0: D = b^2 - 4ac
                                    mpz_class D = c1 * c1 - 4 * c2 * c0;
                                    if (D >= 0) {
                                        mpz_class sq;
                                        mpz_sqrt(sq.get_mpz_t(), D.get_mpz_t());
                                        if (sq * sq == D) {
                                            mpz_class denom = 2 * c2;
                                            mpz_class num1 = -c1 + sq;
                                            mpz_class num2 = -c1 - sq;
                                            if (denom != 0) {
                                                if ((num1 % denom) == 0) { roots.push_back(num1 / denom); if (diag) ++diag_quad_roots; }
                                                if ((num2 % denom) == 0) { roots.push_back(num2 / denom); if (diag) ++diag_quad_roots; }
                                            }
                                        }
                                    }
                                }
                            }
                            // (maxDeg >= 3 in solveVar is skipped — the
                            // closed form would lose integer guarantee.)
                            for (const auto& r : roots) {
                                mpz_class cand = clampVar(solveVar, r);
                                if (cand == cur[solveVar]) continue;
                                if (diag) ++diag_cands;
                                mpz_class delta;
                                mpz_class nc = tryMoveCost(solveVar, cand, delta);
                                if (!haveBest || nc < bestCost) {
                                    bestCost = nc;
                                    bestVar = solveVar;
                                    bestVal = cand;
                                    haveBest = true;
                                    if (diag) ++diag_accepted;
                                }
                                // Capture for the JOINT-move attempt below.
                                if (dir == 0) rootsFirst.push_back(cand);
                                else          rootsSecond.push_back(cand);
                            }
                        }
                        // JOINT-move attempt: for each (rx, ry) cross-
                        // product, evaluate global cost of moving BOTH
                        // pair members together. Most VeryMax atoms
                        // share their vars across many clauses; moving
                        // only one breaks neighbours, so the single-var
                        // candidate is rejected on global cost. Moving
                        // both jointly respects the bilinear interaction
                        // and is the move design master called for
                        // ("固定 y 找 x 范围, 固定 x 找 y 范围, 二维 cell").
                        if (!rootsFirst.empty() && !rootsSecond.empty()) {
                            const std::string& xn = pair.first;
                            const std::string& yn = pair.second;
                            int joint_tried = 0;
                            for (const auto& rx : rootsFirst) {
                                for (const auto& ry : rootsSecond) {
                                    if (++joint_tried > 4) break;  // cap per pair
                                    if (rx == cur[xn] && ry == cur[yn]) continue;
                                    // Inline joint-cost evaluation:
                                    // restore semantics identical to the
                                    // bilinearPair_ block's tryJointCost.
                                    const mpz_class cxOrig = cur[xn];
                                    const mpz_class cyOrig = cur[yn];
                                    cur[xn] = rx;
                                    cur[yn] = ry;
                                    std::unordered_set<std::size_t> affected;
                                    auto itx = varToClauses.find(xn);
                                    auto ity = varToClauses.find(yn);
                                    if (itx != varToClauses.end())
                                        for (auto i : itx->second) affected.insert(i);
                                    if (ity != varToClauses.end())
                                        for (auto i : ity->second) affected.insert(i);
                                    mpz_class jdelta = 0;
                                    for (auto i : affected) {
                                        mpz_class nv = evalCviol(i, cur);
                                        jdelta += (nv - cviol[i]) * weight[i];
                                    }
                                    cur[xn] = cxOrig;
                                    cur[yn] = cyOrig;
                                    mpz_class jc = weightedCost + jdelta;
                                    if (jc < bestPairCost) {
                                        bestPairCost = jc;
                                        bestPairVarX = xn;
                                        bestPairValX = rx;
                                        bestPairVarY = yn;
                                        bestPairValY = ry;
                                        havePairBest = true;
                                        if (diag) ++diag_accepted;
                                    }
                                }
                                if (joint_tried > 4) break;
                            }
                        }
                    }
                }
                if (diag && (diag_pairs > 0 || diag_lin_roots > 0 || diag_cands > 0)) {
                    static thread_local int diag_flip = 0;
                    ++diag_flip;
                    if ((diag_flip & 63) == 1) {
                        std::fprintf(stderr,
                            "[LS-BSUBST] flip=%d pairs=%d lin=%d quad=%d cands=%d accepted=%d\n",
                            diag_flip, diag_pairs, diag_lin_roots, diag_quad_roots,
                            diag_cands, diag_accepted);
                    }
                }
            }

            // P5: if the pair move beats the single-var best, use it.
            bool usePair = havePairBest && bestPairCost < bestCost;

            // Noise: with prob NOISE/10, ignore the best move and random-nudge.
            if (((int)(rng() % 10) < NOISE) ||
                (!haveBest && !usePair) ||
                (usePair ? (bestPairCost >= weightedCost) : (bestCost >= weightedCost))) {
                const std::string& v = cvars[rng() % cvars.size()];
                long nudge = (long)(rng() % 21) - 10;
                if (nudge == 0) nudge = 1;
                mpz_class newVal = clampVar(v, cur[v] + nudge);
                commitMove(v, newVal);
                sinceImprove++;
            } else if (usePair) {
                // Joint pair commit: update both x and y, then incrementally
                // refresh affected clauses (each commitMove call handles
                // its own var's clause set).
                if (!bestPairVarY.empty()) {
                    commitMove(bestPairVarX, bestPairValX);
                    commitMove(bestPairVarY, bestPairValY);
                    // I1: varActivity is a cheap counter and is needed as a
                    // branch-hint signal even when warm-start state isn't
                    // being persisted across cb_check (XOLVER_NIA_LS_BRANCH_HINT).
                    lsContext_.varActivity[bestPairVarX]++;
                    lsContext_.varActivity[bestPairVarY]++;
                } else {
                    commitMove(bestPairVarX, bestPairValX);
                    lsContext_.varActivity[bestPairVarX]++;
                }
                sinceImprove = 0;
            } else {
                commitMove(bestVar, bestVal);
                sinceImprove = 0;
                lsContext_.varActivity[bestVar]++;
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
