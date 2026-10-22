#include "base/RuntimeConfig.h"
#include "search/nia/search/NiaLocalSearch.h"
#include "base/SolveClock.h"
#include <random>
#include <algorithm>
#include <functional>
#include <chrono>
#include <unordered_set>

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
    // 0 or negative = unlimited; unset keeps the ctor-init default.
    budgetMs_ = config::read<config::ReadKind::Long>("XOLVER_NIA_LS_BUDGET_MS", budgetMs_);
    totalBudgetMs_ = config::read<config::ReadKind::Long>("XOLVER_NIA_LS_TOTAL_MS", totalBudgetMs_);
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
    // Budget grows to ~1/3 of wall-clock remaining when XOLVER_WALLCLOCK_SCALE
    // is on (else == totalBudgetMs_), computed live so it tracks time left.
    if (totalBudgetMs_ > 0 &&
        cumulativeMs_ >= wall::scaledBudgetMs(totalBudgetMs_, 1, 3))
        return std::nullopt;

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

    // Collect variables in deterministic order.
    // iter-108 perf: parallel hash-set for O(1) dedup instead of O(|vars|)
    // std::find per insertion. Total cost falls from O(C × K × accumulated)
    // to O(C × K) where C = constraints, K = avg vars-per-constraint.
    std::vector<std::string> vars;
    std::unordered_set<std::string> varsSeen;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            if (varsSeen.insert(v).second) {
                vars.push_back(v);
            }
        }
    }

    // Search for an integer candidate, then fall back to the bounded sweep.
    // NiaSolver independently validates candidates before accepting SAT.
    if (!vars.empty()) {
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

} // namespace xolver
