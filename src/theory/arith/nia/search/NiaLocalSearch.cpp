#include "theory/arith/nia/search/NiaLocalSearch.h"
#include <random>
#include <algorithm>
#include <cstdlib>
#include <functional>

namespace zolver {

NiaLocalSearch::NiaLocalSearch(PolynomialKernel& kernel)
    : kernel_(kernel),
      slsEnabled_(std::getenv("ZOLVER_NIA_LOCALSEARCH") != nullptr) {}

bool NiaLocalSearch::satisfies(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {
    for (const auto& c : constraints) {
        auto val = kernel_.evalInteger(c.poly, model);
        if (!val) return false; // can't evaluate -> not a confirmed model
        const mpz_class& v = *val;
        bool ok = false;
        switch (c.rel) {
            case Relation::Eq:  ok = (v == 0); break;
            case Relation::Neq: ok = (v != 0); break;
            case Relation::Lt:  ok = (v < 0);  break;
            case Relation::Leq: ok = (v <= 0); break;
            case Relation::Gt:  ok = (v > 0);  break;
            case Relation::Geq: ok = (v >= 0); break;
        }
        if (!ok) return false;
    }
    return true;
}

std::optional<IntegerModel> NiaLocalSearch::tryFindModelSls(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    uint64_t seed) {

    if (constraints.empty()) return IntegerModel{};

    // Variables in deterministic order.
    std::vector<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            if (std::find(vars.begin(), vars.end(), v) == vars.end()) {
                vars.push_back(v);
            }
        }
    }
    if (vars.empty()) {
        // Purely constant system: satisfiable iff the constants check out.
        IntegerModel empty;
        return satisfies(empty, constraints) ? std::optional<IntegerModel>(empty)
                                             : std::nullopt;
    }

    // Per-variable search window: domain bounds when known, else a symmetric
    // integer window around 0. SLS targets small/moderate-magnitude models.
    const mpz_class kWindow = 128;
    struct VarRange { mpz_class lo, hi; bool hasLo, hasHi; };
    std::vector<VarRange> ranges(vars.size());
    for (size_t i = 0; i < vars.size(); ++i) {
        const auto* d = domains.getDomain(vars[i]);
        ranges[i].hasLo = d && d->hasLower;
        ranges[i].hasHi = d && d->hasUpper;
        ranges[i].lo = ranges[i].hasLo ? d->lower.value : -kWindow;
        ranges[i].hi = ranges[i].hasHi ? d->upper.value :  kWindow;
        if (ranges[i].lo > ranges[i].hi) ranges[i].hi = ranges[i].lo; // degenerate
    }

    std::mt19937_64 rng(seed);
    auto randInRange = [&](size_t i) -> mpz_class {
        const mpz_class& lo = ranges[i].lo;
        const mpz_class& hi = ranges[i].hi;
        mpz_class span = hi - lo;                 // >= 0
        if (span == 0) return lo;
        // span+1 may exceed 64 bits for huge domains; cap the sampled span.
        mpz_class cap = 2 * kWindow;              // 256-wide sampling window
        mpz_class width = (span < cap) ? span : cap;
        std::uniform_int_distribution<long> dist(0, width.get_si());
        mpz_class off(dist(rng));
        mpz_class base = ranges[i].hasLo ? lo : mpz_class(-kWindow);
        mpz_class val = base + off;
        if (val < lo) val = lo;
        if (val > hi) val = hi;
        return val;
    };
    auto clampVar = [&](size_t i, mpz_class v) -> mpz_class {
        if (v < ranges[i].lo) v = ranges[i].lo;
        if (v > ranges[i].hi) v = ranges[i].hi;
        return v;
    };

    // Move deltas: small steps plus geometric jumps to reach distant roots.
    const long deltas[] = {1, -1, 2, -2, 4, -4, 8, -8,
                           16, -16, 32, -32, 64, -64};

    const int kRestarts = 24;
    const int kStepsPerRestart = 120;
    const double kNoise = 0.3;
    std::uniform_real_distribution<double> coin(0.0, 1.0);

    IntegerModel best;
    for (const auto& v : vars) best[v] = 0;
    mpz_class bestViol = violation(best, constraints);
    if (bestViol == 0 && satisfies(best, constraints)) return best;

    for (int restart = 0; restart < kRestarts; ++restart) {
        IntegerModel cur;
        if (restart == 0) {
            for (const auto& v : vars) cur[v] = 0; // deterministic first start
        } else {
            for (size_t i = 0; i < vars.size(); ++i) cur[vars[i]] = randInRange(i);
        }
        mpz_class curViol = violation(cur, constraints);
        if (curViol == 0 && satisfies(cur, constraints)) return cur;
        if (curViol < bestViol) { best = cur; bestViol = curViol; }

        for (int step = 0; step < kStepsPerRestart; ++step) {
            // Pick a violated constraint to focus on.
            std::vector<size_t> violated;
            for (size_t ci = 0; ci < constraints.size(); ++ci) {
                auto val = kernel_.evalInteger(constraints[ci].poly, cur);
                if (!val) continue;
                mpz_class pen = 0;
                const mpz_class& vv = *val;
                switch (constraints[ci].rel) {
                    case Relation::Eq:  pen = abs(vv); break;
                    case Relation::Neq: pen = (vv == 0) ? mpz_class(1) : mpz_class(0); break;
                    case Relation::Lt:  pen = (vv < 0)  ? mpz_class(0) : (vv + 1); break;
                    case Relation::Leq: pen = (vv <= 0) ? mpz_class(0) : vv; break;
                    case Relation::Gt:  pen = (vv > 0)  ? mpz_class(0) : (1 - vv); break;
                    case Relation::Geq: pen = (vv >= 0) ? mpz_class(0) : -vv; break;
                }
                if (pen > 0) violated.push_back(ci);
            }
            if (violated.empty()) {
                // Heuristic says satisfied — confirm exactly.
                if (satisfies(cur, constraints)) return cur;
                break; // scorer/relation mismatch; restart
            }
            size_t pick = violated[
                std::uniform_int_distribution<size_t>(0, violated.size() - 1)(rng)];
            const auto& focus = constraints[pick];
            std::vector<std::string> fvars = kernel_.variables(focus.poly);
            if (fvars.empty()) break; // unsatisfiable constant constraint; restart

            auto varIndex = [&](const std::string& name) -> size_t {
                for (size_t i = 0; i < vars.size(); ++i)
                    if (vars[i] == name) return i;
                return vars.size();
            };

            bool applied = false;
            if (coin(rng) < kNoise) {
                // Random walk: random variable in the focus constraint, random delta.
                const std::string& vname =
                    fvars[std::uniform_int_distribution<size_t>(0, fvars.size() - 1)(rng)];
                size_t vi = varIndex(vname);
                if (vi < vars.size()) {
                    long d = deltas[
                        std::uniform_int_distribution<size_t>(
                            0, sizeof(deltas) / sizeof(deltas[0]) - 1)(rng)];
                    IntegerModel next = cur;
                    next[vname] = clampVar(vi, cur[vname] + d);
                    if (next[vname] != cur[vname]) {
                        cur = std::move(next);
                        curViol = violation(cur, constraints);
                        applied = true;
                    }
                }
            }
            if (!applied) {
                // Greedy: best neighbor over (focus var, delta), ties broken randomly.
                IntegerModel bestNext = cur;
                mpz_class bestNextViol = curViol;
                int ties = 0;
                for (const auto& vname : fvars) {
                    size_t vi = varIndex(vname);
                    if (vi >= vars.size()) continue;
                    for (long d : deltas) {
                        IntegerModel next = cur;
                        next[vname] = clampVar(vi, cur[vname] + d);
                        if (next[vname] == cur[vname]) continue;
                        mpz_class nv = violation(next, constraints);
                        if (nv < bestNextViol) {
                            bestNextViol = nv; bestNext = std::move(next); ties = 1;
                        } else if (nv == bestNextViol) {
                            // reservoir tie-break for determinism + diversity
                            if (std::uniform_int_distribution<int>(0, ties)(rng) == 0)
                                bestNext = std::move(next);
                            ++ties;
                        }
                    }
                }
                cur = std::move(bestNext);
                curViol = bestNextViol;
            }

            if (curViol == 0 && satisfies(cur, constraints)) return cur;
            if (curViol < bestViol) { best = cur; bestViol = curViol; }
        }
    }

    return std::nullopt;
}

mpz_class NiaLocalSearch::violation(
    const IntegerModel& model,
    const std::vector<NormalizedNiaConstraint>& constraints) const {

    mpz_class total = 0;
    for (const auto& c : constraints) {
        auto valOpt = kernel_.evalInteger(c.poly, model);
        if (!valOpt) continue;
        mpz_class val = *valOpt;
        mpz_class v = 0;
        switch (c.rel) {
            case Relation::Eq:  v = abs(val); break;
            case Relation::Neq: v = (val == 0) ? mpz_class(1) : mpz_class(0); break;
            case Relation::Lt:  v = (val < 0) ? mpz_class(0) : val; break;
            case Relation::Leq: v = (val <= 0) ? mpz_class(0) : val; break;
            case Relation::Gt:  v = (val > 0) ? mpz_class(0) : -val; break;
            case Relation::Geq: v = (val >= 0) ? mpz_class(0) : -val; break;
        }
        total += v * v;
    }
    return total;
}

std::optional<IntegerModel> NiaLocalSearch::tryFindModel(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains) {

    if (constraints.empty()) return IntegerModel{};

    // Collect variables in deterministic order
    std::vector<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            if (std::find(vars.begin(), vars.end(), v) == vars.end()) {
                vars.push_back(v);
            }
        }
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

    // No satisfying assignment found.
    // (Focused SLS is invoked separately by NiaSolver::stageLocalSearch, gated
    // to full effort, so it does not run on every check.)
    return std::nullopt;
}

} // namespace zolver
