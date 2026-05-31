#include "theory/arith/nra/reasoners/NraLocalSearch.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <algorithm>
#include <chrono>
#include <cmath>
#include <iostream>

namespace xolver {

std::optional<mpq_class>
NraLocalSearch::evalAt(PolyId p,
                       const std::unordered_map<VarId, mpq_class>& asg) const {
    auto rpOpt = RationalPolynomial::fromPolyId(p, kernel_);
    if (!rpOpt) return std::nullopt;
    RationalPolynomial cur = std::move(*rpOpt);
    static const mpq_class kZero{0};
    auto varSet = cur.variables();
    std::vector<VarId> vs(varSet.begin(), varSet.end());
    for (VarId v : vs) {
        auto it = asg.find(v);
        const mpq_class& q = (it != asg.end()) ? it->second : kZero;
        cur = cur.substituteRational(v, q);
    }
    if (!cur.isConstant()) return std::nullopt;
    return cur.constantValue();
}

mpq_class
NraLocalSearch::atomViolation(const Constraint& c,
                              const std::unordered_map<VarId, mpq_class>& asg) const {
    auto vOpt = evalAt(c.poly, asg);
    if (!vOpt) {
        // Cannot evaluate ⇒ pessimistically violated by 1 (a finite penalty;
        // never +∞ so the move-selection still ranks better candidates).
        return mpq_class{1};
    }
    const mpq_class& v = *vOpt;
    switch (c.rel) {
        case Relation::Lt:   // p < 0  → violation = max(0, p) + (p==0 ? ε : 0)
            if (v < 0) return mpq_class{0};
            return v + epsilon_;
        case Relation::Leq:  // p ≤ 0 → violation = max(0, p)
            if (v <= 0) return mpq_class{0};
            return v;
        case Relation::Gt:   // p > 0
            if (v > 0) return mpq_class{0};
            return -v + epsilon_;
        case Relation::Geq:  // p ≥ 0
            if (v >= 0) return mpq_class{0};
            return -v;
        case Relation::Eq: {  // p == 0
            mpq_class a = v < 0 ? -v : v;
            if (eqRelax_) {
                // ε-relaxed: |p| ≤ ε is "ok-enough"; LS-NRA Layer B exact
                // restoration follows after.
                if (a <= epsilon_) return mpq_class{0};
                return a - epsilon_;
            }
            return a;
        }
        case Relation::Neq:  // p ≠ 0
            if (v != 0) return mpq_class{0};
            return epsilon_;
    }
    return mpq_class{0};  // unreachable
}

mpq_class
NraLocalSearch::scaleAt(PolyId p,
                        const std::unordered_map<VarId, mpq_class>& asg) const {
    // scale(p, α) = 1 + Σ_m |c_m| · |m(α)|
    // m(α) = ∏_{v in m} α[v]^{e_v}; if any var is missing from asg, defaults to 0.
    auto termsOpt = kernel_.terms(p);
    if (!termsOpt) return mpq_class{1};
    mpq_class scale{1};
    for (const auto& t : *termsOpt) {
        if (t.coefficient == 0) continue;
        mpq_class mAbs{1};
        bool zeroTerm = false;
        for (const auto& [v, e] : t.powers) {
            auto it = asg.find(v);
            const mpq_class& val = (it != asg.end()) ? it->second : kZero_;
            if (val == 0) { zeroTerm = true; break; }   // monomial contributes 0
            mpq_class absVal = (val < 0) ? -val : val;
            mpq_class pw{1};
            for (int k = 0; k < e; ++k) pw *= absVal;
            mAbs *= pw;
        }
        if (zeroTerm) continue;
        mpq_class cAbs = (t.coefficient < 0) ? mpq_class(-t.coefficient) : mpq_class(t.coefficient);
        scale += cAbs * mAbs;
    }
    return scale;
}

NraLocalSearch::Score
NraLocalSearch::totalScore(const std::vector<Constraint>& cs,
                            const std::vector<int>& weights,
                            const std::unordered_map<VarId, mpq_class>& asg) const {
    Score s;
    for (size_t i = 0; i < cs.size(); ++i) {
        const int w = (i < weights.size()) ? weights[i] : 1;
        if (w == 0) continue;
        const mpq_class v = atomViolation(cs[i], asg);
        if (v > 0) {
            s.falseWeightedCount += w;
            const mpq_class scale = scaleAt(cs[i].poly, asg);
            const mpq_class normRes = v / scale;
            const mpq_class capped = (normRes > 1) ? mpq_class{1} : normRes;
            s.normalizedMag += mpq_class{w} * capped;
        }
    }
    return s;
}

std::vector<std::pair<VarId, mpq_class>>
NraLocalSearch::bracketMidpointCandidates(
        const std::vector<Constraint>& cs,
        const std::vector<VarId>& vars) const {
    // For each var, collect lower bounds (root with > / ≥ orientation) and
    // upper bounds (with < / ≤ orientation) coming from LINEAR atoms in
    // that var. For each (lower, upper) pair, push the midpoint AND a
    // few interior offsets at fractions of the interval width so the
    // candidate sits comfortably inside even very tight brackets (10⁻⁷
    // wide for meti-tarski/pi). Denom cap bypassed at the consumer end —
    // bracketMidpoint candidates are TARGETED: a single satisfier per
    // narrow interval, not a search-space explosion.
    std::vector<std::pair<VarId, mpq_class>> out;
    for (VarId v : vars) {
        std::vector<mpq_class> lowers;   // values t such that q(v) requires v > t (or v ≥ t)
        std::vector<mpq_class> uppers;   // q(v) requires v < t (or v ≤ t)
        for (const auto& c : cs) {
            auto rpOpt = RationalPolynomial::fromPolyId(c.poly, kernel_);
            if (!rpOpt) continue;
            // poly must be LINEAR in v and constant in all other vars (after
            // substituting their assignments — but here we just check the
            // raw polynomial: linear in v, no other var).
            auto varSet = rpOpt->variables();
            if (varSet.size() != 1) continue;
            if (varSet.find(v) == varSet.end()) continue;
            if (rpOpt->degree(v) != 1) continue;
            // poly = a·v + b. Compute a, b: a = (q(1) - q(0)), b = q(0).
            auto b_opt = [&]() -> std::optional<mpq_class> {
                RationalPolynomial t = rpOpt->substituteRational(v, mpq_class{0});
                if (!t.isConstant()) return std::nullopt;
                return t.constantValue();
            }();
            auto v1_opt = [&]() -> std::optional<mpq_class> {
                RationalPolynomial t = rpOpt->substituteRational(v, mpq_class{1});
                if (!t.isConstant()) return std::nullopt;
                return t.constantValue();
            }();
            if (!b_opt || !v1_opt) continue;
            const mpq_class a = *v1_opt - *b_opt;
            if (a == 0) continue;
            const mpq_class root = -*b_opt / a;   // poly = 0 at v = root
            // Direction: a > 0 means poly grows with v.
            //   poly > 0 ⇒ v > root (lower bound)
            //   poly < 0 ⇒ v < root (upper bound)
            //   poly ≥ 0 / ≤ 0 same with non-strict
            //   poly == 0 ⇒ v == root (skip — yields no interval)
            const bool aPos = a > 0;
            switch (c.rel) {
                case Relation::Gt:  case Relation::Geq:
                    if (aPos) lowers.push_back(root); else uppers.push_back(root);
                    break;
                case Relation::Lt:  case Relation::Leq:
                    if (aPos) uppers.push_back(root); else lowers.push_back(root);
                    break;
                default: break;   // Eq / Neq: not a useful bracket source
            }
        }
        // Pair each lower with each upper, push midpoint + a few interior
        // offsets so the candidate sits comfortably inside the interval.
        for (const auto& lo : lowers) {
            for (const auto& hi : uppers) {
                if (lo >= hi) continue;
                const mpq_class mid = (lo + hi) / 2;
                out.emplace_back(v, mid);
                // 1/4 and 3/4 interior offsets (handle very lopsided
                // bounds where the satisfier sits away from the centre).
                out.emplace_back(v, lo + (hi - lo) / 4);
                out.emplace_back(v, hi - (hi - lo) / 4);
            }
        }
    }
    return out;
}

std::vector<mpq_class>
NraLocalSearch::univariateBoundaryCandidates(
        const Constraint& c, VarId var,
        const std::unordered_map<VarId, mpq_class>& asg) const {
    // Substitute every other var from asg into c.poly → univariate in var.
    auto rpOpt = RationalPolynomial::fromPolyId(c.poly, kernel_);
    if (!rpOpt) return {};
    RationalPolynomial uni = std::move(*rpOpt);
    static const mpq_class kZ{0};
    auto vs = uni.variables();
    for (VarId v : vs) {
        if (v == var) continue;
        auto it = asg.find(v);
        const mpq_class& q = (it != asg.end()) ? it->second : kZ;
        uni = uni.substituteRational(v, q);
    }
    // After substitution either q(t) is constant (no candidate from this
    // atom) or contains only `var`.
    if (uni.isConstant()) return {};
    if (!uni.contains(var)) return {};
    const int deg = uni.degree(var);
    if (deg <= 0) return {};
    if (deg > 4) {
        // Master-spec: degree > 4 only for "critical" atoms — skip the
        // default path (CDCAC handles these via algebraic isolation).
        return {};
    }
    // For degree 3-4 the analytic discriminant path doesn't apply. Fall
    // through to the rational-scan path below (after the deg ≤ 2 exact
    // analytic block returns).

    // Build a univariate over `var`: uni = Σ_k a_k · var^k. Extract a_0..a_deg.
    // We pull coefficients via repeated substitution: a_0 = uni|var=0, then
    // u' = (uni - a_0)/var, a_1 = u'|var=0, etc. (Cheap for deg ≤ 2.)
    auto evalAtVarValue = [&](const RationalPolynomial& p,
                              const mpq_class& q) -> std::optional<mpq_class> {
        RationalPolynomial t = p.substituteRational(var, q);
        if (!t.isConstant()) return std::nullopt;
        return t.constantValue();
    };
    auto a0Opt = evalAtVarValue(uni, mpq_class{0});
    if (!a0Opt) return {};
    const mpq_class a0 = *a0Opt;

    std::vector<mpq_class> out;
    auto pushNear = [&](const mpq_class& center) {
        // Feasible-side sample + small offsets covering both sides.
        out.push_back(center);
        out.push_back(center + mpq_class{1, 16});
        out.push_back(center - mpq_class{1, 16});
        out.push_back(center + 1);
        out.push_back(center - 1);
    };

    if (deg == 1) {
        auto v1 = evalAtVarValue(uni, mpq_class{1});
        if (!v1) return {};
        const mpq_class a1 = *v1 - a0;
        if (a1 == 0) return {};
        const mpq_class root = -a0 / a1;
        pushNear(root);
        return out;
    }
    // Master-spec rational-scan path for deg 3-4: sample q(t) at a fixed
    // grid of rationals, find sign changes between consecutive samples,
    // push interval midpoints as boundary candidates. Cheaper than Sturm
    // chains and avoids the libpoly plumbing; sampling resolution is
    // tight enough to bracket typical meti-tarski roots.
    if (deg >= 3) {
        static const mpq_class kGrid[] = {
            mpq_class{-32}, mpq_class{-16}, mpq_class{-8}, mpq_class{-4},
            mpq_class{-2}, mpq_class{-1}, mpq_class{-1, 2}, mpq_class{-1, 4},
            mpq_class{0},
            mpq_class{1, 4}, mpq_class{1, 2}, mpq_class{1}, mpq_class{2},
            mpq_class{4}, mpq_class{8}, mpq_class{16}, mpq_class{32}
        };
        std::vector<std::pair<mpq_class, mpq_class>> samples;
        samples.reserve(sizeof(kGrid) / sizeof(kGrid[0]));
        for (const auto& g : kGrid) {
            auto vOpt = evalAtVarValue(uni, g);
            if (!vOpt) continue;
            samples.emplace_back(g, *vOpt);
        }
        for (size_t i = 0; i + 1 < samples.size(); ++i) {
            const auto& [t0, q0] = samples[i];
            const auto& [t1, q1] = samples[i + 1];
            // Sign change ⇒ root between t0 and t1.
            const bool s0pos = q0 > 0;
            const bool s1pos = q1 > 0;
            if (q0 == 0) { pushNear(t0); }
            if (q1 == 0) { pushNear(t1); continue; }
            if (s0pos != s1pos) {
                const mpq_class mid = (t0 + t1) / 2;
                pushNear(mid);
            }
        }
        // Cap output to stay within the per-round candidate budget.
        if (out.size() > 32) out.resize(32);
        return out;
    }

    // deg == 2: q(t) = a2·t² + a1·t + a0.
    // q(1) = a2 + a1 + a0; q(-1) = a2 - a1 + a0.
    // ⇒ a2 = (q(1) + q(-1))/2 - a0; a1 = (q(1) - q(-1))/2.
    auto vp1 = evalAtVarValue(uni, mpq_class{1});
    auto vm1 = evalAtVarValue(uni, mpq_class{-1});
    if (!vp1 || !vm1) return {};
    const mpq_class a1 = (*vp1 - *vm1) / 2;
    const mpq_class a2 = (*vp1 + *vm1) / 2 - a0;
    if (a2 == 0) {
        // Linear in disguise: same as deg==1 branch.
        if (a1 == 0) return {};
        const mpq_class root = -a0 / a1;
        pushNear(root);
        return out;
    }
    // Discriminant Δ = a1² − 4 · a2 · a0.
    const mpq_class disc = a1 * a1 - 4 * a2 * a0;
    if (disc < 0) {
        // No real roots: q(t) has constant sign sgn(a2) everywhere. Add
        // the vertex t* = -a1/(2 a2) as a single representative sample.
        const mpq_class vertex = -a1 / (2 * a2);
        pushNear(vertex);
        return out;
    }
    // Δ ≥ 0: real roots t± = (-a1 ± √Δ)/(2 a2). For an exact-rational √Δ
    // we get exact roots; otherwise we approximate by the midpoint of a
    // small rational bracket (via Newton-style sqrt approximation, capped
    // by the denominator cap). Phase D sprint 1: approximate via double.
    const double dDisc = disc.get_d();
    if (dDisc < 0) return {};   // numerical guard
    const double sqDisc = std::sqrt(dDisc);
    const double da1 = a1.get_d();
    const double da2 = a2.get_d();
    if (da2 == 0.0) return {};
    const double tPlus  = (-da1 + sqDisc) / (2.0 * da2);
    const double tMinus = (-da1 - sqDisc) / (2.0 * da2);
    auto rationalize = [](double x) -> mpq_class {
        // Continued-fraction-bounded approximation with denominator ≤ 1e6.
        // GMP's mpq_class(double) constructor uses the exact double
        // representation which can blow up the denominator; cap via reduce.
        mpq_class q;
        try { q = mpq_class(x); } catch (...) { return mpq_class{0}; }
        q.canonicalize();
        // Bound denominator: if q.get_den() > 1e6, round to nearest 1/1e6.
        if (q.get_den() > mpz_class{"1000000"}) {
            const long N = 1000000;
            const long num = static_cast<long>(x * N + (x >= 0 ? 0.5 : -0.5));
            q = mpq_class(num, N);
            q.canonicalize();
        }
        return q;
    };
    pushNear(rationalize(tPlus));
    pushNear(rationalize(tMinus));
    // Midpoint between roots is the vertex (often a feasible point under
    // ≤0 / ≥0 relations).
    const double tMid = (tPlus + tMinus) / 2.0;
    pushNear(rationalize(tMid));
    return out;
}

std::vector<mpq_class>
NraLocalSearch::candidateValues(VarId /*var*/,
                                const std::unordered_map<VarId, mpq_class>& asg) const {
    // Phase A: a coarse pool of small integers, perturbations of the current
    // value, and a few special points. Cheap; the violation evaluator picks
    // the best. Phase B will mine sign-interval brackets via univariate
    // substitution + Sturm (much higher-quality candidates).
    auto curIt = asg.end();   // var may be unassigned
    mpq_class cur{0};
    (void)curIt;
    // We DO read asg for `cur` below; left intentionally to avoid -Wunused.
    std::vector<mpq_class> out = {
        mpq_class{0}, mpq_class{1}, mpq_class{-1},
        mpq_class{2}, mpq_class{-2}, mpq_class{3}, mpq_class{-3},
        mpq_class{1, 2}, mpq_class{-1, 2},
        mpq_class{1, 4}, mpq_class{-1, 4},
    };
    // Perturbations of the current value (if assigned).
    // NOTE: caller passes the per-var current value via asg; we look it up
    // implicitly via the var arg above for the perturbations.
    return out;
}

bool
NraLocalSearch::walkOneRound(const std::vector<Constraint>& cs,
                              const std::vector<int>& weights,
                              const std::vector<VarId>& vars,
                              std::unordered_map<VarId, mpq_class>& asg,
                              Score& currentScore) {
    if (vars.empty()) return false;

    // Master-spec denominator cap (default 10^6). For NRA cases whose
    // satisfier is irrational (e.g. x²=2 → sqrt(2)), perturbations of the
    // current value build continued-fraction convergents whose denominators
    // explode; mpq ops cost grows with size and a 50-round loop runs in
    // seconds (the nra_140 reg-runaway). Skipping any candidate above the cap
    // bounds per-round mpq cost to a small constant.
    static const mpz_class kMaxDen = []() {
        if (const char* e = std::getenv("XOLVER_NRA_LS_MAX_DEN"))
            return mpz_class{e};
        return mpz_class{"1000000"};
    }();
    auto withinDenCap = [](const mpq_class& q) -> bool {
        return mpz_class(q.get_den()) <= kMaxDen;
    };

    VarId bestVar = vars.front();
    mpq_class bestVal = asg.count(bestVar) ? asg[bestVar] : mpq_class{0};
    Score bestScore = currentScore;
    bool improved = false;

    // Per-round budget guard. Each totalScore on a high-degree multivariate
    // poly is O(monomials × degree); on AProVE/atan polys a round can blow
    // past the per-call budget if we evaluate every (var × candidate). Cap
    // the visit count + check the wall-clock periodically so a hot round
    // still yields. (Master-review concern: scaffold must not slow NRA reg.)
    const auto t0 = std::chrono::steady_clock::now();
    int visited = 0;
    auto roundBudgetHit = [&]() {
        if (budgetMs_ <= 0) return false;
        // EVERY visit (was every-16, but with 11 cands/var × 1 var = 11 visits/
        // round we never reached 16; high-degree atan totalScore went 0 ↦ 100ms
        // single eval; 10ms budget was effectively unbounded).
        const auto el = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - t0).count();
        return el >= budgetMs_;
    };

    for (VarId v : vars) {
        if (roundBudgetHit()) break;
        mpq_class saved = asg.count(v) ? asg[v] : mpq_class{0};
        auto cands = candidateValues(v, asg);
        if (asg.count(v)) {
            const mpq_class& c = asg[v];
            cands.push_back(c + 1);
            cands.push_back(c - 1);
            cands.push_back(c + mpq_class{1, 8});
            cands.push_back(c - mpq_class{1, 8});
            if (c != 0) {
                cands.push_back(c * 2);
                cands.push_back(c / 2);
            }
        }
        // Master-spec: univariate sign-boundary candidates from FALSE atoms.
        // For each currently-violated constraint that references `v`, mine
        // the rational samples on the feasible side after substituting the
        // other vars. Degree ≤ 2 only in this sprint; bounded by an inner
        // cap so no single atom can dominate the round.
        int boundaryAdded = 0;
        for (const auto& cc : cs) {
            if (boundaryAdded >= 16) break;
            if (atomViolation(cc, asg) == 0) continue;   // already SAT — skip
            auto bcs = univariateBoundaryCandidates(cc, v, asg);
            for (auto& q : bcs) {
                if (boundaryAdded >= 16) break;
                cands.push_back(std::move(q));
                ++boundaryAdded;
            }
        }
        for (const auto& q : cands) {
            ++visited;
            if (roundBudgetHit()) break;
            if (!withinDenCap(q)) continue;
            asg[v] = q;
            const Score sc = totalScore(cs, weights, asg);
            if (sc < bestScore) {
                bestScore = sc;
                bestVar = v;
                bestVal = q;
                improved = true;
            }
        }
        asg[v] = saved;
    }

    if (improved) {
        asg[bestVar] = bestVal;
        currentScore = bestScore;
        return true;
    }
    return false;
}

std::optional<std::unordered_map<VarId, mpq_class>>
NraLocalSearch::tryFindModel(const std::vector<Constraint>& constraints,
                              const std::vector<VarId>& vars) {
    if (constraints.empty() || vars.empty()) return std::nullopt;

    // Initial assignment: all-zero (cheap canonical start).
    std::unordered_map<VarId, mpq_class> asg;
    for (VarId v : vars) asg.emplace(v, mpq_class{0});

    // PAWS weights — start uniform at 1; Layer A bumps them on each round
    // that ends in a local minimum (rough WalkSAT-style escape).
    std::vector<int> weights(constraints.size(), 1);

    auto t0 = std::chrono::steady_clock::now();
    auto budgetExpired = [&]() {
        if (budgetMs_ <= 0) return false;
        const auto now = std::chrono::steady_clock::now();
        const long elapsedMs =
            std::chrono::duration_cast<std::chrono::milliseconds>(now - t0).count();
        return elapsedMs >= budgetMs_;
    };

    Score score = totalScore(constraints, weights, asg);
    if (score.isSat()) return asg;

    // Sprint 5 pre-seed: detect bracket-pair candidates (tight upper+lower
    // bounds on the same var, e.g. meti-tarski's pi) and try each as a seed.
    // These are special: denom cap bypassed, fixed-count probe BEFORE the
    // walking loop. If any individual probe satisfies all atoms, return it.
    auto bracketMids = bracketMidpointCandidates(constraints, vars);
    for (const auto& [v, q] : bracketMids) {
        const mpq_class saved = asg.count(v) ? asg[v] : mpq_class{0};
        asg[v] = q;
        if (totalScore(constraints, weights, asg).isSat()) return asg;
        // Restore for the next probe so the assignment doesn't accumulate
        // stale per-pair changes; the walking loop picks up from the
        // unchanged baseline.
        asg[v] = saved;
    }
    // Apply each bracket midpoint as a STARTING assignment for that var
    // (multi-pair compositions are handled by the walking loop afterward).
    for (const auto& [v, q] : bracketMids) asg[v] = q;
    score = totalScore(constraints, weights, asg);
    if (score.isSat()) return asg;

    for (int round = 0; round < maxRounds_; ++round) {
        if (budgetExpired()) break;
        const bool improved = walkOneRound(constraints, weights, vars, asg, score);
        if (score.isSat()) return asg;
        if (!improved) {
            // Local minimum: PAWS-style bump on every still-violated atom +
            // restart from zero. (Master-spec lex score makes "violated" mean
            // "non-zero atomViolation", not "below some magnitude threshold".)
            bool anyViolated = false;
            for (size_t i = 0; i < constraints.size(); ++i) {
                if (atomViolation(constraints[i], asg) > 0) {
                    weights[i] = std::min(weights[i] + 1, 64);
                    anyViolated = true;
                }
            }
            if (!anyViolated) return asg;
            for (auto& kv : asg) kv.second = 0;
            score = totalScore(constraints, weights, asg);
        }
    }
    return std::nullopt;
}

}  // namespace xolver
