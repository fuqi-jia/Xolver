#include "theory/arith/logics/nia/search/SmartInit.h"

#include <algorithm>

namespace xolver {

SmartInit::SmartInit(PolynomialKernel& kernel) : kernel_(kernel) {}

bool SmartInit::isLinearForm(
    PolyId poly,
    std::vector<std::pair<std::string, mpz_class>>& terms,
    mpz_class& constTerm) const {

    terms.clear();
    constTerm = 0;
    auto termsOpt = kernel_.terms(poly);
    if (!termsOpt) return false;
    for (const auto& t : *termsOpt) {
        if (t.powers.empty()) { constTerm += t.coefficient; continue; }
        if (t.powers.size() != 1 || t.powers[0].second != 1) return false;
        std::string nm(kernel_.varName(t.powers[0].first));
        bool merged = false;
        for (auto& lt : terms) {
            if (lt.first == nm) { lt.second += t.coefficient; merged = true; break; }
        }
        if (!merged) terms.push_back({nm, t.coefficient});
    }
    return true;
}

void SmartInit::extractLinearInfo(
    const std::vector<NormalizedNiaConstraint>& constraints) {

    // Pass 1: collect vars by walking ALL constraint polynomials.
    std::unordered_set<std::string> allVars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) allVars.insert(v);
    }
    varsInOrder_.clear();
    varsInOrder_.reserve(allVars.size());
    for (const auto& v : allVars) varsInOrder_.push_back(v);
    std::sort(varsInOrder_.begin(), varsInOrder_.end());

    for (const auto& v : varsInOrder_) info_[v] = SmartInitVarInfo{};

    // Pass 2: per Eq atom, classify as single-var pin or 2+-var derive.
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        std::vector<std::pair<std::string, mpz_class>> linTerms;
        mpz_class constSum;
        if (!isLinearForm(c.poly, linTerms, constSum)) continue;
        if (linTerms.empty()) continue;
        // Single-var: pin v = -k/c (if integer).
        if (linTerms.size() == 1) {
            const auto& [singleVar, singleCoef] = linTerms[0];
            if (singleCoef == 0) continue;
            mpz_class neg = -constSum;
            if ((neg % singleCoef) != 0) continue;
            mpz_class root = neg / singleCoef;
            auto it = info_.find(singleVar);
            if (it == info_.end()) continue;
            if (!it->second.pinned) {
                it->second.pinned = true;
                it->second.pinnedValue = root;
            } else if (it->second.pinnedValue != root) {
                // Conflicting pins — formula is infeasible; let
                // the main pipeline detect it. SmartInit drops the pin.
                it->second.pinned = false;
            }
            continue;
        }
        // 2+-var: find an anchor with |c| = 1.
        int anchorIdx = -1;
        for (size_t i = 0; i < linTerms.size(); ++i) {
            if (linTerms[i].second == 1 || linTerms[i].second == -1) {
                anchorIdx = static_cast<int>(i);
                break;
            }
        }
        if (anchorIdx < 0) continue;
        const std::string& anchor = linTerms[anchorIdx].first;
        auto it = info_.find(anchor);
        if (it == info_.end()) continue;
        // Skip if anchor is already pinned or derived.
        if (it->second.pinned || it->second.derived) continue;
        SmartInitVarInfo& info = it->second;
        info.derived = true;
        info.anchorSign = (linTerms[anchorIdx].second == 1) ? 1 : -1;
        info.derivedConst = constSum;
        info.derivedDeps.clear();
        for (size_t i = 0; i < linTerms.size(); ++i) {
            if (static_cast<int>(i) == anchorIdx) continue;
            info.derivedDeps.push_back(linTerms[i]);
        }
    }
}

void SmartInit::tightenBounds(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains) {

    // Phase A: seed with DomainStore bounds.
    for (const auto& v : varsInOrder_) {
        const IntDomain* d = domains.getDomain(v);
        if (!d) continue;
        auto& info = info_[v];
        if (d->hasLower) { info.hasLower = true; info.lower = d->lower.value; }
        if (d->hasUpper) { info.hasUpper = true; info.upper = d->upper.value; }
    }

    // Phase B: refine via single-var bound atoms (c*v + k rel 0).
    for (const auto& c : constraints) {
        std::vector<std::pair<std::string, mpz_class>> linTerms;
        mpz_class constSum;
        if (!isLinearForm(c.poly, linTerms, constSum)) continue;
        if (linTerms.size() != 1) continue;
        const auto& [v, coef] = linTerms[0];
        if (coef != 1 && coef != -1) continue;
        // v + k <=/>= 0 with coef = ±1.
        // Eq is already handled in extractLinearInfo as pin.
        if (c.rel == Relation::Eq) continue;
        // threshold = -k / coef (exact, since coef = ±1).
        mpz_class threshold = -constSum / coef;
        auto& info = info_[v];
        // coef=1 means v + k rel 0 -> v rel -k.
        // coef=-1 means -v + k rel 0 -> v rel k.
        // Map relation accordingly:
        bool relIsLeq = (c.rel == Relation::Leq);
        bool relIsGeq = (c.rel == Relation::Geq);
        // After multiplying by coef, the relation flips if coef < 0.
        // But since we computed threshold = -k/coef, we want:
        //   coef=1 + Leq:  v <= -k = threshold => upper bound = threshold
        //   coef=1 + Geq:  v >= -k = threshold => lower bound
        //   coef=-1 + Leq: -v + k <= 0 => v >= k = threshold => lower
        //   coef=-1 + Geq: -v + k >= 0 => v <= k = threshold => upper
        bool isUpper = (coef == 1 && relIsLeq) || (coef == -1 && relIsGeq);
        if (isUpper) {
            if (!info.hasUpper || threshold < info.upper) {
                info.hasUpper = true; info.upper = threshold;
            }
        } else if (relIsGeq || relIsLeq) {
            if (!info.hasLower || threshold > info.lower) {
                info.hasLower = true; info.lower = threshold;
            }
        }
    }

    // Phase C: ensure pinned values respect their bounds (they
    // should by construction; if not, drop the pin and let the
    // main pipeline catch the infeasibility).
    for (auto& [v, info] : info_) {
        if (!info.pinned) continue;
        if (info.hasLower && info.pinnedValue < info.lower) info.pinned = false;
        if (info.hasUpper && info.pinnedValue > info.upper) info.pinned = false;
    }
}

void SmartInit::analyze(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains) {
    info_.clear();
    varsInOrder_.clear();
    extractLinearInfo(constraints);
    tightenBounds(constraints, domains);

    // LS-SMART-3 short: exact 2x2 linear-system solver via Cramer's rule.
    // For every pair of Eq atoms that BOTH reduce to a linear form
    // {a*x + b*y + e = 0, c*x + d*y + f = 0} on the same two variables,
    // compute the determinant ad - bc; if it's nonzero AND it divides
    // both numerator polynomials -ed + bf and ec - af exactly, pin both
    // x and y to the integer solution. This catches user's example
    // (x + y = 1, x + 2y = 4) → x=-2, y=3 even when single-Eq derive
    // would only chain one variable to the other.
    //
    // O(n^2) over Eq atoms; n is small (~10s of asserts even on
    // VeryMax-class).
    std::vector<std::tuple<size_t, std::vector<std::pair<std::string, mpz_class>>, mpz_class>> linEqs;
    for (size_t i = 0; i < constraints.size(); ++i) {
        if (constraints[i].rel != Relation::Eq) continue;
        std::vector<std::pair<std::string, mpz_class>> lt;
        mpz_class k;
        if (!isLinearForm(constraints[i].poly, lt, k)) continue;
        if (lt.size() == 2) linEqs.push_back({i, std::move(lt), k});
    }
    for (size_t i = 0; i < linEqs.size(); ++i) {
        const auto& [_i1, ti, ki] = linEqs[i];
        const auto& v1 = ti[0].first;
        const auto& v2 = ti[1].first;
        for (size_t j = i + 1; j < linEqs.size(); ++j) {
            const auto& [_i2, tj, kj] = linEqs[j];
            if (tj.size() != 2) continue;
            // Match var names — could be in either order.
            const std::string& uj1 = tj[0].first;
            const std::string& uj2 = tj[1].first;
            bool aligned = (uj1 == v1 && uj2 == v2);
            bool swapped = (uj1 == v2 && uj2 == v1);
            if (!aligned && !swapped) continue;
            const mpz_class& a = ti[0].second;
            const mpz_class& b = ti[1].second;
            const mpz_class& c = aligned ? tj[0].second : tj[1].second;
            const mpz_class& d = aligned ? tj[1].second : tj[0].second;
            const mpz_class& e = ki;
            const mpz_class& f = kj;
            mpz_class det = a * d - b * c;
            if (det == 0) continue;  // singular — drop
            // {a*x + b*y + e = 0, c*x + d*y + f = 0}
            // => x = (b*f - d*e) / det,  y = (c*e - a*f) / det
            mpz_class numX = b * f - d * e;
            mpz_class numY = c * e - a * f;
            if (numX % det != 0 || numY % det != 0) continue;
            mpz_class xVal = numX / det;
            mpz_class yVal = numY / det;
            auto pinIfFree = [&](const std::string& nm, const mpz_class& val) {
                auto it = info_.find(nm);
                if (it == info_.end()) return;
                if (it->second.hasLower && val < it->second.lower) return;
                if (it->second.hasUpper && val > it->second.upper) return;
                if (!it->second.pinned) {
                    it->second.pinned = true;
                    it->second.pinnedValue = val;
                    // Pinning supersedes any derive that may have been set
                    it->second.derived = false;
                } else if (it->second.pinnedValue != val) {
                    // Conflicting pin — drop both pin and derive; main
                    // pipeline will flag inconsistency.
                    it->second.pinned = false;
                }
            };
            pinIfFree(v1, xVal);
            pinIfFree(v2, yVal);
        }
    }

    // LS-SMART-4: per-var modular pre-check. For each Eq atom
    //   c_v * v + sum_{u != v} c_u * u + k = 0
    // (after fully linear decomposition), compute the GCD g of the
    // OTHER coefficients {c_u : u != v}. Then c_v * v + k must be
    // ≡ 0 (mod g) for any integer u-assignment, which gives the
    // modular condition  v * c_v ≡ -k (mod g). If gcd(c_v, g)
    // divides (-k), the residue set is well-defined and we record
    // it; otherwise the formula has no integer solution and
    // SmartInit silently skips (the modular reasoner upstream catches it).
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        std::vector<std::pair<std::string, mpz_class>> linTerms;
        mpz_class constSum;
        if (!isLinearForm(c.poly, linTerms, constSum)) continue;
        if (linTerms.size() < 2) continue;
        for (size_t i = 0; i < linTerms.size(); ++i) {
            const std::string& v = linTerms[i].first;
            const mpz_class& cv = linTerms[i].second;
            if (cv == 0) continue;
            auto it = info_.find(v);
            if (it == info_.end()) continue;
            if (it->second.pinned || it->second.derived) continue;
            // gcd of OTHER coefficients.
            mpz_class g = 0;
            for (size_t j = 0; j < linTerms.size(); ++j) {
                if (j == i) continue;
                mpz_class absC = (linTerms[j].second < 0) ? -linTerms[j].second
                                                          : linTerms[j].second;
                if (absC == 0) continue;
                if (g == 0) g = absC;
                else mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), absC.get_mpz_t());
            }
            if (g <= 1) continue;  // no useful modular constraint
            // We need c_v * v ≡ -k (mod g). Compute gcd(c_v, g).
            mpz_class absCv = (cv < 0) ? -cv : cv;
            mpz_class gcv;
            mpz_gcd(gcv.get_mpz_t(), absCv.get_mpz_t(), g.get_mpz_t());
            mpz_class negK = -constSum;
            if (negK % gcv != 0) {
                // Infeasible (modular contradiction). Silent — the
                // modular reasoner will report UNSAT.
                continue;
            }
            // Reduce: solve c_v' * v ≡ negK' (mod g') where g' = g/gcv,
            // c_v' = cv/gcv, negK' = negK/gcv. gcd(c_v', g') = 1, so
            // c_v' has a modular inverse mod g'.
            mpz_class gp = g / gcv;
            if (gp <= 1) continue;
            mpz_class cvp = absCv / gcv;
            mpz_class negKp = negK / gcv;
            // Modular inverse of cvp mod gp via extended GCD.
            mpz_class inv;
            if (mpz_invert(inv.get_mpz_t(), cvp.get_mpz_t(), gp.get_mpz_t()) == 0) {
                continue;  // not invertible (shouldn't happen, gcd=1)
            }
            mpz_class residue = (inv * negKp) % gp;
            if (residue < 0) residue += gp;
            // If c_v was negative, the equation was -|cv| * v ≡ negK,
            // so v ≡ -inv * negKp ≡ gp - residue (mod gp).
            if (cv < 0) residue = (gp - residue) % gp;
            // Intersect with any existing modular condition. For
            // simplicity, only record if no prior modulus is set;
            // a multi-atom CRT intersection is left to LS-SMART-3.
            if (it->second.modulus == 0) {
                it->second.modulus = gp;
                it->second.allowedResidues.clear();
                it->second.allowedResidues.push_back(residue);
            }
        }
    }

    // LS-SMART-5: per-var coefficient-derived sample range. For each
    // atom, compute |constSum / c_v| for each var v with linear
    // coefficient c_v (degree-1 monomial). Take the max over atoms.
    // For nonlinear atoms (degree >= 2 monomials), use the constSum
    // magnitude as a rough scale signal regardless of var.
    for (const auto& c : constraints) {
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        mpz_class constSum = 0;
        std::unordered_map<std::string, mpz_class> linCoefs;
        bool nonlinear = false;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) { constSum += t.coefficient; continue; }
            if (t.powers.size() == 1 && t.powers[0].second == 1) {
                std::string nm(kernel_.varName(t.powers[0].first));
                linCoefs[nm] += t.coefficient;
            } else {
                nonlinear = true;
            }
        }
        const mpz_class absRhs = (constSum < 0) ? -constSum : constSum;
        if (absRhs == 0) continue;
        for (auto& [v, coef] : linCoefs) {
            if (coef == 0) continue;
            auto it = info_.find(v);
            if (it == info_.end()) continue;
            mpz_class absCoef = (coef < 0) ? -coef : coef;
            // Plausible upper bound on |v|: |rhs / coef|, plus a small
            // safety factor (×2) to allow LS to overshoot slightly.
            mpz_class bound = (absRhs + absCoef - 1) / absCoef;  // ceil division
            bound *= 2;
            // Floor at 20 to ensure the existing narrow default is
            // never narrower than coef-derived.
            if (bound < 20) bound = 20;
            if (bound > it->second.coefRange) it->second.coefRange = bound;
        }
        // For nonlinear atoms, propagate absRhs as a SCALE signal to
        // every var mentioned in the atom (since LS may need to
        // explore values up to that magnitude).
        if (nonlinear) {
            for (const auto& v : kernel_.variables(c.poly)) {
                auto it = info_.find(v);
                if (it == info_.end()) continue;
                mpz_class bound = absRhs * 2;
                if (bound < 20) bound = 20;
                if (bound > it->second.coefRange) it->second.coefRange = bound;
            }
        }
    }
}

mpz_class SmartInit::evalDerived(const std::string& anchor,
                                   const IntegerModel& cur) const {
    auto it = info_.find(anchor);
    if (it == info_.end() || !it->second.derived) return mpz_class(0);
    const auto& info = it->second;
    mpz_class accum = info.derivedConst;
    for (const auto& [dv, dc] : info.derivedDeps) {
        auto cit = cur.find(dv);
        if (cit == cur.end()) return mpz_class(0);
        accum += dc * cit->second;
    }
    return -info.anchorSign * accum;
}

IntegerModel SmartInit::propose(std::mt19937_64& rng) const {
    IntegerModel model;
    // Phase 1: pinned values first (they're forced).
    for (const auto& v : varsInOrder_) {
        auto it = info_.find(v);
        if (it == info_.end()) continue;
        if (it->second.pinned) {
            model[v] = it->second.pinnedValue;
        }
    }
    // Phase 2: free vars (neither pinned nor derived) — sample within
    // the tightened box. If unbounded, use a narrow ±20 range (small
    // values are typical for VeryMax SAT models).
    for (const auto& v : varsInOrder_) {
        auto it = info_.find(v);
        if (it == info_.end()) continue;
        if (it->second.pinned) continue;
        if (it->second.derived) continue;
        const auto& info = it->second;
        if (info.hasLower && info.hasUpper) {
            mpz_class span = info.upper - info.lower;
            mpz_class pick;
            if (span <= 0) {
                pick = info.lower;
            } else {
                // Random in [lower, upper] inclusive.
                uint64_t r = rng();
                mpz_class spanInc = span + 1;
                mpz_class rmod = mpz_class(static_cast<unsigned long>(r)) % spanInc;
                pick = info.lower + rmod;
            }
            model[v] = pick;
        } else if (info.hasLower) {
            // Lower bound only: pick lower (small magnitudes typical).
            model[v] = info.lower;
        } else if (info.hasUpper) {
            model[v] = info.upper;
        } else {
            // LS-SMART-Z1 (z3-discovery 2026-06-02): VeryMax z3 SAT
            // models are DOMINATED by zeros (96% SAT14, 71% CInteger,
            // 65% ITS). Bias unbounded free vars to 0 with ~75%
            // probability; the remaining 25% sample from coefRange /
            // modular as before. Cluster-specific tuning can refine
            // this later (LS-SMART-Z2 prefix-aware).
            //
            // LS-SMART-Z2 (2026-06-02 deeper z3 analysis): of the
            // 25% non-zero, 87% of non-zero values in 55-case z3 model
            // sweep are in {-2, -1, 1, 2}: aggregate distribution is
            //   1:  62.7%,  -1: 12.6%,  2: 8.0%,  -2: 3.6%, other 13%
            // Bias the non-zero branch to match this empirical
            // distribution rather than uniform coefRange sampling.
            uint64_t zeroDie = rng() % 100;
            if (zeroDie < 75) {
                model[v] = mpz_class(0);
                continue;
            }
            // Z2 calibrated small-value bias (only when modular condition
            // is NOT set — modular case has its own residue handling).
            // Note: user 2026-06-02 noted that LARGE-magnitude cases
            // (max|v| up to ~10^10 in ITS juHashMap chain) ARE precisely
            // where LS is the right tool (BB would OOM). So Z2 also
            // includes a log-uniform "spread" branch that reaches
            // multi-order-of-magnitude values across restarts.
            if (info.modulus <= 1) {
                uint64_t smallDie = rng() % 1000;
                // Calibrated z3-model distribution per-mille (sums to 1000):
                //   1: 627    -1: 126    2: 80    -2: 36    3: 18
                //   medium [10..1000]: 33
                //   large [1000..1e5]: 33
                //   huge [1e5..1e9]:   30  (LS-territory per user 2026-06-02:
                //                          BB would OOM at 128 bits)
                //   coefRange fall-through: 17
                if (smallDie < 627)      { model[v] = mpz_class(1);  continue; }
                else if (smallDie < 753) { model[v] = mpz_class(-1); continue; }
                else if (smallDie < 833) { model[v] = mpz_class(2);  continue; }
                else if (smallDie < 869) { model[v] = mpz_class(-2); continue; }
                else if (smallDie < 887) { model[v] = mpz_class(3);  continue; }
                else if (smallDie < 920) {
                    long mag = 10 + static_cast<long>(rng() % 991);
                    bool neg = (rng() & 1) != 0;
                    model[v] = mpz_class(neg ? -mag : mag);
                    continue;
                }
                else if (smallDie < 953) {
                    long mag = 1000 + static_cast<long>(rng() % 99001);
                    bool neg = (rng() & 1) != 0;
                    model[v] = mpz_class(neg ? -mag : mag);
                    continue;
                }
                else if (smallDie < 983) {
                    // Huge log-uniform: pick exponent uniformly in [5, 9],
                    // then mantissa uniform in [1, 10), then random sign.
                    int exp = 5 + static_cast<int>(rng() % 5);
                    long mant = 1 + static_cast<long>(rng() % 9);
                    long mag = mant;
                    for (int i = 0; i < exp; ++i) mag *= 10;
                    bool neg = (rng() & 1) != 0;
                    model[v] = mpz_class(neg ? -mag : mag);
                    continue;
                }
                // 1.7% remainder falls through to coefRange random for variety.
            }
            // Fully unbounded: prefer the coefficient-derived range
            // (LS-SMART-5) when set, else fall back to narrow ±20.
            mpz_class range = info.coefRange;
            if (range <= 0) range = 20;
            const mpz_class RANGE_CAP("1000000");
            if (range > RANGE_CAP) range = RANGE_CAP;
            // LS-SMART-4: if a modular condition is set, sample
            // from the residue class. Pick a multiple of modulus
            // near 0, shift by allowed residue.
            if (info.modulus > 1 && !info.allowedResidues.empty()) {
                const mpz_class& res = info.allowedResidues[0];
                mpz_class numSteps = (2 * range) / info.modulus;
                if (numSteps < 1) numSteps = 1;
                uint64_t r = rng();
                mpz_class stepInc = numSteps + 1;
                mpz_class step = mpz_class(static_cast<unsigned long>(r)) % stepInc;
                model[v] = res + (step - numSteps / 2) * info.modulus;
            } else {
                uint64_t r = rng();
                mpz_class span = 2 * range + 1;
                mpz_class rmod = mpz_class(static_cast<unsigned long>(r)) % span;
                model[v] = rmod - range;
            }
        }
    }
    // Phase 3: cascade-evaluate derived vars using model[]'s
    // dependencies. Multiple-pass since derived can depend on
    // derived (rare under our anchor selection, but possible if
    // upstream filtering missed).
    for (int pass = 0; pass < 3; ++pass) {
        bool changed = false;
        for (const auto& v : varsInOrder_) {
            auto it = info_.find(v);
            if (it == info_.end()) continue;
            if (!it->second.derived) continue;
            mpz_class newVal = evalDerived(v, model);
            auto mit = model.find(v);
            if (mit == model.end() || mit->second != newVal) {
                model[v] = newVal;
                changed = true;
            }
        }
        if (!changed) break;
    }
    return model;
}

} // namespace xolver
