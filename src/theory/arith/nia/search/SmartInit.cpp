#include "theory/arith/nia/search/SmartInit.h"

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
                // How many full moduli fit in 2*range?
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
