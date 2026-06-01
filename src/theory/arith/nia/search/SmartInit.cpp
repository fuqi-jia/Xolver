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
            // Fully unbounded: narrow ±20 random (vs LS's ±2000). Per
            // H5 VeryMax SAT models, values are typically small.
            long r = static_cast<long>(rng() % 41) - 20;
            model[v] = mpz_class(r);
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
