#include "theory/arith/nra/simplex/PolynomialIntervalPruner.h"
#include <algorithm>
#include <unordered_set>
#include <unordered_map>

namespace xolver {

namespace {

// Compute interval of x^e given certified bounds.
// Returns a pair (lo, hi); either side nullopt if unbounded.
struct Range {
    std::optional<mpq_class> lo, hi;
};

Range powerInterval(const CertifiedBound* loB, const CertifiedBound* hiB,
                    int exp, std::vector<SatLit>& usedReasons) {
    Range r;
    if (exp == 0) {
        r.lo = mpq_class(1);
        r.hi = mpq_class(1);
        return r;
    }
    // Available bounds
    std::optional<mpq_class> lo, hi;
    if (loB) lo = loB->value;
    if (hiB) hi = hiB->value;
    // Push reasons (we'll attribute them if the interval contributes).
    auto pushReason = [&](const CertifiedBound* b) {
        if (!b) return;
        for (auto l : b->reasons) usedReasons.push_back(l);
    };

    if (exp % 2 == 0) {
        // Even power: result is always >= 0.
        // The interval [lo,hi] for x maps to:
        //   if 0 in [lo, hi]: [0, max(lo^e, hi^e)]
        //   if lo > 0:        [lo^e, hi^e]
        //   if hi < 0:        [hi^e, lo^e]
        auto pw = [&](const mpq_class& x) {
            mpq_class r = 1;
            for (int i = 0; i < exp; ++i) r *= x;
            return r;
        };
        if (lo && hi) {
            if (*lo >= 0) {
                r.lo = pw(*lo);
                r.hi = pw(*hi);
            } else if (*hi <= 0) {
                r.lo = pw(*hi);
                r.hi = pw(*lo);
            } else {
                r.lo = mpq_class(0);
                r.hi = std::max(pw(*lo), pw(*hi));
            }
            pushReason(loB); pushReason(hiB);
        } else if (lo) {
            if (*lo >= 0) {
                r.lo = pw(*lo);
                pushReason(loB);
            } else {
                r.lo = mpq_class(0);   // even powers can't go below 0
            }
            r.hi = std::nullopt;
        } else if (hi) {
            if (*hi <= 0) {
                r.lo = pw(*hi);
                pushReason(hiB);
            } else {
                r.lo = mpq_class(0);
            }
            r.hi = std::nullopt;
        } else {
            r.lo = mpq_class(0);
            r.hi = std::nullopt;
        }
        return r;
    } else {
        // Odd power: monotone increasing.
        auto pw = [&](const mpq_class& x) {
            mpq_class r = 1;
            for (int i = 0; i < exp; ++i) r *= x;
            return r;
        };
        if (lo) { r.lo = pw(*lo); pushReason(loB); }
        if (hi) { r.hi = pw(*hi); pushReason(hiB); }
        return r;
    }
}

Range multiplyRange(const Range& a, const Range& b) {
    Range out;
    // [aLo, aHi] * [bLo, bHi]: extrema at corners.
    // If any side is unbounded, the result may be unbounded.
    auto present = [](const std::optional<mpq_class>& x) { return x.has_value(); };
    if (!present(a.lo) || !present(a.hi) || !present(b.lo) || !present(b.hi)) {
        // Conservative: if any sign-bracket can be determined, give a half-bound; else fully unbounded.
        return out;
    }
    mpq_class p1 = *a.lo * *b.lo;
    mpq_class p2 = *a.lo * *b.hi;
    mpq_class p3 = *a.hi * *b.lo;
    mpq_class p4 = *a.hi * *b.hi;
    mpq_class lo = std::min({p1, p2, p3, p4});
    mpq_class hi = std::max({p1, p2, p3, p4});
    out.lo = lo;
    out.hi = hi;
    return out;
}

} // anon namespace

MonomialInterval intervalOfMonomial(
    const mpq_class& coefficient,
    const std::vector<std::pair<VarId, int>>& powers,
    const CertifiedSimplexFacts& facts,
    std::vector<SatLit>& usedReasons) {
    MonomialInterval out;
    if (coefficient == 0) {
        out.low = mpq_class(0);
        out.high = mpq_class(0);
        return out;
    }
    // Compute the product of variable power intervals.
    Range running;
    running.lo = mpq_class(1);
    running.hi = mpq_class(1);
    for (const auto& [v, e] : powers) {
        auto loOpt = facts.lower(v);
        auto hiOpt = facts.upper(v);
        const CertifiedBound* lo = loOpt ? &(*loOpt) : nullptr;
        const CertifiedBound* hi = hiOpt ? &(*hiOpt) : nullptr;
        Range pr = powerInterval(lo, hi, e, usedReasons);
        running = multiplyRange(running, pr);
        if (!running.lo.has_value() && !running.hi.has_value()) {
            out.valid = false;
            return out;
        }
    }
    // Multiply by coefficient (sign-flip handles negative coefficients).
    if (coefficient > 0) {
        if (running.lo) out.low  = *running.lo * coefficient;
        if (running.hi) out.high = *running.hi * coefficient;
    } else {
        if (running.hi) out.low  = *running.hi * coefficient;
        if (running.lo) out.high = *running.lo * coefficient;
    }
    return out;
}

std::optional<IntervalConflict> tryRefuteByPolynomialInterval(
    const std::vector<IntervalConstraint>& constraints,
    const CertifiedSimplexFacts& facts,
    PolynomialKernel& kernel) {

    for (const auto& c : constraints) {
        if (c.poly == NullPoly) continue;
        // Use the kernel decomposition (S1c-cached).
        auto termsOpt = kernel.terms(c.poly);
        if (!termsOpt) continue;
        const auto& terms = *termsOpt;
        std::optional<mpq_class> polyLow, polyHigh;
        polyLow  = mpq_class(0);
        polyHigh = mpq_class(0);
        std::vector<SatLit> reasons;
        bool indeterminate = false;
        for (const auto& term : terms) {
            std::vector<std::pair<VarId, int>> powers;
            powers.reserve(term.powers.size());
            for (const auto& [v, e] : term.powers) powers.push_back({v, e});
            MonomialInterval mi = intervalOfMonomial(mpq_class(term.coefficient),
                                                    powers, facts, reasons);
            if (!mi.valid) { indeterminate = true; break; }
            if (mi.low) {
                if (polyLow) *polyLow += *mi.low;
                else         polyLow = std::nullopt;
            } else {
                polyLow = std::nullopt;
            }
            if (mi.high) {
                if (polyHigh) *polyHigh += *mi.high;
                else          polyHigh = std::nullopt;
            } else {
                polyHigh = std::nullopt;
            }
        }
        if (indeterminate) continue;
        // Decide contradiction based on relation.
        bool refuted = false;
        switch (c.rel) {
            case Relation::Eq:
                if (polyLow && *polyLow > 0) refuted = true;
                if (polyHigh && *polyHigh < 0) refuted = true;
                break;
            case Relation::Geq:
                if (polyHigh && *polyHigh < 0) refuted = true;
                break;
            case Relation::Gt:
                if (polyHigh && *polyHigh <= 0) refuted = true;
                break;
            case Relation::Leq:
                if (polyLow && *polyLow > 0) refuted = true;
                break;
            case Relation::Lt:
                if (polyLow && *polyLow >= 0) refuted = true;
                break;
            default: break;
        }
        if (refuted) {
            IntervalConflict conf;
            conf.reasons.push_back(c.reason);
            // Dedup reasons set
            std::unordered_set<uint64_t> seen;
            auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
            seen.insert(key(c.reason));
            for (auto r : reasons) {
                if (seen.insert(key(r)).second) conf.reasons.push_back(r);
            }
            conf.explanation = "polynomial interval contradicts relation";
            return conf;
        }
    }
    return std::nullopt;
}

namespace {

using Term = PolynomialKernel::MonomialTerm;
using PowerKey = std::vector<std::pair<VarId, int>>;

// Canonical powers (sorted by VarId).
PowerKey canon(const PowerKey& p) {
    PowerKey r = p;
    std::sort(r.begin(), r.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });
    return r;
}

// Pretty hash of a PowerKey for set comparison.
std::string powerHash(const PowerKey& p) {
    std::string s;
    s.reserve(p.size() * 8);
    for (const auto& [v, e] : p) {
        s += std::to_string(v); s += '^'; s += std::to_string(e); s += ',';
    }
    return s;
}

// Subtract b from a, element-wise. Returns nullopt if any resulting exponent
// is negative (i.e. a is not a multiple of b).
std::optional<PowerKey> subtractPowers(const PowerKey& a, const PowerKey& b) {
    std::unordered_map<VarId, int> m;
    for (const auto& [v, e] : a) m[v] += e;
    for (const auto& [v, e] : b) m[v] -= e;
    PowerKey out;
    out.reserve(m.size());
    for (const auto& [v, e] : m) {
        if (e < 0) return std::nullopt;
        if (e > 0) out.push_back({v, e});
    }
    std::sort(out.begin(), out.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });
    return out;
}

// Add b to a, element-wise.
PowerKey addPowers(const PowerKey& a, const PowerKey& b) {
    std::unordered_map<VarId, int> m;
    for (const auto& [v, e] : a) m[v] += e;
    for (const auto& [v, e] : b) m[v] += e;
    PowerKey out;
    out.reserve(m.size());
    for (const auto& [v, e] : m) if (e > 0) out.push_back({v, e});
    std::sort(out.begin(), out.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });
    return out;
}

// Try to find a single-monomial multiplier q = (q_coeff, q_powers) such that
// for every term d_i of D, q * d_i appears in P with matching coefficient.
// If found, returns (q_coeff, q_powers, set of P indices used). If not, nullopt.
struct MultiplierMatch {
    mpq_class q_coeff;
    PowerKey  q_powers;
    std::vector<size_t> usedPIndices;
};

std::optional<MultiplierMatch> findSingleMonomialMultiplier(
        const std::vector<Term>& D_terms,
        const std::vector<Term>& P_terms) {

    if (D_terms.empty() || P_terms.empty()) return std::nullopt;

    // Try EACH non-zero D term as a possible anchor. This lets a derived
    // equality like `vv2 - vv3 = 0` substitute either direction into other
    // constraints (anchor on vv2 or on -vv3).
    for (size_t anchorIdx = 0; anchorIdx < D_terms.size(); ++anchorIdx) {
        const Term& anchorT = D_terms[anchorIdx];
        if (anchorT.coefficient == 0) continue;
        PowerKey d_anchor_pk = canon(anchorT.powers);
        mpq_class d_anchor_coeff(anchorT.coefficient);

    // Try each P term as potential `q * d_anchor`.
    for (size_t idx = 0; idx < P_terms.size(); ++idx) {
        const Term& pcand = P_terms[idx];
        if (pcand.coefficient == 0) continue;
        PowerKey p_pk = canon(pcand.powers);
        // q_powers = p_pk - d_anchor_pk
        auto qPK = subtractPowers(p_pk, d_anchor_pk);
        if (!qPK) continue;
        mpq_class qC = mpq_class(pcand.coefficient) / d_anchor_coeff;

        // Build P index by signature for fast lookup.
        std::unordered_map<std::string, std::vector<size_t>> bySig;
        for (size_t i = 0; i < P_terms.size(); ++i) {
            bySig[powerHash(canon(P_terms[i].powers))].push_back(i);
        }

        // For each d_i, look for q * d_i in P with matching coefficient.
        bool consistent = true;
        std::vector<size_t> used;
        std::unordered_set<size_t> usedSet;
        for (const auto& d_i : D_terms) {
            if (d_i.coefficient == 0) continue;
            PowerKey target_pk = addPowers(canon(d_i.powers), *qPK);
            mpq_class target_coeff = mpq_class(d_i.coefficient) * qC;
            auto it = bySig.find(powerHash(target_pk));
            if (it == bySig.end()) { consistent = false; break; }
            bool found = false;
            for (size_t pidx : it->second) {
                if (usedSet.count(pidx)) continue;
                if (mpq_class(P_terms[pidx].coefficient) == target_coeff) {
                    used.push_back(pidx);
                    usedSet.insert(pidx);
                    found = true;
                    break;
                }
            }
            if (!found) { consistent = false; break; }
        }
        if (consistent) {
            return MultiplierMatch{qC, *qPK, std::move(used)};
        }
    }
    }   // close anchorIdx loop
    return std::nullopt;
}

// Compute the residual: P - q * D, returned as a term list.
std::vector<Term> computeResidual(
        const std::vector<Term>& P_terms,
        const MultiplierMatch& mm) {
    std::vector<Term> residual;
    residual.reserve(P_terms.size());
    std::unordered_set<size_t> used(mm.usedPIndices.begin(), mm.usedPIndices.end());
    for (size_t i = 0; i < P_terms.size(); ++i) {
        if (used.count(i)) continue;
        residual.push_back(P_terms[i]);
    }
    return residual;
}

// Detect if a polynomial p can be solved for a MONOMIAL pattern.
// The general pattern: p contains a monomial `coeff * (target_pattern)` that
// appears in EXACTLY ONE term, and the variables in target_pattern don't
// appear in any other monomial of p (so target_pattern can be isolated).
//
// Single-variable case (target_pattern = v): same as before.
// Compound case (target_pattern = v1^a1 * v2^a2 * ...): allows substituting
// monomials like `lambda1*vv1` as a whole, which closes the mgc_02-class
// cascade where lambda1 only appears multiplied by vv1.
struct SolveForResult {
    VarId v = NullVar;                        // primary variable (for backward compat)
    PowerKey monomialPattern;                 // the FULL monomial pattern being solved for
    mpq_class coeffOfV;                       // coefficient of the isolated monomial
    std::vector<Term> remainder;              // terms of p excluding the isolated monomial
};

std::optional<SolveForResult> trySolveForLinearVariable(
        const std::vector<Term>& terms) {
    // Try each monomial as the "isolated pattern" candidate.
    for (size_t i = 0; i < terms.size(); ++i) {
        const Term& t = terms[i];
        if (t.coefficient == 0) continue;
        if (t.powers.empty()) continue;       // constant term can't be a pattern
        PowerKey patternPK = canon(t.powers);
        // The pattern's variable set.
        std::unordered_set<VarId> patternVars;
        for (const auto& [v, e] : patternPK) patternVars.insert(v);
        // For pattern to be isolatable, NO variable in pattern can appear in
        // any other monomial of p. This makes the pattern unique in p.
        bool isolatable = true;
        for (size_t j = 0; j < terms.size(); ++j) {
            if (j == i) continue;
            for (const auto& [vv, e] : terms[j].powers) {
                if (patternVars.count(vv)) { isolatable = false; break; }
            }
            if (!isolatable) break;
        }
        if (!isolatable) continue;
        SolveForResult r;
        r.v = patternPK[0].first;   // first var as primary (backward compat)
        r.monomialPattern = patternPK;
        r.coeffOfV = mpq_class(t.coefficient);
        for (size_t j = 0; j < terms.size(); ++j) {
            if (j == i) continue;
            r.remainder.push_back(terms[j]);
        }
        return r;
    }
    return std::nullopt;
}

// Multiply two term-lists (polynomial product) and return the product.
std::vector<Term> multiplyTerms(const std::vector<Term>& a,
                                 const std::vector<Term>& b) {
    std::unordered_map<std::string, std::pair<mpq_class, PowerKey>> acc;
    for (const auto& ta : a) {
        for (const auto& tb : b) {
            PowerKey pk = addPowers(canon(ta.powers), canon(tb.powers));
            mpq_class c = mpq_class(ta.coefficient) * mpq_class(tb.coefficient);
            std::string key = powerHash(pk);
            auto it = acc.find(key);
            if (it == acc.end()) acc[key] = {c, pk};
            else                 it->second.first += c;
        }
    }
    std::vector<Term> out;
    out.reserve(acc.size());
    for (auto& [k, vp] : acc) {
        if (vp.first == 0) continue;
        Term t;
        t.coefficient = mpz_class(vp.first.get_num() / vp.first.get_den());
        // Only handle integer coefficients (kernel constraint). If non-integer,
        // skip this substitution (sound: dropping derived constraint preserves
        // soundness, just loses completeness on this case).
        if (vp.first.get_den() != 1) return {};
        t.powers = vp.second;
        out.push_back(std::move(t));
    }
    return out;
}

// Scale a term list by a constant rational.
std::vector<Term> scaleTerms(const std::vector<Term>& a, const mpq_class& s) {
    std::vector<Term> out;
    out.reserve(a.size());
    for (const auto& t : a) {
        mpq_class c = mpq_class(t.coefficient) * s;
        if (c == 0) continue;
        if (c.get_den() != 1) return {};   // non-integer; bail
        Term nt;
        nt.coefficient = mpz_class(c.get_num() / c.get_den());
        nt.powers = t.powers;
        out.push_back(std::move(nt));
    }
    return out;
}

// Sum two term-lists.
std::vector<Term> addTerms(const std::vector<Term>& a, const std::vector<Term>& b) {
    std::unordered_map<std::string, std::pair<mpq_class, PowerKey>> acc;
    auto pushAll = [&](const std::vector<Term>& lst) {
        for (const auto& t : lst) {
            PowerKey pk = canon(t.powers);
            std::string key = powerHash(pk);
            auto it = acc.find(key);
            if (it == acc.end()) acc[key] = {mpq_class(t.coefficient), pk};
            else                 it->second.first += mpq_class(t.coefficient);
        }
    };
    pushAll(a);
    pushAll(b);
    std::vector<Term> out;
    out.reserve(acc.size());
    for (auto& [k, vp] : acc) {
        if (vp.first == 0) continue;
        Term t;
        if (vp.first.get_den() != 1) return {};
        t.coefficient = mpz_class(vp.first.get_num() / vp.first.get_den());
        t.powers = vp.second;
        out.push_back(std::move(t));
    }
    return out;
}

// Compute v^k as a term-list (single monomial).
std::vector<Term> varPower(VarId v, int k) {
    if (k == 0) {
        Term t;
        t.coefficient = mpz_class(1);
        return {t};
    }
    Term t;
    t.coefficient = mpz_class(1);
    t.powers.push_back({v, k});
    return {t};
}

// Substitute v -> replacement_poly in target_terms (single-variable version).
std::vector<Term> substitutePolyInTerms(
        const std::vector<Term>& target,
        VarId v,
        const std::vector<Term>& replacement) {
    std::vector<Term> result;
    for (const auto& t : target) {
        int kOfV = 0;
        std::vector<std::pair<VarId, int>> otherPowers;
        for (const auto& [vv, e] : t.powers) {
            if (vv == v) kOfV = e;
            else         otherPowers.push_back({vv, e});
        }
        if (kOfV == 0) {
            result.push_back(t);
            continue;
        }
        std::vector<Term> repK;
        repK.push_back({mpz_class(1), {}});
        for (int i = 0; i < kOfV; ++i) {
            repK = multiplyTerms(repK, replacement);
            if (repK.empty() && i+1 < kOfV) return {};
        }
        Term otherMono;
        otherMono.coefficient = t.coefficient;
        otherMono.powers = otherPowers;
        auto scaled = multiplyTerms(repK, {otherMono});
        result = addTerms(result, scaled);
    }
    return result;
}

// Substitute a compound monomial pattern -> replacement_poly in target_terms.
// pattern_powers represents the "left-hand side" monomial (e.g. lambda1*vv1).
// For each target monomial t whose powers include pattern_powers as a factor
// (each pattern_var^pattern_exp <= target_var^target_exp), the substitution
// computes:
//   t.coefficient * replacement^pattern_match_count * other_factors
// where pattern_match_count is the maximum number of times pattern fits in t.
//
// For most cases (mgc_02 pattern), pattern appears exactly once in target.
// We handle pattern_match_count = floor(min target_exp / pattern_exp)
// over the pattern variables, but for simplicity restrict to count = 1.
std::vector<Term> substituteMonomialPatternInTerms(
        const std::vector<Term>& target,
        const PowerKey& patternPK,
        const std::vector<Term>& replacement) {
    if (patternPK.empty()) return target;
    std::vector<Term> result;
    for (const auto& t : target) {
        // Check if t contains pattern as a factor: every (v, e) in patternPK
        // must have e' >= e in t.powers.
        std::unordered_map<VarId, int> tMap;
        for (const auto& [v, e] : t.powers) tMap[v] = e;
        bool contains = true;
        for (const auto& [v, e] : patternPK) {
            auto it = tMap.find(v);
            if (it == tMap.end() || it->second < e) { contains = false; break; }
        }
        if (!contains) {
            result.push_back(t);
            continue;
        }
        // Build "other factors" = t.powers minus patternPK.
        std::vector<std::pair<VarId, int>> otherPowers;
        for (const auto& [v, e] : t.powers) {
            int patExp = 0;
            for (const auto& [pv, pe] : patternPK) if (pv == v) { patExp = pe; break; }
            int residualE = e - patExp;
            if (residualE > 0) otherPowers.push_back({v, residualE});
        }
        Term otherMono;
        otherMono.coefficient = t.coefficient;
        otherMono.powers = otherPowers;
        // Multiply replacement * other_mono.
        auto scaled = multiplyTerms(replacement, {otherMono});
        result = addTerms(result, scaled);
    }
    return result;
}

// Try to factor out a sign-definite variable v from EQ constraint c.
// If every monomial of c.poly contains v with positive exponent, the
// reduced polynomial (each exponent decremented by 1) is sound to add
// as a new EQ constraint (since v != 0 + v*q = 0 => q = 0).
struct FactorResult {
    bool factored = false;
    std::vector<PolynomialKernel::MonomialTerm> reducedTerms;
    VarId factorVar = NullVar;
    std::vector<SatLit> reasons;
};

FactorResult tryFactorOnce(const IntervalConstraint& c,
                            const CertifiedSimplexFacts& facts,
                            PolynomialKernel& kernel) {
    FactorResult fr;
    if (c.rel != Relation::Eq) return fr;
    auto termsOpt = kernel.terms(c.poly);
    if (!termsOpt || termsOpt->empty()) return fr;
    const auto& terms = *termsOpt;
    // Pick a candidate variable: must appear in EVERY monomial with
    // exponent >= 1, AND have sign-definite non-zero.
    std::unordered_map<VarId, int> minExp;
    bool first = true;
    for (const auto& t : terms) {
        std::unordered_map<VarId, int> here;
        for (const auto& [v, e] : t.powers) here[v] = e;
        if (first) {
            minExp = here;
            first = false;
        } else {
            for (auto it = minExp.begin(); it != minExp.end();) {
                auto h = here.find(it->first);
                if (h == here.end()) { it = minExp.erase(it); continue; }
                if (h->second < it->second) it->second = h->second;
                ++it;
            }
        }
        if (minExp.empty()) return fr;
    }
    // Pick the first sign-definite candidate.
    VarId pick = NullVar;
    for (const auto& [v, e] : minExp) {
        if (e < 1) continue;
        int s = facts.certifiedSign(v);
        if (s == +1 || s == -1) {  // strict, non-zero
            pick = v;
            break;
        }
    }
    if (pick == NullVar) return fr;
    // Build reduced monomials.
    std::vector<PolynomialKernel::MonomialTerm> reduced;
    reduced.reserve(terms.size());
    for (const auto& t : terms) {
        PolynomialKernel::MonomialTerm nt;
        nt.coefficient = t.coefficient;
        for (const auto& [v, e] : t.powers) {
            int ne = (v == pick) ? (e - 1) : e;
            if (ne > 0) nt.powers.push_back({v, ne});
        }
        reduced.push_back(std::move(nt));
    }
    fr.factored = true;
    fr.reducedTerms = std::move(reduced);
    fr.factorVar = pick;
    // The reason for the factoring step: original constraint reason + the
    // bound reasons that proved pick has sign != 0.
    fr.reasons.push_back(c.reason);
    if (auto lo = facts.lower(pick)) for (auto r : lo->reasons) fr.reasons.push_back(r);
    if (auto hi = facts.upper(pick)) for (auto r : hi->reasons) fr.reasons.push_back(r);
    return fr;
}

// Compute the interval of a polynomial given as a term list (not a PolyId).
// Returns nullopt if any monomial is indeterminate.
struct PolyInterval { std::optional<mpq_class> low, high; bool indeterminate=false; };
PolyInterval intervalOfTerms(
    const std::vector<PolynomialKernel::MonomialTerm>& terms,
    const CertifiedSimplexFacts& facts,
    std::vector<SatLit>& usedReasons) {
    PolyInterval out;
    out.low = mpq_class(0);
    out.high = mpq_class(0);
    for (const auto& term : terms) {
        std::vector<std::pair<VarId, int>> powers;
        powers.reserve(term.powers.size());
        for (const auto& [v, e] : term.powers) powers.push_back({v, e});
        MonomialInterval mi = intervalOfMonomial(mpq_class(term.coefficient),
                                                  powers, facts, usedReasons);
        if (!mi.valid) { out.indeterminate = true; return out; }
        if (mi.low) {
            if (out.low) *out.low += *mi.low;
        } else {
            out.low = std::nullopt;
        }
        if (mi.high) {
            if (out.high) *out.high += *mi.high;
        } else {
            out.high = std::nullopt;
        }
    }
    return out;
}

bool intervalRefutesEq(const PolyInterval& iv) {
    if (iv.low && *iv.low > 0) return true;
    if (iv.high && *iv.high < 0) return true;
    return false;
}

// Key for dedup of derived term-lists (so we don't loop forever).
std::string termsKey(const std::vector<PolynomialKernel::MonomialTerm>& terms) {
    std::string s;
    s.reserve(terms.size() * 16);
    for (const auto& t : terms) {
        s += t.coefficient.get_str();
        s += '|';
        for (const auto& [v, e] : t.powers) {
            s += std::to_string(v);
            s += '^';
            s += std::to_string(e);
            s += '*';
        }
        s += ';';
    }
    return s;
}

} // anon

std::optional<IntervalConflict> tryRefuteByIterativeFactoring(
    const std::vector<IntervalConstraint>& constraints,
    CertifiedSimplexFacts& facts,
    PolynomialKernel& kernel,
    int maxIterations) {

    // Increase iteration cap for deeper substitution cascades like mgc_02.
    if (maxIterations < 12) maxIterations = 12;

    // Round 0: try plain interval refutation.
    if (auto c = tryRefuteByPolynomialInterval(constraints, facts, kernel))
        return c;

    // Working set: original constraints + derived (factored).
    struct DerivedConstraint {
        std::vector<PolynomialKernel::MonomialTerm> terms;
        Relation rel;
        std::vector<SatLit> reasons;
    };
    std::vector<DerivedConstraint> derived;
    std::unordered_set<std::string> seen;

    // Cap on derived constraint count. Raise to 1000 so the multi-step
    // mgc_02 cascade (gamma0 subst -> lambda1*vv1 subst -> vv2=vv3 subst
    // into final eq5) has enough budget to complete.
    constexpr size_t kMaxDerivedCap = 1000;
    auto addDerived = [&](DerivedConstraint d) -> bool {
        if (derived.size() >= kMaxDerivedCap) return false;
        std::string k = termsKey(d.terms);
        if (seen.count(k)) return false;
        seen.insert(k);
        derived.push_back(std::move(d));
        return true;
    };

    // Eager refutation check on a single term-list -- emit conflict immediately
    // so we don't spend cycles deriving more constraints.
    auto eagerCheck = [&](const std::vector<Term>& terms,
                          const std::vector<SatLit>& baseReasons)
                            -> std::optional<IntervalConflict> {
        std::vector<SatLit> used;
        PolyInterval iv = intervalOfTerms(terms, facts, used);
        if (iv.indeterminate) return std::nullopt;
        if (!intervalRefutesEq(iv)) return std::nullopt;
        IntervalConflict conf;
        std::unordered_set<uint64_t> seenLit;
        auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
        for (auto r : baseReasons) if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
        for (auto r : used)        if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
        conf.explanation = "polynomial substitution closes constraint";
        return conf;
    };

    // Seed with original constraints (factored if possible).
    for (const auto& c : constraints) {
        auto fr = tryFactorOnce(c, facts, kernel);
        if (fr.factored && !fr.reducedTerms.empty()) {
            DerivedConstraint dc;
            dc.terms = fr.reducedTerms;
            dc.rel = Relation::Eq;
            dc.reasons = fr.reasons;
            addDerived(std::move(dc));
        }
    }

    // Cache original constraint term-lists once.
    std::vector<std::vector<Term>> origTerms;
    origTerms.reserve(constraints.size());
    for (const auto& c : constraints) {
        if (c.poly == NullPoly) { origTerms.emplace_back(); continue; }
        auto t = kernel.terms(c.poly);
        if (t) origTerms.push_back(*t);
        else   origTerms.emplace_back();
    }

    auto checkRefutation = [&](const std::vector<Term>& terms,
                               const std::vector<SatLit>& baseReasons,
                               Relation rel)
                                  -> std::optional<IntervalConflict> {
        std::vector<SatLit> used;
        PolyInterval iv = intervalOfTerms(terms, facts, used);
        if (iv.indeterminate) return std::nullopt;
        bool refuted = false;
        switch (rel) {
            case Relation::Eq:
                if (iv.low && *iv.low > 0) refuted = true;
                if (iv.high && *iv.high < 0) refuted = true;
                break;
            case Relation::Geq:
                if (iv.high && *iv.high < 0) refuted = true;
                break;
            case Relation::Gt:
                if (iv.high && *iv.high <= 0) refuted = true;
                break;
            case Relation::Leq:
                if (iv.low && *iv.low > 0) refuted = true;
                break;
            case Relation::Lt:
                if (iv.low && *iv.low >= 0) refuted = true;
                break;
            default: break;
        }
        if (!refuted) return std::nullopt;
        IntervalConflict conf;
        std::unordered_set<uint64_t> seenLit;
        auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
        for (auto r : baseReasons) if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
        for (auto r : used)        if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
        conf.explanation = "iterative cross-equation reduction";
        return conf;
    };

    bool diag = std::getenv("XOLVER_NRA_OSF_DIAG") != nullptr;

    // Focused approach: pick the LARGEST EQ constraint and apply all
    // solvable substitutions to IT directly, then check.
    auto applyAllSubsToTarget = [&](
            const std::vector<Term>& targetTerms,
            const std::vector<SatLit>& targetReasons,
            Relation targetRel,
            int maxApplications) -> std::optional<IntervalConflict> {
        std::vector<Term> current = targetTerms;
        std::vector<SatLit> reasons = targetReasons;
        std::unordered_set<uint64_t> reasonsSet;
        auto rkey = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
        for (auto r : reasons) reasonsSet.insert(rkey(r));
        for (int round = 0; round < maxApplications; ++round) {
            bool anyApplied = false;
            // Try every derived constraint as a substitution source.
            for (size_t di = 0; di < derived.size(); ++di) {
                auto sf = trySolveForLinearVariable(derived[di].terms);
                if (!sf) continue;
                mpq_class invScale = mpq_class(-1) / sf->coeffOfV;
                auto replacement = scaleTerms(sf->remainder, invScale);
                if (replacement.empty() && !sf->remainder.empty()) continue;
                // Check if pattern appears in current.
                std::vector<Term> after;
                if (sf->monomialPattern.size() == 1 && sf->monomialPattern[0].second == 1) {
                    VarId v = sf->v;
                    bool hasVar = false;
                    for (const auto& t : current) {
                        for (const auto& [vv, e] : t.powers) {
                            if (vv == v) { hasVar = true; break; }
                        }
                        if (hasVar) break;
                    }
                    if (!hasVar) continue;
                    after = substitutePolyInTerms(current, v, replacement);
                } else {
                    bool hasPattern = false;
                    for (const auto& t : current) {
                        std::unordered_map<VarId, int> tMap;
                        for (const auto& [v, e] : t.powers) tMap[v] = e;
                        bool ok = true;
                        for (const auto& [v, e] : sf->monomialPattern) {
                            auto it = tMap.find(v);
                            if (it == tMap.end() || it->second < e) { ok = false; break; }
                        }
                        if (ok) { hasPattern = true; break; }
                    }
                    if (!hasPattern) continue;
                    after = substituteMonomialPatternInTerms(current, sf->monomialPattern, replacement);
                }
                if (after.empty()) continue;
                // Soundness-preserving completeness cap: skip substitutions
                // that would explode the polynomial beyond a useful refutation
                // size. Dropping a substitution is sound (we just lose
                // completeness on this path; the constraint is unchanged).
                // 200 terms is enough for the cvc5 NLext-style refutations we
                // can actually evaluate via interval arithmetic; beyond that
                // the interval becomes (-inf,+inf) anyway and we're burning
                // cycles for nothing. mgc_02 cascade hit 22301 terms = pure
                // waste.
                constexpr size_t kMaxFocusedTerms = 200;
                if (after.size() > kMaxFocusedTerms) {
                    if (diag) {
                        std::fprintf(stderr, "[OSF-FOCUS] skip D[%zu]: subst -> %zu terms (cap %zu)\n",
                                     di, after.size(), kMaxFocusedTerms);
                    }
                    continue;
                }
                current = std::move(after);
                for (auto r : derived[di].reasons) {
                    if (reasonsSet.insert(rkey(r)).second) reasons.push_back(r);
                }
                anyApplied = true;
                if (diag) {
                    std::fprintf(stderr, "[OSF-FOCUS] applied subst from D[%zu]; current now %zu terms\n",
                                 di, current.size());
                }
                // Check refutation.
                std::vector<SatLit> chkReasons = reasons;
                std::vector<SatLit> usedR;
                PolyInterval iv = intervalOfTerms(current, facts, usedR);
                if (!iv.indeterminate) {
                    bool refuted = false;
                    switch (targetRel) {
                        case Relation::Eq:
                            if (iv.low && *iv.low > 0) refuted = true;
                            if (iv.high && *iv.high < 0) refuted = true;
                            break;
                        case Relation::Geq:
                            if (iv.high && *iv.high < 0) refuted = true;
                            break;
                        case Relation::Gt:
                            if (iv.high && *iv.high <= 0) refuted = true;
                            break;
                        case Relation::Leq:
                            if (iv.low && *iv.low > 0) refuted = true;
                            break;
                        case Relation::Lt:
                            if (iv.low && *iv.low >= 0) refuted = true;
                            break;
                        default: break;
                    }
                    if (refuted) {
                        IntervalConflict conf;
                        for (auto r : reasons) conf.reasons.push_back(r);
                        for (auto r : usedR) {
                            if (reasonsSet.insert(rkey(r)).second) conf.reasons.push_back(r);
                        }
                        conf.explanation = "focused chained substitution closes target";
                        if (diag) {
                            std::fprintf(stderr, "[OSF-FOCUS] CONFLICT after %d substitutions; final %zu terms\n",
                                         round + 1, current.size());
                        }
                        return conf;
                    }
                }
            }
            if (!anyApplied) break;
        }
        return std::nullopt;
    };
    if (diag) {
        std::fprintf(stderr, "[OSF-DIAG] iter loop start: derived=%zu constraints=%zu\n",
                     derived.size(), constraints.size());
    }

    for (int iter = 0; iter < maxIterations; ++iter) {
        bool changed = false;

        if (diag) {
            std::fprintf(stderr, "[OSF-DIAG] iter %d: derived=%zu\n", iter, derived.size());
        }

        // First check each derived constraint's interval for contradiction.
        for (const auto& d : derived) {
            auto cf = checkRefutation(d.terms, d.reasons, d.rel);
            if (cf) return cf;
        }

        // S-pair reduction. Iterate by index + snapshot size to avoid
        // reference invalidation when addDerived grows the vector.
        size_t snapshotSize = derived.size();
        for (size_t didx = 0; didx < snapshotSize; ++didx) {
            // Take a copy of relevant fields BEFORE addDerived may invalidate
            // references. This is critical for correctness.
            std::vector<Term> d_terms_snapshot = derived[didx].terms;
            std::vector<SatLit> d_reasons_snapshot = derived[didx].reasons;
            for (size_t ci = 0; ci < constraints.size(); ++ci) {
                const auto& cc = constraints[ci];
                if (cc.rel != Relation::Eq) continue;
                const auto& pterms = origTerms[ci];
                if (pterms.empty()) continue;
                if (pterms.size() < d_terms_snapshot.size()) continue;
                auto mm = findSingleMonomialMultiplier(d_terms_snapshot, pterms);
                if (!mm) continue;
                auto residual = computeResidual(pterms, *mm);
                if (residual.empty()) continue;
                if (residual.size() >= pterms.size()) continue;
                DerivedConstraint nd;
                size_t residualSize = residual.size();
                nd.terms = std::move(residual);
                nd.rel = Relation::Eq;
                std::unordered_set<uint64_t> seenLit;
                auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
                for (auto r : d_reasons_snapshot) if (seenLit.insert(key(r)).second) nd.reasons.push_back(r);
                if (seenLit.insert(key(cc.reason)).second) nd.reasons.push_back(cc.reason);
                if (addDerived(std::move(nd))) {
                    changed = true;
                    if (diag) {
                        std::fprintf(stderr, "[OSF-DIAG] S-pair: P[%zu] %zu terms - q*D %zu = residual %zu\n",
                                     ci, pterms.size(), d_terms_snapshot.size(), residualSize);
                    }
                }
            }
        }

        // Also try cross-derived-to-derived S-pair reduction in subsequent rounds.
        size_t derivedCount = derived.size();
        for (size_t di = 0; di < derivedCount; ++di) {
            for (size_t dj = di + 1; dj < derivedCount; ++dj) {
                if (derived[di].rel != Relation::Eq) continue;
                if (derived[dj].rel != Relation::Eq) continue;
                if (derived[di].terms.size() > derived[dj].terms.size()) {
                    auto mm = findSingleMonomialMultiplier(derived[dj].terms, derived[di].terms);
                    if (!mm) continue;
                    auto residual = computeResidual(derived[di].terms, *mm);
                    if (residual.empty() || residual.size() >= derived[di].terms.size()) continue;
                    DerivedConstraint nd;
                    nd.terms = std::move(residual);
                    nd.rel = Relation::Eq;
                    std::unordered_set<uint64_t> seenLit;
                    auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
                    for (auto r : derived[di].reasons) if (seenLit.insert(key(r)).second) nd.reasons.push_back(r);
                    for (auto r : derived[dj].reasons) if (seenLit.insert(key(r)).second) nd.reasons.push_back(r);
                    if (addDerived(std::move(nd))) changed = true;
                }
            }
        }

        // After deriving new constraints, also try factoring them with the
        // current facts (some derived constraints may become factorable).
        for (size_t di = 0; di < derived.size(); ++di) {
            // Skip if terms are too small to factor.
            if (derived[di].terms.size() < 2) continue;
            // Find a common variable across all monomials with definite sign.
            std::unordered_map<VarId, int> minExp;
            bool first = true;
            for (const auto& t : derived[di].terms) {
                std::unordered_map<VarId, int> here;
                for (const auto& [v, e] : t.powers) here[v] = e;
                if (first) { minExp = here; first = false; }
                else {
                    for (auto it = minExp.begin(); it != minExp.end();) {
                        auto h = here.find(it->first);
                        if (h == here.end()) { it = minExp.erase(it); continue; }
                        if (h->second < it->second) it->second = h->second;
                        ++it;
                    }
                }
                if (minExp.empty()) break;
            }
            VarId pick = NullVar;
            for (const auto& [v, e] : minExp) {
                if (e < 1) continue;
                int s = facts.certifiedSign(v);
                if (s == +1 || s == -1) { pick = v; break; }
            }
            if (pick == NullVar) continue;
            std::vector<Term> reduced;
            for (const auto& t : derived[di].terms) {
                Term nt;
                nt.coefficient = t.coefficient;
                for (const auto& [v, e] : t.powers) {
                    int ne = (v == pick) ? (e - 1) : e;
                    if (ne > 0) nt.powers.push_back({v, ne});
                }
                reduced.push_back(std::move(nt));
            }
            DerivedConstraint nd;
            nd.terms = std::move(reduced);
            nd.rel = Relation::Eq;
            nd.reasons = derived[di].reasons;
            if (auto lo = facts.lower(pick)) for (auto r : lo->reasons) nd.reasons.push_back(r);
            if (auto hi = facts.upper(pick)) for (auto r : hi->reasons) nd.reasons.push_back(r);
            if (addDerived(std::move(nd))) changed = true;
        }

        // Polynomial substitution: for each derived constraint that can be
        // solved for a variable v (i.e. v appears in only one monomial with
        // coeff ±1 and exp 1), substitute v -> (the rest) into all original
        // and derived constraints. This is the key step that closes mgc_02
        // after the cascade gamma0 -> vv1*(vv3^2 + 1) -> ...
        size_t derivedAtStartOfSubst = derived.size();
        for (size_t di = 0; di < derivedAtStartOfSubst; ++di) {
            const auto solveOpt = trySolveForLinearVariable(derived[di].terms);
            if (!solveOpt) continue;
            const VarId solveVar = solveOpt->v;
            const PowerKey solvePattern = solveOpt->monomialPattern;
            // Replacement poly: -remainder / coeffOfV (mpq for the scale).
            mpq_class invScale = mpq_class(-1) / solveOpt->coeffOfV;
            std::vector<Term> replacement = scaleTerms(solveOpt->remainder, invScale);
            if (replacement.empty() && !solveOpt->remainder.empty()) continue;  // bail on fractional

            // Eager-conflict-on-substitution return token.
            std::optional<IntervalConflict> eagerConflict;
            auto tryAddSubst = [&](const std::vector<Term>& pt,
                                   const std::vector<SatLit>& baseReasons,
                                   const char* label, size_t labelIdx) -> bool {
                if (eagerConflict) return false;
                if (pt.empty()) return false;
                // Use compound monomial substitution if pattern has >1 var
                // (e.g. lambda1*vv1); else fall back to single-var.
                std::vector<Term> subst;
                if (solvePattern.size() == 1 && solvePattern[0].second == 1) {
                    bool hasVar = false;
                    for (const auto& t : pt) {
                        for (const auto& [v, e] : t.powers) {
                            if (v == solveVar) { hasVar = true; break; }
                        }
                        if (hasVar) break;
                    }
                    if (!hasVar) return false;
                    subst = substitutePolyInTerms(pt, solveVar, replacement);
                } else {
                    // Compound: substitute lambda1*vv1 pattern.
                    bool hasPattern = false;
                    for (const auto& t : pt) {
                        std::unordered_map<VarId, int> tMap;
                        for (const auto& [v, e] : t.powers) tMap[v] = e;
                        bool ok = true;
                        for (const auto& [v, e] : solvePattern) {
                            auto it = tMap.find(v);
                            if (it == tMap.end() || it->second < e) { ok = false; break; }
                        }
                        if (ok) { hasPattern = true; break; }
                    }
                    if (!hasPattern) return false;
                    subst = substituteMonomialPatternInTerms(pt, solvePattern, replacement);
                }
                if (subst.empty()) return false;
                // Build combined reasons.
                std::vector<SatLit> combined;
                std::unordered_set<uint64_t> seenLit;
                auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
                for (auto r : derived[di].reasons) if (seenLit.insert(key(r)).second) combined.push_back(r);
                for (auto r : baseReasons)         if (seenLit.insert(key(r)).second) combined.push_back(r);
                // Eager check BEFORE adding -- if this substitution closes
                // the constraint, return conflict immediately.
                auto cf = eagerCheck(subst, combined);
                if (cf) {
                    eagerConflict = std::move(cf);
                    if (diag) {
                        std::fprintf(stderr, "[OSF-DIAG] EAGER CONFLICT after subst on %s[%zu] var %u: %zu terms refute Eq\n",
                                     label, labelIdx, (unsigned)solveVar, subst.size());
                    }
                    return true;
                }
                size_t outSize = subst.size();
                DerivedConstraint nd;
                nd.terms = std::move(subst);
                nd.rel = Relation::Eq;
                nd.reasons = combined;
                if (addDerived(std::move(nd))) {
                    changed = true;
                    if (diag) {
                        std::fprintf(stderr, "[OSF-DIAG] subst: %s[%zu] %zu -> %zu after subst var %u\n",
                                     label, labelIdx, pt.size(), outSize, (unsigned)solveVar);
                    }
                }
                return false;
            };

            // Substitute into each original constraint. INCLUDE inequalities:
            // substitution into eq4 (an inequality) is sound -- if the
            // substituted version becomes refutable by interval, we still
            // emit conflict via eagerCheck which respects the relation.
            for (size_t ci = 0; ci < constraints.size(); ++ci) {
                // For inequalities, the substituted constraint's relation
                // is the same as the original. Pass via separate path.
                Relation origRel = constraints[ci].rel;
                if (origRel == Relation::Eq) {
                    tryAddSubst(origTerms[ci], {constraints[ci].reason}, "P", ci);
                    if (eagerConflict) return *eagerConflict;
                } else {
                    // For inequalities, manually substitute and check the
                    // resulting interval against the original relation.
                    std::vector<Term> subst;
                    if (solvePattern.size() == 1 && solvePattern[0].second == 1) {
                        bool hasVar = false;
                        for (const auto& t : origTerms[ci]) {
                            for (const auto& [v, e] : t.powers) {
                                if (v == solveVar) { hasVar = true; break; }
                            }
                            if (hasVar) break;
                        }
                        if (!hasVar) continue;
                        subst = substitutePolyInTerms(origTerms[ci], solveVar, replacement);
                    } else {
                        subst = substituteMonomialPatternInTerms(origTerms[ci], solvePattern, replacement);
                    }
                    if (subst.empty()) continue;
                    // Build reasons and check refutation against ORIGINAL rel.
                    std::vector<SatLit> combined;
                    std::unordered_set<uint64_t> seenLit;
                    auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
                    for (auto r : derived[di].reasons) if (seenLit.insert(key(r)).second) combined.push_back(r);
                    if (seenLit.insert(key(constraints[ci].reason)).second) combined.push_back(constraints[ci].reason);
                    auto cf = checkRefutation(subst, combined, origRel);
                    if (cf) {
                        if (diag) {
                            std::fprintf(stderr, "[OSF-DIAG] INEQUALITY P[%zu] closed after subst (%zu terms)\n",
                                         ci, subst.size());
                        }
                        return *cf;
                    }
                }
            }

            // CHAINED substitution: also substitute into previously derived
            // constraints. This is what unlocks mgc_02-style multi-step
            // cascades (gamma0 -> eq2_subst -> solve lambda1 -> eq5_subst).
            //
            // CORRECTNESS: tryAddSubst calls addDerived which can grow the
            // `derived` vector and invalidate references. Snapshot terms +
            // reasons BEFORE the call (same fix shape as S-pair loop above).
            size_t derivedSnap = derived.size();
            for (size_t dj = 0; dj < derivedSnap; ++dj) {
                if (dj == di) continue;
                if (derived[dj].rel != Relation::Eq) continue;
                std::vector<Term> dj_terms_snap = derived[dj].terms;
                std::vector<SatLit> dj_reasons_snap = derived[dj].reasons;
                tryAddSubst(dj_terms_snap, dj_reasons_snap, "D", dj);
                if (eagerConflict) return *eagerConflict;
            }
        }

        // After each iteration, try the focused approach: apply ALL solvable
        // substitutions to each original constraint in cascade. This catches
        // the mgc_02-class cascade where the right substitution sequence
        // exists in derived but breadth-first never combines them on the
        // right target.
        for (size_t ci = 0; ci < constraints.size(); ++ci) {
            const auto& pt = origTerms[ci];
            if (pt.empty()) continue;
            if (pt.size() < 4) continue;
            std::vector<SatLit> baseReason{constraints[ci].reason};
            auto cf = applyAllSubsToTarget(pt, baseReason, constraints[ci].rel, /*maxApps=*/15);
            if (cf) return cf;
        }
        if (!changed) break;
    }
    return std::nullopt;
}

} // namespace xolver
