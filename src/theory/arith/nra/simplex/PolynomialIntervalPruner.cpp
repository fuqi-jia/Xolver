#include "theory/arith/nra/simplex/PolynomialIntervalPruner.h"
#include "util/EnvParam.h"
#include <algorithm>
#include <functional>
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

[[maybe_unused]] std::optional<SolveForResult> trySolveForLinearVariable(
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

// Enumerate EVERY isolatable monomial pattern in the given term list.
// Necessary because a single derived constraint may admit multiple
// independent substitution directions, e.g. eq2 = gamma0*mu + lambda1*vv1 - vv2
// is isolatable on (gamma0*mu), (lambda1*vv1), and (vv2) — and downstream
// targets may only contain ONE of those patterns. The single-pattern
// variant above (used as fast path) returns whichever comes first in
// term order, which for mgc_02 happens to miss the lambda1*vv1 pattern
// that closes eq5.
std::vector<SolveForResult> trySolveForAllIsolatablePatterns(
        const std::vector<Term>& terms) {
    std::vector<SolveForResult> out;
    for (size_t i = 0; i < terms.size(); ++i) {
        const Term& t = terms[i];
        if (t.coefficient == 0) continue;
        if (t.powers.empty()) continue;
        PowerKey patternPK = canon(t.powers);
        std::unordered_set<VarId> patternVars;
        for (const auto& [v, e] : patternPK) patternVars.insert(v);
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
        r.v = patternPK[0].first;
        r.monomialPattern = patternPK;
        r.coeffOfV = mpq_class(t.coefficient);
        for (size_t j = 0; j < terms.size(); ++j) {
            if (j == i) continue;
            r.remainder.push_back(terms[j]);
        }
        out.push_back(std::move(r));
    }
    return out;
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
[[maybe_unused]] std::vector<Term> varPower(VarId v, int k) {
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

// Returns +1 if the single monomial is provably strictly positive given the
// CertifiedSimplexFacts; -1 if strictly negative; 0 if indeterminate.
//
// Soundness: certifiedSign() returns +1 only when the variable's certified
// lower bound is strictly > 0 (either lo.value > 0, or lo.value == 0 with
// strict). So a +1-tagged monomial is genuinely > 0 in every model, and
// the reasons backing certifiedSign are exactly the bounds we need.
//
// This complements interval analysis: a sum of strict-positive monomials
// has interval lower bound 0 (since each monomial's interval lower is
// open at 0), but the SUM is provably > 0. The interval check would
// miss this; the strict-sign check catches it.
int monomialStrictSign(
        const PolynomialKernel::MonomialTerm& t,
        const CertifiedSimplexFacts& facts,
        std::vector<SatLit>& reasonsOut) {
    if (t.coefficient == 0) return 0;
    int sign = (t.coefficient > 0) ? +1 : -1;
    std::vector<SatLit> local;
    for (const auto& [v, e] : t.powers) {
        int vs = facts.certifiedSign(v);
        if (e % 2 == 0) {
            // v^e >= 0 always; > 0 strict iff vs is strict-positive or strict-negative
            // certifiedSign: +1 = strict>0, -1 = strict<0, +2 = nonneg, -2 = nonpos, 0 = indeterminate
            if (vs != +1 && vs != -1) return 0;
            // sign contribution from v^e (even power) is always +1
            if (vs == +1) { if (auto lo = facts.lower(v)) for (auto r : lo->reasons) local.push_back(r); }
            else            { if (auto hi = facts.upper(v)) for (auto r : hi->reasons) local.push_back(r); }
        } else {
            if (vs == +1) {
                if (auto lo = facts.lower(v)) for (auto r : lo->reasons) local.push_back(r);
            } else if (vs == -1) {
                sign = -sign;
                if (auto hi = facts.upper(v)) for (auto r : hi->reasons) local.push_back(r);
            } else {
                return 0;
            }
        }
    }
    for (auto r : local) reasonsOut.push_back(r);
    return sign;
}

// Returns +1 if every monomial is strict-positive (with at least one nonzero),
// -1 if every is strict-negative, 0 if indeterminate. Collects supporting
// reasons from the strict-sign chain.
int polyStrictSign(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const CertifiedSimplexFacts& facts,
        std::vector<SatLit>& reasonsOut) {
    int polySign = 0;
    std::vector<SatLit> local;
    for (const auto& t : terms) {
        if (t.coefficient == 0) continue;
        int ms = monomialStrictSign(t, facts, local);
        if (ms == 0) return 0;
        if (polySign == 0) polySign = ms;
        else if (polySign != ms) return 0;
    }
    if (polySign != 0) {
        for (auto r : local) reasonsOut.push_back(r);
    }
    return polySign;
}

// AM-GM monomial absorption refutation.
//
// Given a polynomial that is sum of mixed-sign monomials, prove it is strict-
// positive (or strict-negative) by ABSORBING each opposite-sign monomial into
// a pair of same-sign monomials via the AM-GM inequality.
//
// Recall AM-GM: for a, b >= 0, (a + b) / 2 >= sqrt(a * b).
// Apply to monomials c_a * X_a and c_b * X_b (with c_a, c_b > 0, X_a, X_b
// strict-positive products of vars):
//   (c_a * X_a + c_b * X_b) / 2 >= sqrt(c_a * c_b) * sqrt(X_a * X_b)
// So if X_a * X_b = X^2 (geometric-mean condition) and c_a * c_b >= c^2,
//   c_a * X_a + c_b * X_b >= 2 * c * X
// Therefore -c * X + (c_a * X_a + c_b * X_b) / 2 >= 0.
//
// This handles mgc_03-class refutations: after substitution, eq5 reduces to
// (positives) - delta*theta*vv3^3 = 0. delta^2 and theta^2*vv3^6 are both in
// the positives, and (delta^2)(theta^2*vv3^6) = (delta*theta*vv3^3)^2, so
// AM-GM absorbs the negative; remaining positives are strict-positive.
//
// Returns +1 if the polynomial is provably strict-positive via AM-GM absorption,
// -1 for strict-negative, 0 if no proof found.
//
// Per-positive-monomial absorption budget: 1.0 (each positive monomial can
// donate at most half of itself to absorptions; reserved half stays as strict-
// positive residual).
namespace {
    // Helper: hash a canonical power-key for matching X_a * X_b == X^2.
    std::string powerKeyHash(const std::vector<std::pair<VarId, int>>& pk) {
        std::string s;
        for (const auto& [v, e] : pk) {
            s += std::to_string(v);
            s += '^';
            s += std::to_string(e);
            s += ';';
        }
        return s;
    }
    [[maybe_unused]] std::vector<std::pair<VarId, int>> doublePowerKey(
            const std::vector<std::pair<VarId, int>>& pk) {
        std::vector<std::pair<VarId, int>> out;
        out.reserve(pk.size());
        for (const auto& [v, e] : pk) out.push_back({v, 2 * e});
        return out;
    }
    [[maybe_unused]] std::vector<std::pair<VarId, int>> sumPowerKeys(
            const std::vector<std::pair<VarId, int>>& a,
            const std::vector<std::pair<VarId, int>>& b) {
        std::unordered_map<VarId, int> m;
        for (const auto& [v, e] : a) m[v] += e;
        for (const auto& [v, e] : b) m[v] += e;
        std::vector<std::pair<VarId, int>> out;
        out.reserve(m.size());
        for (auto& [v, e] : m) out.push_back({v, e});
        std::sort(out.begin(), out.end());
        return out;
    }
} // anon

int polyStrictSignAMGM(
        const std::vector<PolynomialKernel::MonomialTerm>& terms,
        const CertifiedSimplexFacts& facts,
        std::vector<SatLit>& reasonsOut) {
    // First, the no-absorption test (fast path).
    {
        std::vector<SatLit> r0;
        int ss = polyStrictSign(terms, facts, r0);
        if (ss != 0) { reasonsOut = r0; return ss; }
    }
    // Classify each monomial by its strict-sign.
    struct Item {
        mpq_class absCoeff;
        int sign;
        std::vector<std::pair<VarId, int>> powers;
        std::string keyHash;
        size_t idx;
    };
    std::vector<Item> items;
    std::vector<SatLit> chainReasons;
    for (size_t i = 0; i < terms.size(); ++i) {
        const auto& t = terms[i];
        if (t.coefficient == 0) continue;
        std::vector<SatLit> tmp;
        int s = monomialStrictSign(t, facts, tmp);
        if (s == 0) return 0;
        Item it;
        it.absCoeff = mpq_class(t.coefficient > 0 ? t.coefficient : -t.coefficient);
        it.sign = s;
        for (const auto& [v, e] : t.powers) it.powers.push_back({v, e});
        std::sort(it.powers.begin(), it.powers.end());
        it.keyHash = powerKeyHash(it.powers);
        it.idx = i;
        items.push_back(std::move(it));
        for (auto r : tmp) chainReasons.push_back(r);
    }
    if (items.empty()) return 0;
    // Determine majority sign (the polysign we want to prove).
    int posCount = 0, negCount = 0;
    for (const auto& it : items) {
        if (it.sign > 0) ++posCount;
        else if (it.sign < 0) ++negCount;
    }
    if (posCount == 0 || negCount == 0) {
        // All same sign already; would have been caught by fast path above
        // unless monomialStrictSign disagreed -- in that case bail.
        return 0;
    }
    int majoritySign = (posCount >= negCount) ? +1 : -1;
    // Build an index of MAJORITY-sign items by their key (for X_a * X_b = X^2
    // lookup). Each item gets a remaining-budget of 1.0 (can be partially
    // consumed across absorptions; we reserve half for residual strict
    // positivity).
    struct MajorityItem { mpq_class budget; const Item* ref; };
    std::vector<MajorityItem> majority;
    majority.reserve(items.size());
    for (const auto& it : items) {
        if (it.sign == majoritySign) {
            majority.push_back({mpq_class(1), &it});
        }
    }
    // Index majority items by power-key for fast lookup.
    std::unordered_map<std::string, std::vector<size_t>> byKey;
    for (size_t i = 0; i < majority.size(); ++i) {
        byKey[majority[i].ref->keyHash].push_back(i);
    }
    // For each MINORITY-sign monomial, find an absorbing k-tuple in majority.
    // k-monomial AM-GM: m_1 + ... + m_k >= k * (c_1*c_2*...*c_k)^(1/k) * X,
    // where X_1 * X_2 * ... * X_k = X^k. To absorb -c*X with full budget of
    // each contributor:
    //   k * (c_1*...*c_k)^(1/k) >= c   <=>   c_1*...*c_k >= (c/k)^k
    // (and equivalently k^k * c_1*...*c_k >= c^k).
    //
    // Recursive enumeration: try k = 1, 2, 3, ... up to maxK. At each k,
    // search combinations of majority monomials with sum-of-powers = k*neg.powers
    // and coefficient product >= (c/k)^k. Use full budget of each contributor.
    //
    // Generalizes mgc_02 (k=1 self-pair after cancellation), mgc_03/04 (k=2),
    // mgc_05 (k=3), ..., mgc_N (k=N-2).
    constexpr int kMaxAMGMOrder = 10;   // bounds search; mgc_10 needs k=8
    // Total recursive-search node budget to bound k-tuple enumeration. At
    // k=10 over ~20 majority monomials, naive C(20,10) ~= 184k combinations
    // per negative -- exceed this budget and we bail (returns 0, signaling
    // "indeterminate" so caller can try other strategies).
    constexpr int kMaxAMGMSearchNodes = 20000;
    int searchBudget = kMaxAMGMSearchNodes;
    for (const auto& neg : items) {
        if (neg.sign == majoritySign) continue;
        bool absorbed = false;
        // Try increasing tuple sizes k = 1, 2, ..., maxK.
        for (int k = 1; k <= kMaxAMGMOrder && !absorbed; ++k) {
            // Target: powers sum = k * neg.powers, coeff product >= (c/k)^k
            // Equivalently k^k * prod(c_i) >= c^k.
            // Compute c^k once.
            mpq_class cToK = mpq_class(1);
            for (int i = 0; i < k; ++i) cToK *= neg.absCoeff;
            mpq_class kToK = mpq_class(1);
            for (int i = 0; i < k; ++i) kToK *= mpq_class(k);
            // Target power: k * neg.powers.
            std::unordered_map<VarId, int> targetPowers;
            for (const auto& [v, e] : neg.powers) targetPowers[v] = k * e;
            // Recursive search. We allow REPEATED selection of the same majority
            // index (with budget sharing) -- but to keep it simple here, we
            // enumerate combinations with repetition disabled (each majority
            // monomial used at most once). For repetition cases the multi-pass
            // outer loop over negatives can pick up slack.
            std::function<bool(int, size_t, std::unordered_map<VarId,int>&,
                               mpq_class, std::vector<size_t>&)> rec;
            std::vector<size_t> chosen;
            rec = [&](int remaining, size_t startIdx,
                      std::unordered_map<VarId,int>& accPowers,
                      mpq_class accProdCoeff,
                      std::vector<size_t>& selected) -> bool {
                if (--searchBudget <= 0) return false;   // budget bail
                if (remaining == 0) {
                    // Check power-key match
                    for (const auto& [v, e] : accPowers) {
                        auto it = targetPowers.find(v);
                        if (it == targetPowers.end() || it->second != e) return false;
                    }
                    if (accPowers.size() != targetPowers.size()) return false;
                    // Check coefficient AMGM bound: k^k * prod_c >= c^k
                    mpq_class lhs = kToK * accProdCoeff;
                    if (lhs < cToK) return false;
                    return true;
                }
                for (size_t i = startIdx; i < majority.size(); ++i) {
                    if (majority[i].budget <= 0) continue;
                    const auto& mi = *majority[i].ref;
                    // Prune: any power in mi must not exceed target
                    bool exceeds = false;
                    for (const auto& [v, e] : mi.powers) {
                        auto it = targetPowers.find(v);
                        if (it == targetPowers.end()) { exceeds = true; break; }
                        auto cur = accPowers[v];
                        if (cur + e > it->second) { exceeds = true; break; }
                    }
                    if (exceeds) continue;
                    // Recurse
                    std::unordered_map<VarId,int> savedAcc = accPowers;
                    for (const auto& [v, e] : mi.powers) accPowers[v] += e;
                    selected.push_back(i);
                    if (rec(remaining - 1, i + 1, accPowers,
                            accProdCoeff * mi.absCoeff, selected)) {
                        return true;
                    }
                    selected.pop_back();
                    accPowers = savedAcc;
                }
                return false;
            };
            std::unordered_map<VarId,int> accPowers;
            chosen.clear();
            if (rec(k, 0, accPowers, mpq_class(1), chosen)) {
                // Found a k-tuple absorbing -c*X. Consume full budget of each
                // contributor in `chosen`.
                for (size_t i : chosen) majority[i].budget = mpq_class(0);
                absorbed = true;
            }
        }
        if (!absorbed) return 0;
    }
    // After absorption, the remaining budgets are all >= 0. The polynomial is
    // (absorbed parts) + (sum of remaining-budget * positive monomials).
    // For STRICT positivity, we need AT LEAST ONE majority monomial with strict
    // positive remaining budget (so the sum has a strict-positive contribution).
    bool anyStrictPositiveRemaining = false;
    for (const auto& mi : majority) {
        if (mi.budget > 0) { anyStrictPositiveRemaining = true; break; }
    }
    if (!anyStrictPositiveRemaining) return 0;
    for (auto r : chainReasons) reasonsOut.push_back(r);
    return majoritySign;
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
    // Capped to ensure PHASE3 (Positivstellensatz linear combination) is
    // reachable for mgc_09/10-class cases where the iter loop never converges.
    if (maxIterations < 3) maxIterations = 3;
    if (maxIterations > 3) maxIterations = 3;

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
    // Reduced from 1000 to keep PHASE3 reachable for mgc_09/10 within budget.
    // The iter loop's substitution exploration is O(derived^2 * patterns *
    // constraints * substitution_cost); growing derived past ~30 makes a
    // single iteration take seconds, blocking the Positivstellensatz phase.
    constexpr size_t kMaxDerivedCap = 30;
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

    bool diag = xolver::env::diag("XOLVER_NRA_OSF_DIAG");

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
            // 1-STEP LOOKAHEAD: enumerate every (derived constraint, isolatable
            // pattern) pair, compute the after-substitution polynomial, and
            // pick the substitution that yields the SMALLEST result. This is
            // the difference between a greedy in-order pass that blows up
            // (substituting vv3 -> 2-term replacement into eq5 grows to 50+
            // terms because eq5 contains vv3^2,vv3^3,vv3^4) and a min-growth
            // pass that prefers surgical compound substitutions (lambda1*vv1
            // -> vv2 - gamma0*mu replaces exactly ONE term with a 2-term
            // expansion, keeping the polynomial controllable).
            //
            // Equivalent to: at each round, look one step ahead at all moves,
            // commit to the move with the smallest result. Quadratic per
            // round (n_derived * patterns_per * cost_to_subst) but each
            // application moves us closer to fixpoint.
            constexpr size_t kMaxFocusedTerms = 200;
            std::optional<size_t> bestDi;
            std::optional<SolveForResult> bestSf;
            std::vector<Term> bestAfter;
            std::vector<Term> bestReplacement;
            size_t bestAfterSize = SIZE_MAX;

            for (size_t di = 0; di < derived.size(); ++di) {
                auto allPatterns = trySolveForAllIsolatablePatterns(derived[di].terms);
                if (allPatterns.empty()) continue;
                for (const auto& sf : allPatterns) {
                    mpq_class invScale = mpq_class(-1) / sf.coeffOfV;
                    auto replacement = scaleTerms(sf.remainder, invScale);
                    if (replacement.empty() && !sf.remainder.empty()) continue;
                    std::vector<Term> after;
                    if (sf.monomialPattern.size() == 1 && sf.monomialPattern[0].second == 1) {
                        VarId v = sf.v;
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
                            for (const auto& [v, e] : sf.monomialPattern) {
                                auto it = tMap.find(v);
                                if (it == tMap.end() || it->second < e) { ok = false; break; }
                            }
                            if (ok) { hasPattern = true; break; }
                        }
                        if (!hasPattern) continue;
                        after = substituteMonomialPatternInTerms(current, sf.monomialPattern, replacement);
                    }
                    if (after.empty()) continue;
                    if (after.size() > kMaxFocusedTerms) continue;
                    // Pick smallest result (greedy-min-growth). Tiebreaks:
                    //  (a) strict size reduction over identity moves
                    //  (b) compound pattern (>1 var) over single-var, so
                    //      vv2<->vv3 var-rename oscillations don't dominate
                    //      and starve the closing lambda1*vv1 substitution.
                    bool betterPrimary = (after.size() < bestAfterSize);
                    bool tiedPrimary   = (after.size() == bestAfterSize);
                    bool betterSecondary = false;
                    if (tiedPrimary && bestSf) {
                        size_t curBestVars = bestSf->monomialPattern.size();
                        size_t candVars    = sf.monomialPattern.size();
                        // Prefer compound (more vars) when same result size,
                        // breaks var-rename oscillation that blocks mgc_03+.
                        if (candVars > curBestVars) betterSecondary = true;
                    }
                    if (tiedPrimary && !bestSf && after.size() <= current.size()) {
                        betterSecondary = true;   // first applicable
                    }
                    if (betterPrimary || betterSecondary) {
                        bestAfterSize = after.size();
                        bestAfter = after;
                        bestDi = di;
                        bestSf = sf;
                        bestReplacement = replacement;
                    }
                }
            }
            if (!bestDi) break;   // no applicable substitution this round
            {
                size_t di = *bestDi;
                const auto& sf = *bestSf;
                current = std::move(bestAfter);
                for (auto r : derived[di].reasons) {
                    if (reasonsSet.insert(rkey(r)).second) reasons.push_back(r);
                }
                anyApplied = true;
                if (diag) {
                    std::fprintf(stderr, "[OSF-FOCUS] applied D[%zu] pattern=[", di);
                    for (const auto& [v, e] : sf.monomialPattern) {
                        std::fprintf(stderr, "%u^%d,", (unsigned)v, e);
                    }
                    std::fprintf(stderr, "] repl=%zu terms; current now %zu terms\n",
                                 bestReplacement.size(), current.size());
                }
                // Check refutation. Use both the additive interval bound
                // AND the strict-sign-definite test (which catches the
                // sum-of-strict-positives-equals-zero contradiction that
                // additive interval analysis misses because each monomial's
                // interval lower is open at 0).
                std::vector<SatLit> usedR;
                PolyInterval iv = intervalOfTerms(current, facts, usedR);
                bool refuted = false;
                if (!iv.indeterminate) {
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
                }
                std::vector<SatLit> strictR;
                if (!refuted) {
                    int ssign = polyStrictSign(current, facts, strictR);
                    if (ssign == 0) {
                        ssign = polyStrictSignAMGM(current, facts, strictR);
                        if (diag) {
                            std::fprintf(stderr, "[OSF-FOCUS] AMGM on %zu-term -> sign=%d\n",
                                         current.size(), ssign);
                        }
                    }
                    if (ssign != 0) {
                        switch (targetRel) {
                            case Relation::Eq:
                                refuted = true;   // strict positive != 0 or strict negative != 0
                                break;
                            case Relation::Geq:
                                if (ssign < 0) refuted = true;
                                break;
                            case Relation::Gt:
                                if (ssign <= 0) refuted = true;  // ssign==0 already excluded
                                break;
                            case Relation::Leq:
                                if (ssign > 0) refuted = true;
                                break;
                            case Relation::Lt:
                                if (ssign >= 0) refuted = true;
                                break;
                            default: break;
                        }
                    }
                }
                if (refuted) {
                    IntervalConflict conf;
                    for (auto r : reasons) conf.reasons.push_back(r);
                    for (auto r : usedR) {
                        if (reasonsSet.insert(rkey(r)).second) conf.reasons.push_back(r);
                    }
                    for (auto r : strictR) {
                        if (reasonsSet.insert(rkey(r)).second) conf.reasons.push_back(r);
                    }
                    conf.explanation = "focused chained substitution closes target";
                    if (diag) {
                        std::fprintf(stderr, "[OSF-FOCUS] CONFLICT after %d substitutions; final %zu terms\n",
                                     round + 1, current.size());
                    }
                    return conf;
                }
            } // end apply-best block
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
            // Enumerate ALL isolatable patterns per derived constraint, not
            // just the first. mgc_02 specifically needs the lambda1*vv1
            // pattern in eq2 (which is the second isolatable pattern, the
            // first being gamma0*mu — irrelevant to eq5 since eq5 has no
            // gamma0).
            const auto allPatterns = trySolveForAllIsolatablePatterns(derived[di].terms);
            if (allPatterns.empty()) continue;
            for (const auto& patternResult : allPatterns) {
            const VarId solveVar = patternResult.v;
            const PowerKey solvePattern = patternResult.monomialPattern;
            // Replacement poly: -remainder / coeffOfV (mpq for the scale).
            mpq_class invScale = mpq_class(-1) / patternResult.coeffOfV;
            std::vector<Term> replacement = scaleTerms(patternResult.remainder, invScale);
            if (replacement.empty() && !patternResult.remainder.empty()) continue;  // bail on fractional

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
            } // end for (const auto& patternResult : allPatterns)
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

    // PHASE 3: Positivstellensatz linear combination strategy.
    //
    // For each (EQ target, INEQ constraint) pair, build a combined polynomial
    // K = eq_LHS + lambda * ineq_LHS for small rational lambda > 0, then run
    // the focused substitution cascade on K. If K reduces to a sign-definite
    // form contradicting its inferred relation, refutation.
    //
    // Math: eq_LHS = 0 and ineq_LHS rel 0 imply K = lambda * (something rel 0).
    // For lambda > 0: K inherits the ineq's strict relation.
    //
    // This handles cases where the EQ target alone can't reach sign-definite
    // (mgc_09/10 family: residual after substitution has a -c*X term that
    // can't be absorbed by k-AM-GM in the pure-variable subset). Combining
    // with the inequality contributes additional sign-definite mass that may
    // tip the AM-GM tuple search past the threshold.
    if (diag) {
        std::fprintf(stderr, "[OSF-PHASE3] linear-combination search begins\n");
    }
    // Positivstellensatz refutation: form K = a*eq_LHS + b*ineq_LHS with
    // integer a, b. Since eq_LHS = 0, K's value is b*ineq_LHS_value, so:
    //   ineq.rel = Lt: K_value = b*(<0). K > 0 iff b < 0, K < 0 iff b > 0.
    //   ineq.rel = Gt: K_value = b*(>0). K > 0 iff b > 0, K < 0 iff b < 0.
    // For mgc_N family the closing certificate has form (a, b) = (k, -(N-2))
    // or similar small-integer ratio that cancels the residual coefficient.
    struct ABPair { int a; int b; };
    const ABPair candidates[] = {
        // Symmetric small ratios
        {1, 1}, {1, -1}, {1, 2}, {1, -2}, {1, 3}, {1, -3},
        {2, 1}, {2, -1}, {2, 3}, {2, -3}, {2, 5}, {2, -5},
        {3, 1}, {3, -1}, {3, 2}, {3, -2}, {3, 5}, {3, -5}, {3, 7}, {3, -7},
        {5, 2}, {5, -2}, {5, 3}, {5, -3}, {5, 7}, {5, -7},
        {7, 3}, {7, -3}, {7, 5}, {7, -5}, {7, 10}, {7, -10},
        // mgc-family residual coefficients: mgc_N residual is (N-2),
        // closing typically wants a = (residual leader from ineq) and
        // b = -(eq residual). E.g., mgc_09: a=10, b=-7 cancels residual.
        {10, -7}, {10, 7}, {10, -1}, {10, -3}, {10, -5}, {10, -9},
        {10, 1}, {10, 3}, {10, 5}, {10, 9},
        {11, -8}, {11, 8}, {12, -9}, {12, 9}, {12, -10}, {12, 10},
    };
    auto flipRelation = [](Relation r) {
        switch (r) {
            case Relation::Lt: return Relation::Gt;
            case Relation::Gt: return Relation::Lt;
            case Relation::Leq: return Relation::Geq;
            case Relation::Geq: return Relation::Leq;
            default: return r;
        }
    };
    for (size_t eqIdx = 0; eqIdx < constraints.size(); ++eqIdx) {
        if (constraints[eqIdx].rel != Relation::Eq) continue;
        const auto& eqTerms = origTerms[eqIdx];
        if (eqTerms.size() < 5) continue;
        for (size_t iqIdx = 0; iqIdx < constraints.size(); ++iqIdx) {
            const auto& iqRel = constraints[iqIdx].rel;
            if (iqRel != Relation::Lt && iqRel != Relation::Gt) continue;
            const auto& iqTerms = origTerms[iqIdx];
            if (iqTerms.size() < 3) continue;
            for (const auto& ab : candidates) {
                auto scaledEq   = scaleTerms(eqTerms,   mpq_class(ab.a));
                auto scaledIneq = scaleTerms(iqTerms,   mpq_class(ab.b));
                if (scaledEq.empty()  && !eqTerms.empty())  continue;
                if (scaledIneq.empty() && !iqTerms.empty()) continue;
                auto combined = addTerms(scaledEq, scaledIneq);
                if (combined.empty()) continue;
                // Determine combined relation. eq contributes 0; combined value
                // = b * ineq_value. Sign of b * ineq:
                Relation combinedRel = iqRel;
                if (ab.b < 0) combinedRel = flipRelation(iqRel);
                std::vector<SatLit> baseReason{constraints[eqIdx].reason, constraints[iqIdx].reason};
                if (diag) {
                    std::fprintf(stderr, "[OSF-PHASE3] try %d*P[%zu]+%d*P[%zu] rel=%d -> %zu terms\n",
                                 ab.a, eqIdx, ab.b, iqIdx, (int)combinedRel, combined.size());
                }
                auto cf = applyAllSubsToTarget(combined, baseReason, combinedRel, /*maxApps=*/15);
                if (cf) {
                    if (diag) {
                        std::fprintf(stderr, "[OSF-PHASE3] CONFLICT via %d*P[%zu]+%d*P[%zu]\n",
                                     ab.a, eqIdx, ab.b, iqIdx);
                    }
                    return cf;
                }
            }
        }
    }
    return std::nullopt;
}

} // namespace xolver
