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

    auto addDerived = [&](DerivedConstraint d) -> bool {
        std::string k = termsKey(d.terms);
        if (seen.count(k)) return false;
        seen.insert(k);
        derived.push_back(std::move(d));
        return true;
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

    for (int iter = 0; iter < maxIterations; ++iter) {
        bool changed = false;

        // Check each derived constraint's interval for contradiction.
        for (const auto& d : derived) {
            std::vector<SatLit> used;
            PolyInterval iv = intervalOfTerms(d.terms, facts, used);
            if (iv.indeterminate) continue;
            if (intervalRefutesEq(iv)) {
                IntervalConflict conf;
                std::unordered_set<uint64_t> seenLit;
                auto key = [](SatLit l) { return (uint64_t(l.var) << 1) | uint64_t(l.sign ? 1 : 0); };
                for (auto r : d.reasons) if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
                for (auto r : used)      if (seenLit.insert(key(r)).second) conf.reasons.push_back(r);
                conf.explanation = "iterative factoring + interval refutation";
                return conf;
            }
        }

        // Try factoring the derived constraints further.
        std::vector<DerivedConstraint> nextRound;
        for (const auto& d : derived) {
            // Build a temporary IntervalConstraint wrapper via PolyId construction;
            // but for derived term-lists we operate on the term level directly.
            // Reuse tryFactorOnce by reconstructing a poly? Skip for now:
            // we focus on round-1 factoring (most cases need only one step).
        }
        (void)nextRound;
        if (!changed) break;
    }
    return std::nullopt;
}

} // namespace xolver
