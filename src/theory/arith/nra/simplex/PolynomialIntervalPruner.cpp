#include "theory/arith/nra/simplex/PolynomialIntervalPruner.h"
#include <algorithm>
#include <unordered_set>

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

} // namespace xolver
