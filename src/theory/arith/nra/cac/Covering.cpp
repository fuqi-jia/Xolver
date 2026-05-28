#include "theory/arith/nra/cac/Covering.h"

#include <algorithm>

namespace xolver {

// --- CacInterval ------------------------------------------------------------

bool CacInterval::valid() const {
    const int c = lo.compare(hi);
    if (c < 0) return true;                 // lo < hi : nonempty
    if (c == 0) return !loOpen && !hiOpen;  // lo == hi : only the closed point
    return false;                           // lo > hi : empty
}

bool CacInterval::contains(const RealValue& x) const {
    const ExtendedRealValue ex = ExtendedRealValue::finite(x);
    const int cl = lo.compare(ex);   // lo vs x
    const int ch = hi.compare(ex);   // hi vs x
    const bool loOk = loOpen ? (cl < 0) : (cl <= 0);   // lo < x / lo <= x
    const bool hiOk = hiOpen ? (ch > 0) : (ch >= 0);   // hi > x / hi >= x
    return loOk && hiOk;
}

// --- rationalStrictlyBetween ------------------------------------------------

mpq_class rationalStrictlyBetween(const RealValue& a, const RealValue& b) {
    // Precondition: a < b. Fast path when both endpoints are rational.
    auto ar = a.tryAsRational();
    auto br = b.tryAsRational();
    if (ar && br) return (*ar + *br) / 2;

    // Bisection over a rational bracket [lo, hi] ⊇ [a, b]. Dyadic midpoints are
    // dense in ℝ, so some midpoint lands strictly inside the positive-width
    // interval (a, b); each step halves the bracket toward the boundary it
    // overshoots. Bounds from floor/ceil are exact for both kinds.
    mpq_class lo(a.floor());
    mpq_class hi(b.ceil());
    if (lo >= hi) { lo -= 1; hi += 1; }
    for (int iter = 0; iter < 100000; ++iter) {
        mpq_class m = (lo + hi) / 2;
        m.canonicalize();
        const RealValue mv = RealValue::fromMpq(m);
        if (mv.compare(a) <= 0)      { lo = m; }   // m <= a : move up
        else if (mv.compare(b) >= 0) { hi = m; }   // m >= b : move down
        else                         { return m; } // a < m < b
    }
    return (lo + hi) / 2;  // unreachable for well-separated reals
}

// --- Covering ---------------------------------------------------------------

void Covering::add(const CacInterval& iv) {
    if (iv.valid()) intervals_.push_back(iv);
}

bool Covering::covers(const RealValue& x) const {
    for (const auto& iv : intervals_) if (iv.contains(x)) return true;
    return false;
}

std::vector<CacInterval> Covering::merged() const {
    std::vector<CacInterval> v;
    v.reserve(intervals_.size());
    for (const auto& iv : intervals_) if (iv.valid()) v.push_back(iv);
    if (v.empty()) return v;

    std::sort(v.begin(), v.end(), [](const CacInterval& a, const CacInterval& b) {
        const int cl = a.lo.compare(b.lo);
        if (cl != 0) return cl < 0;
        if (a.loOpen != b.loOpen) return !a.loOpen;   // closed-lo first
        return a.hi.compare(b.hi) > 0;                // wider first
    });

    std::vector<CacInterval> out;
    CacInterval cur = v[0];
    for (size_t i = 1; i < v.size(); ++i) {
        const CacInterval& iv = v[i];   // iv.lo >= cur.lo (sorted)
        const int c = cur.hi.compare(iv.lo);
        // Connected iff they overlap (c>0), or touch at a point covered by at
        // least one side (c==0 and not both open there).
        const bool connected = (c > 0) || (c == 0 && !(cur.hiOpen && iv.loOpen));
        if (connected) {
            const int hc = cur.hi.compare(iv.hi);
            if (hc < 0)       { cur.hi = iv.hi; cur.hiOpen = iv.hiOpen; }
            else if (hc == 0) { cur.hiOpen = cur.hiOpen && iv.hiOpen; }
            // hc > 0: cur already extends past iv — keep cur.hi/hiOpen.
        } else {
            out.push_back(cur);
            cur = iv;
        }
    }
    out.push_back(cur);
    return out;
}

bool Covering::isComplete() const {
    const auto m = merged();
    return m.size() == 1 && m[0].lo.isNegInf() && m[0].hi.isPosInf();
}

std::optional<RealValue> Covering::sampleUncovered() const {
    const auto m = merged();
    if (m.empty()) return RealValue::fromInt(0);   // nothing excluded

    // Left gap: a rational below the leftmost finite lower bound.
    if (!m.front().lo.isNegInf()) {
        const mpz_class q = m.front().lo.asFinite().floor() - 1;
        return RealValue::fromMpq(mpq_class(q));
    }

    // Interior gaps between consecutive merged intervals.
    for (size_t i = 0; i + 1 < m.size(); ++i) {
        const ExtendedRealValue& hi = m[i].hi;
        const ExtendedRealValue& lo = m[i + 1].lo;
        const int c = hi.compare(lo);
        if (c < 0) {
            // Open gap (hi, lo); both finite (interior endpoints).
            return RealValue::fromMpq(
                rationalStrictlyBetween(hi.asFinite(), lo.asFinite()));
        }
        if (c == 0 && m[i].hiOpen && m[i + 1].loOpen) {
            // Isolated point-gap: both intervals open at the shared endpoint.
            return hi.asFinite();
        }
    }

    // Right gap: a rational above the rightmost finite upper bound.
    if (!m.back().hi.isPosInf()) {
        const mpz_class q = m.back().hi.asFinite().ceil() + 1;
        return RealValue::fromMpq(mpq_class(q));
    }

    return std::nullopt;   // union == ℝ
}

} // namespace xolver
