#include "theory/core/DerivedFact.h"

#include <algorithm>
#include <unordered_set>

namespace xolver {

namespace {

// A fully rational/±Inf view of an Interval, used for exact intersection.
// Algebraic endpoints are widened (lower → bracket.lower, upper → bracket.upper)
// so the resulting interval is a SUPERSET of the true one.
struct NormInterval {
    bool loInf = true;   // lower is -Inf
    mpq_class lo;
    bool loOpen = true;
    bool hiInf = true;   // upper is +Inf
    mpq_class hi;
    bool hiOpen = true;
    bool empty = false;
};

NormInterval normalize(const Interval& iv) {
    NormInterval n;
    // lower
    switch (iv.lower.kind) {
        case BoundEndpoint::Kind::NegInf: n.loInf = true; break;
        case BoundEndpoint::Kind::PosInf: n.empty = true; break;  // lower=+Inf is degenerate
        case BoundEndpoint::Kind::Rational:
            n.loInf = false; n.lo = iv.lower.rationalValue; n.loOpen = iv.lowerOpen; break;
        case BoundEndpoint::Kind::Algebraic:
            // widen: use the bracket's lower bound, closed (superset)
            n.loInf = false; n.lo = iv.lower.algebraicValue.lower; n.loOpen = false; break;
    }
    // upper
    switch (iv.upper.kind) {
        case BoundEndpoint::Kind::PosInf: n.hiInf = true; break;
        case BoundEndpoint::Kind::NegInf: n.empty = true; break;  // upper=-Inf is degenerate
        case BoundEndpoint::Kind::Rational:
            n.hiInf = false; n.hi = iv.upper.rationalValue; n.hiOpen = iv.upperOpen; break;
        case BoundEndpoint::Kind::Algebraic:
            n.hiInf = false; n.hi = iv.upper.algebraicValue.upper; n.hiOpen = false; break;
    }
    if (!n.empty && !n.loInf && !n.hiInf) {
        if (n.lo > n.hi) n.empty = true;
        else if (n.lo == n.hi && (n.loOpen || n.hiOpen)) n.empty = true;
    }
    return n;
}

// Intersect two normalized intervals.
NormInterval intersectNorm(const NormInterval& a, const NormInterval& b) {
    if (a.empty || b.empty) { NormInterval e; e.empty = true; return e; }
    NormInterval r;
    // lower = max(a.lo, b.lo)
    if (a.loInf && b.loInf) { r.loInf = true; }
    else if (a.loInf) { r.loInf = false; r.lo = b.lo; r.loOpen = b.loOpen; }
    else if (b.loInf) { r.loInf = false; r.lo = a.lo; r.loOpen = a.loOpen; }
    else {
        r.loInf = false;
        if (a.lo > b.lo) { r.lo = a.lo; r.loOpen = a.loOpen; }
        else if (b.lo > a.lo) { r.lo = b.lo; r.loOpen = b.loOpen; }
        else { r.lo = a.lo; r.loOpen = a.loOpen || b.loOpen; }
    }
    // upper = min(a.hi, b.hi)
    if (a.hiInf && b.hiInf) { r.hiInf = true; }
    else if (a.hiInf) { r.hiInf = false; r.hi = b.hi; r.hiOpen = b.hiOpen; }
    else if (b.hiInf) { r.hiInf = false; r.hi = a.hi; r.hiOpen = a.hiOpen; }
    else {
        r.hiInf = false;
        if (a.hi < b.hi) { r.hi = a.hi; r.hiOpen = a.hiOpen; }
        else if (b.hi < a.hi) { r.hi = b.hi; r.hiOpen = b.hiOpen; }
        else { r.hi = a.hi; r.hiOpen = a.hiOpen || b.hiOpen; }
    }
    if (!r.loInf && !r.hiInf) {
        if (r.lo > r.hi) { r.empty = true; }
        else if (r.lo == r.hi && (r.loOpen || r.hiOpen)) { r.empty = true; }
    }
    return r;
}

Interval denorm(const NormInterval& n) {
    Interval iv;
    iv.lower = n.loInf ? BoundEndpoint::negInf() : BoundEndpoint::rational(n.lo);
    iv.lowerOpen = n.loInf ? true : n.loOpen;
    iv.upper = n.hiInf ? BoundEndpoint::posInf() : BoundEndpoint::rational(n.hi);
    iv.upperOpen = n.hiInf ? true : n.hiOpen;
    return iv;
}

}  // namespace

IntervalSet IntervalSet::intersect(const IntervalSet& other) const {
    IntervalSet result(domain);
    std::vector<NormInterval> outs;
    for (const auto& a : intervals) {
        NormInterval na = normalize(a);
        if (na.empty) continue;
        for (const auto& b : other.intervals) {
            NormInterval nb = normalize(b);
            if (nb.empty) continue;
            NormInterval r = intersectNorm(na, nb);
            if (!r.empty) outs.push_back(r);
        }
    }
    std::sort(outs.begin(), outs.end(), [](const NormInterval& x, const NormInterval& y) {
        if (x.loInf != y.loInf) return x.loInf;          // -Inf first
        if (x.loInf) return false;
        if (x.lo != y.lo) return x.lo < y.lo;
        return !x.loOpen && y.loOpen;                    // closed before open at same point
    });
    for (auto& n : outs) result.intervals.push_back(denorm(n));
    return result;
}

bool IntervalSet::isFiniteInt() const {
    if (domain != Domain::Int) return false;
    if (intervals.empty()) return true;  // empty set is trivially finite
    for (const auto& iv : intervals) {
        // Both endpoints must be finite rationals.  Algebraic / ±Inf endpoints
        // are not admitted here: they disable Cap. 9 (defer), which is sound.
        if (!iv.lower.isRational() || !iv.upper.isRational()) return false;
    }
    return true;
}

std::vector<mpz_class> IntervalSet::integerPoints() const {
    std::vector<mpz_class> pts;
    if (!isFiniteInt()) return pts;
    for (const auto& iv : intervals) {
        const mpq_class& lo = iv.lower.rationalValue;
        const mpq_class& hi = iv.upper.rationalValue;
        // smallest integer >= lo (closed) or > lo (open)
        mpz_class loInt;
        {
            mpz_class fl;
            mpz_fdiv_q(fl.get_mpz_t(), lo.get_num().get_mpz_t(), lo.get_den().get_mpz_t());
            // fl = floor(lo); ceil(lo) = fl if lo integer else fl+1
            bool loIsInt = (lo.get_den() == 1);
            mpz_class ceilLo = loIsInt ? fl : (fl + 1);
            if (iv.lowerOpen && loIsInt) loInt = ceilLo + 1;  // strictly greater
            else loInt = ceilLo;
        }
        // largest integer <= hi (closed) or < hi (open)
        mpz_class hiInt;
        {
            mpz_class fl;
            mpz_fdiv_q(fl.get_mpz_t(), hi.get_num().get_mpz_t(), hi.get_den().get_mpz_t());
            bool hiIsInt = (hi.get_den() == 1);
            if (iv.upperOpen && hiIsInt) hiInt = fl - 1;  // strictly less
            else hiInt = fl;  // floor(hi)
        }
        for (mpz_class k = loInt; k <= hiInt; ++k) pts.push_back(k);
    }
    std::sort(pts.begin(), pts.end());
    pts.erase(std::unique(pts.begin(), pts.end()), pts.end());
    return pts;
}

bool IntervalSet::hasIntegerPoint() const {
    for (const auto& iv : intervals) {
        // Algebraic / unbounded endpoints: an unbounded side always admits
        // integers; an algebraic endpoint is treated as admitting one (sound
        // for the no-false-UNSAT direction).
        bool loInf = iv.lower.isNegInf();
        bool hiInf = iv.upper.isPosInf();
        if (loInf || hiInf) return true;
        if (iv.lower.isAlgebraic() || iv.upper.isAlgebraic()) return true;
        const mpq_class& lo = iv.lower.rationalValue;
        const mpq_class& hi = iv.upper.rationalValue;
        mpz_class loInt;
        {
            mpz_class fl;
            mpz_fdiv_q(fl.get_mpz_t(), lo.get_num().get_mpz_t(), lo.get_den().get_mpz_t());
            bool loIsInt = (lo.get_den() == 1);
            mpz_class ceilLo = loIsInt ? fl : (fl + 1);
            loInt = (iv.lowerOpen && loIsInt) ? (ceilLo + 1) : ceilLo;
        }
        mpz_class hiInt;
        {
            mpz_class fl;
            mpz_fdiv_q(fl.get_mpz_t(), hi.get_num().get_mpz_t(), hi.get_den().get_mpz_t());
            bool hiIsInt = (hi.get_den() == 1);
            hiInt = (iv.upperOpen && hiIsInt) ? (fl - 1) : fl;
        }
        if (loInt <= hiInt) return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// DerivationLedger
// ---------------------------------------------------------------------------
std::vector<SatLit> DerivationLedger::flattenReasons(const ReasonNode& node) const {
    std::vector<SatLit> out;
    std::unordered_set<size_t> visited;
    std::vector<size_t> stack(node.upstreamIndices.begin(), node.upstreamIndices.end());
    for (const auto& l : node.baseLiterals) out.push_back(l);
    while (!stack.empty()) {
        size_t idx = stack.back();
        stack.pop_back();
        if (!visited.insert(idx).second) continue;
        if (idx >= facts_.size()) continue;
        const ReasonNode& r = facts_[idx].reasons;
        for (const auto& l : r.baseLiterals) out.push_back(l);
        for (size_t up : r.upstreamIndices) {
            if (!visited.count(up)) stack.push_back(up);
        }
    }
    // dedup
    std::sort(out.begin(), out.end(), [](SatLit a, SatLit b) {
        if (a.var != b.var) return a.var < b.var;
        return a.sign < b.sign;
    });
    out.erase(std::unique(out.begin(), out.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), out.end());
    return out;
}

std::vector<SatLit> DerivationLedger::flattenReasons(size_t index) const {
    if (index >= facts_.size()) return {};
    return flattenReasons(facts_[index].reasons);
}

} // namespace xolver
