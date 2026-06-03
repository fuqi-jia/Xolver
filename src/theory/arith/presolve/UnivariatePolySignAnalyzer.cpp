#include "theory/arith/presolve/UnivariatePolySignAnalyzer.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"
#include "theory/arith/nra/core/CdcacValue.h"

#include <algorithm>

namespace xolver {

UnivariatePolySignAnalyzer::UnivariatePolySignAnalyzer() = default;
UnivariatePolySignAnalyzer::~UnivariatePolySignAnalyzer() = default;

namespace {

// Sign of the integer-coefficient (high-to-low) univariate at rational q.
int signOfRationalEval(const std::vector<mpz_class>& hi2lo, const mpq_class& q) {
    mpq_class acc = 0;
    for (const auto& c : hi2lo) acc = acc * q + mpq_class(c);
    if (acc > 0) return 1;
    if (acc < 0) return -1;
    return 0;
}

bool relHoldsForSign(int s, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return s == 0;
        case Relation::Neq: return s != 0;
        case Relation::Lt:  return s < 0;
        case Relation::Leq: return s <= 0;
        case Relation::Gt:  return s > 0;
        case Relation::Geq: return s >= 0;
    }
    return false;
}

mpq_class rootRep(const RealAlg& r) {
    if (r.isRational()) return r.rational;
    return (r.root.lower + r.root.upper) / 2;
}

BoundEndpoint rootEndpoint(const RealAlg& r) {
    if (r.isRational()) return BoundEndpoint::rational(r.rational);
    return BoundEndpoint::algebraic(r.root);
}

mpz_class lcm2(const mpz_class& a, const mpz_class& b) {
    if (a == 0 || b == 0) return (a == 0) ? abs(b) : abs(a);
    mpz_class g;
    mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return abs(a / g * b);
}

struct Segment {
    BoundEndpoint lo, hi;
    bool loOpen, hiOpen;
    int sign;
};

}  // namespace

bool UnivariatePolySignAnalyzer::run(PresolveState& st) {
    if (!backend_) backend_ = std::make_unique<LibpolyBackend>(st.kernel);
    const auto dom = st.integerDomain ? IntervalSet::Domain::Int : IntervalSet::Domain::Real;

    bool made = false;
    for (size_t i = 0; i < st.atoms.size(); ++i) {
        PresolveAtom& A = st.atoms[i];
        if (!A.live) continue;
        auto vars = A.poly.variables();
        if (vars.size() != 1) continue;
        VarId x = *vars.begin();
        if (totalDegree(A.poly) < 1) continue;

        // Skip atoms already analyzed with identical content (pure function of
        // poly+rel); prevents re-isolation and spurious fixpoint progress.
        auto sig = std::make_pair(A.rel, A.poly.terms());
        auto memoIt = analyzed_.find(i);
        if (memoIt != analyzed_.end() && memoIt->second == sig) continue;
        analyzed_[i] = sig;

        // Build integer coefficients high-to-low (clear denominators).
        auto lowToHigh = A.poly.coefficients(x);
        bool ok = true;
        mpz_class den = 1;
        for (const auto& c : lowToHigh) {
            if (!c.isZero() && !c.isConstant()) { ok = false; break; }
            mpq_class cv = c.isZero() ? mpq_class(0) : c.constantValue();
            den = lcm2(den, cv.get_den());
        }
        if (!ok) continue;
        std::vector<mpz_class> hi2lo;
        for (int e = static_cast<int>(lowToHigh.size()) - 1; e >= 0; --e) {
            mpq_class cv = lowToHigh[e].isZero() ? mpq_class(0) : lowToHigh[e].constantValue();
            mpq_class scaled = cv * den;
            hi2lo.push_back(scaled.get_num());
        }

        // Isolate real roots.
        UniPolyId up = backend_->allocUni(hi2lo);
        RootSet rs = backend_->isolateRealRoots(up);
        // Firewall bail (oversize coeffs): empty roots here would falsely imply a
        // sign-invariant line ⇒ unsound domain narrowing. Skip this atom instead.
        if (rs.crashOccurred) continue;
        std::vector<RealAlg> roots = rs.roots;
        std::sort(roots.begin(), roots.end(),
                  [](const RealAlg& a, const RealAlg& b) { return rootRep(a) < rootRep(b); });

        // sample a rational strictly inside an open section.
        auto sampleBetween = [&](bool aInf, const RealAlg& a, bool bInf, const RealAlg& b) -> mpq_class {
            if (aInf && bInf) return mpq_class(0);
            if (aInf) {
                mpq_class br = b.isRational() ? b.rational : b.root.lower;
                return br - 1;
            }
            if (bInf) {
                mpq_class ar = a.isRational() ? a.rational : a.root.upper;
                return ar + 1;
            }
            mpq_class ar = a.isRational() ? a.rational : a.root.upper;
            mpq_class br = b.isRational() ? b.rational : b.root.lower;
            return (ar + br) / 2;
        };

        // Build the sign-invariant segments.
        std::vector<Segment> segs;
        const int k = static_cast<int>(roots.size());
        RealAlg dummy = RealAlg::fromRational(0);
        if (k == 0) {
            segs.push_back({BoundEndpoint::negInf(), BoundEndpoint::posInf(), true, true,
                            signOfRationalEval(hi2lo, mpq_class(0))});
        } else {
            segs.push_back({BoundEndpoint::negInf(), rootEndpoint(roots[0]), true, true,
                            signOfRationalEval(hi2lo, sampleBetween(true, dummy, false, roots[0]))});
            for (int j = 0; j < k; ++j) {
                segs.push_back({rootEndpoint(roots[j]), rootEndpoint(roots[j]), false, false, 0});
                if (j + 1 < k) {
                    segs.push_back({rootEndpoint(roots[j]), rootEndpoint(roots[j + 1]), true, true,
                                    signOfRationalEval(hi2lo, sampleBetween(false, roots[j], false, roots[j + 1]))});
                } else {
                    segs.push_back({rootEndpoint(roots[j]), BoundEndpoint::posInf(), true, true,
                                    signOfRationalEval(hi2lo, sampleBetween(false, roots[j], true, dummy))});
                }
            }
        }

        // Coalesce maximal satisfying runs into the satisfying IntervalSet.
        IntervalSet sat(dom);
        int n = static_cast<int>(segs.size());
        int j = 0;
        while (j < n) {
            if (!relHoldsForSign(segs[j].sign, A.rel)) { ++j; continue; }
            int start = j;
            while (j < n && relHoldsForSign(segs[j].sign, A.rel)) ++j;
            int end = j - 1;
            Interval iv;
            iv.lower = segs[start].lo; iv.lowerOpen = segs[start].loOpen;
            iv.upper = segs[end].hi;   iv.upperOpen = segs[end].hiOpen;
            sat.intervals.push_back(iv);
        }

        // Decide.
        ReasonNode atomReasons;
        atomReasons.baseLiterals = st.ledger.flattenReasons(A.reasons);

        bool unsat = st.integerDomain ? !sat.hasIntegerPoint() : sat.isEmpty();
        if (unsat) {
            st.hasConflict = true;
            st.conflict.clause = atomReasons.baseLiterals;
            return true;
        }
        if (sat.isUniverse()) {
            A.live = false;  // atom always holds
            made = true;
            continue;
        }
        if (addBound(st, x, sat, A.reasons)) made = true;
        if (st.hasConflict) return true;
    }
    return made;
}

} // namespace xolver
