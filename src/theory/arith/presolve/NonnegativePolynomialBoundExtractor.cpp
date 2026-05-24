#include "theory/arith/presolve/NonnegativePolynomialBoundExtractor.h"

#include <vector>

namespace nlcolver {

namespace {

// A monomial c·∏ xᵢ^eᵢ is manifestly non-negative iff c ≥ 0 and every
// exponent is even.
bool monomialNonneg(const MonomialKey& key, const mpq_class& c) {
    if (c < 0) return false;
    for (const auto& [v, e] : key) { (void)v; if (e % 2 != 0) return false; }
    return true;
}

// floor(q^(1/e)) for q ≥ 0 and even e ≥ 2.  Since n^e is a non-negative
// integer, n^e ≤ q ⟺ n^e ≤ floor(q); use the integer e-th root of floor(q).
mpz_class floorRoot(const mpq_class& q, unsigned long e) {
    if (q < 0) return -1;
    mpz_class zf;
    mpz_fdiv_q(zf.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());  // floor(q)
    mpz_class r;
    mpz_root(r.get_mpz_t(), zf.get_mpz_t(), e);  // floor(zf^(1/e))
    return r;
}

}  // namespace

bool NonnegativePolynomialBoundExtractor::run(PresolveState& st) {
    bool made = false;
    for (size_t ai = 0; ai < st.atoms.size(); ++ai) {
        PresolveAtom& A = st.atoms[ai];
        if (!A.live) continue;
        if (A.rel != Relation::Eq && A.rel != Relation::Leq) continue;

        // poly rel 0.  We need the "Σ(nonneg terms) (=|≤) C" orientation.  For
        // Eq, poly = 0 ⟺ −poly = 0, so try both orientations; for Leq only the
        // as-is form (negating would flip ≤ into the unusable ≥ direction).
        std::vector<RationalPolynomial> cands;
        cands.push_back(A.poly);
        if (A.rel == Relation::Eq) cands.push_back(-A.poly);

        for (const RationalPolynomial& cand : cands) {
            mpq_class c0 = 0;
            bool allNonneg = true;
            bool anyTerm = false;
            for (const auto& [key, c] : cand.terms()) {
                if (key.empty()) { c0 = c; continue; }
                anyTerm = true;
                if (!monomialNonneg(key, c)) { allNonneg = false; break; }
            }
            if (!allNonneg || !anyTerm) continue;

            // poly = Σtⱼ + c0 ⇒ Σtⱼ (=|≤) C with C = -c0.
            mpq_class C = -c0;

            // Negative-RHS conflict: a sum of non-negatives cannot equal/≤ C<0.
            if (C < 0) {
                st.hasConflict = true;
                st.conflict.clause = st.ledger.flattenReasons(A.reasons);
                return true;
            }

            // Per single-var even-power term c·x^e: x^e ≤ C/c ⇒ |x| ≤ (C/c)^(1/e).
            // Only the Int domain gets a variable bound here: the integer e-th
            // root ⌊(C/c)^(1/e)⌋ is exact for integers but would *tighten* the
            // true real bound (excluding valid reals between ⌊·⌋ and the real
            // root), so the Real case is left to Cap. 4's algebraic endpoints.
            if (st.integerDomain) {
                for (const auto& [key, c] : cand.terms()) {
                    if (key.size() != 1) continue;
                    VarId x = key[0].first;
                    int e = key[0].second;
                    if (e < 2 || e % 2 != 0 || c <= 0) continue;
                    mpz_class n = floorRoot(C / c, static_cast<unsigned long>(e));
                    if (n < 0) continue;
                    mpq_class nb(n);
                    IntervalSet bound = IntervalSet::fromRational(
                        IntervalSet::Domain::Int, -nb, false, nb, false);  // [-n, n]
                    if (addBound(st, x, bound, A.reasons)) made = true;
                    if (st.hasConflict) return true;
                }
            }
            break;  // one valid orientation suffices
        }
    }
    return made;
}

} // namespace nlcolver
