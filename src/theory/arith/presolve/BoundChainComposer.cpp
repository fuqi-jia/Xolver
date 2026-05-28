#include "theory/arith/presolve/BoundChainComposer.h"

#include <algorithm>

namespace xolver {

namespace {

// Coefficient of the degree-1 monomial {(v,1)} in p, else 0.
mpq_class linearCoeff(const RationalPolynomial& p, VarId v) {
    MonomialKey key = {{v, 1}};
    auto it = p.terms().find(key);
    return (it == p.terms().end()) ? mpq_class(0) : it->second;
}

bool polyEqual(const RationalPolynomial& a, const RationalPolynomial& b) {
    return a.terms() == b.terms();
}

ReasonNode unionReasons(const PresolveState& st, const ReasonNode& a, const ReasonNode& b) {
    ReasonNode out;
    std::vector<SatLit> lits = st.ledger.flattenReasons(a);
    auto bl = st.ledger.flattenReasons(b);
    lits.insert(lits.end(), bl.begin(), bl.end());
    std::sort(lits.begin(), lits.end(), [](SatLit x, SatLit y) {
        if (x.var != y.var) return x.var < y.var;
        return x.sign < y.sign;
    });
    lits.erase(std::unique(lits.begin(), lits.end(), [](SatLit x, SatLit y) {
        return x.var == y.var && x.sign == y.sign;
    }), lits.end());
    out.baseLiterals = std::move(lits);
    return out;
}

}  // namespace

bool BoundChainComposer::run(PresolveState& st) {
    bool made = false;
    const size_t origN = st.atoms.size();  // don't process freshly-added atoms here

    for (size_t ai = 0; ai < origN; ++ai) {
        if (!st.atoms[ai].live) continue;
        Relation ra = st.atoms[ai].rel;
        if (ra != Relation::Lt && ra != Relation::Leq) continue;
        RationalPolynomial polyA = st.atoms[ai].poly;
        ReasonNode reasonsA = st.atoms[ai].reasons;

        for (size_t bi = 0; bi < origN; ++bi) {
            if (bi == ai || !st.atoms[bi].live) continue;
            Relation rb = st.atoms[bi].rel;
            if (rb != Relation::Lt && rb != Relation::Leq) continue;
            RationalPolynomial polyB = st.atoms[bi].poly;
            ReasonNode reasonsB = st.atoms[bi].reasons;

            for (VarId v : polyA.variables()) {
                if (polyA.degree(v) != 1 || polyB.degree(v) != 1) continue;
                mpq_class cA = linearCoeff(polyA, v);
                mpq_class cB = linearCoeff(polyB, v);
                if (!(cA < 0) || !(cB > 0)) continue;  // A lower-bounds v, B upper-bounds v

                RationalPolynomial pa = polyA; pa *= (mpq_class(1) / abs(cA));
                RationalPolynomial pb = polyB; pb *= (mpq_class(1) / abs(cB));
                RationalPolynomial combo = pa + pb;
                combo.normalize();
                if (combo.contains(v)) continue;                 // v failed to cancel
                if (combo.variables().size() > 1) continue;       // keep univariate/constant

                Relation rr = (ra == Relation::Lt || rb == Relation::Lt) ? Relation::Lt : Relation::Leq;
                ReasonNode rn = unionReasons(st, reasonsA, reasonsB);

                if (combo.isConstant()) {
                    if (!relationHoldsForConstant(combo.constantValue(), rr)) {
                        st.hasConflict = true;
                        st.conflict.clause = rn.baseLiterals;
                        return true;
                    }
                    // Tight bound pair: pa = -pb with both bounds non-strict ⇒
                    // pb = 0, i.e. the two bounds force an equality (e.g.
                    // x ≥ c ∧ x ≤ c ⇒ x = c). Emit it so substitution can
                    // eliminate the variable everywhere — including inside
                    // nonlinear terms — which e.g. collapses (x1-x2)²+(y1-y2)² ≥ 1
                    // to a constant contradiction once every center is pinned.
                    if (combo.isZero() && rr == Relation::Leq) {
                        RationalPolynomial eqPoly = pb;
                        eqPoly.normalize();
                        if (!eqPoly.isZero()) {
                            bool dupEq = false;
                            for (const auto& E : st.atoms) {
                                if (E.live && E.rel == Relation::Eq && polyEqual(E.poly, eqPoly)) { dupEq = true; break; }
                            }
                            if (!dupEq) {
                                PresolveAtom na;
                                na.poly = eqPoly;
                                na.rel = Relation::Eq;
                                na.reasons = rn;
                                na.live = true;
                                st.atoms.push_back(std::move(na));
                                made = true;
                            }
                        }
                    }
                    continue;  // tautological constant (equality may have been emitted)
                }

                // Deduplicate against existing atoms.
                bool dup = false;
                for (const auto& E : st.atoms) {
                    if (E.live && E.rel == rr && polyEqual(E.poly, combo)) { dup = true; break; }
                }
                if (dup) continue;

                PresolveAtom na;
                na.poly = combo;
                na.rel = rr;
                na.reasons = rn;
                na.live = true;
                st.atoms.push_back(std::move(na));
                made = true;
            }
        }
    }
    return made;
}

} // namespace xolver
