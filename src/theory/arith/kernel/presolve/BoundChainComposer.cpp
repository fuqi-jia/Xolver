#include "theory/arith/kernel/presolve/BoundChainComposer.h"
#include "util/EnvParam.h"

#include <algorithm>
#include <cstdlib>
#include <iostream>

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

    // Budget: this is a heuristic Fourier-Motzkin bound-chain pre-pass. On
    // many-variable rational-coefficient systems (e.g. Pine loop-invariant
    // checks) it generates a combinatorial blowup of derived 1-var atoms, and
    // the O(atoms) dedup scan per push makes one run() quadratic in the atoms
    // generated — a 15s+ hang where z3 decides in ~0s. Cap the input size and
    // total work so composition can never dominate solving. SOUND: a skipped
    // composition only forgoes a derived fact (and any conflict it would expose
    // is still found by the main solver); we never emit a wrong fact.
    static const size_t kMaxAtoms =
        static_cast<size_t>(std::max(1, env::paramInt("XOLVER_NRA_BOUNDCHAIN_MAX_ATOMS", 2000)));
    static const long kMaxWork =
        static_cast<long>(std::max(1, env::paramInt("XOLVER_NRA_BOUNDCHAIN_MAX_WORK", 1500000)));
    static const bool diag = xolver::env::diag("XOLVER_PRESOLVE_DIAG");
    if (origN > kMaxAtoms) {
        if (diag) std::cerr << "[BOUNDCHAIN] skip: origN=" << origN
                            << " > cap=" << kMaxAtoms << "\n";
        return false;
    }
    long work = 0;

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
                if (work > kMaxWork) {
                    if (diag) std::cerr << "[BOUNDCHAIN] work budget hit: origN=" << origN
                                        << " work=" << work << " made=" << made << "\n";
                    return made;
                }
                ++work;
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
                                ++work;
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
                    ++work;
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
