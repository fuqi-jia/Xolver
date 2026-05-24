#include "theory/arith/presolve/AffineSubstitution.h"

namespace nlcolver {

bool AffineSubstitution::run(PresolveState& st) {
    bool made = false;

    for (size_t ai = 0; ai < st.atoms.size(); ++ai) {
        if (!st.atoms[ai].live) continue;
        if (st.atoms[ai].rel != Relation::Eq) continue;
        if (totalDegree(st.atoms[ai].poly) > 1) continue;  // affine only

        // Pick a variable to eliminate: a degree-1 monomial with a usable coeff.
        VarId chosen = NullVar;
        mpq_class chosenCoeff;
        for (const auto& [key, coeff] : st.atoms[ai].poly.terms()) {
            if (key.size() != 1 || key[0].second != 1) continue;  // single var, exp 1
            if (st.integerDomain) {
                if (coeff == 1 || coeff == -1) { chosen = key[0].first; chosenCoeff = coeff; break; }
            } else {
                if (coeff != 0) { chosen = key[0].first; chosenCoeff = coeff; break; }
            }
        }
        if (chosen == NullVar) continue;

        // Int discipline: every coefficient must be integral so the affine RHS
        // is integer-valued whenever the other Int variables are integers.
        if (st.integerDomain) {
            bool allInt = true;
            for (const auto& [key, coeff] : st.atoms[ai].poly.terms()) {
                (void)key;
                if (coeff.get_den() != 1) { allInt = false; break; }
            }
            if (!allInt) continue;
        }

        // value = -(poly - chosenCoeff*chosen) / chosenCoeff
        RationalPolynomial value = st.atoms[ai].poly - RationalPolynomial::fromVar(chosen, 1, chosenCoeff);
        value.normalize();
        value *= (mpq_class(-1) / chosenCoeff);
        value.normalize();

        // Reduce by existing substitutions so value is over non-eliminated vars.
        for (const auto& [ev, entry] : st.substMap) {
            if (value.contains(ev)) value = substituteVar(value, ev, entry.value);
        }
        value.normalize();

        // Record the substitution fact.
        DerivedFact f;
        f.payload = DerivedSubst{chosen, value};
        f.reasons = st.atoms[ai].reasons;
        size_t fidx = st.ledger.append(f);
        st.substMap[chosen] = PresolveState::SubstEntry{value, fidx};

        // Apply to every other live atom.
        for (size_t bi = 0; bi < st.atoms.size(); ++bi) {
            if (bi == ai) continue;
            PresolveAtom& B = st.atoms[bi];
            if (!B.live || !B.poly.contains(chosen)) continue;
            B.poly = substituteVar(B.poly, chosen, value);
            B.poly.normalize();
            B.reasons.upstreamIndices.push_back(fidx);
            if (B.poly.isConstant()) {
                mpq_class cval = B.poly.constantValue();
                if (!relationHoldsForConstant(cval, B.rel)) {
                    st.hasConflict = true;
                    st.conflict.clause = st.ledger.flattenReasons(B.reasons);
                    return true;
                }
                B.live = false;  // satisfied
            }
        }

        // Compose backward: eliminate `chosen` from earlier substitution values.
        for (auto& [ev, entry] : st.substMap) {
            if (ev == chosen) continue;
            if (entry.value.contains(chosen)) {
                entry.value = substituteVar(entry.value, chosen, value);
                entry.value.normalize();
            }
        }

        st.atoms[ai].live = false;  // equality consumed
        made = true;
    }

    return made;
}

} // namespace nlcolver
