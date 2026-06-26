#include "theory/arith/kernel/presolve/AffineSubstitution.h"

namespace xolver {

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
        if (st.substMap.count(chosen)) continue;  // already eliminated

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
        RationalPolynomial value =
            st.atoms[ai].poly - RationalPolynomial::fromVar(chosen, 1, chosenCoeff);
        value.normalize();
        value *= (mpq_class(-1) / chosenCoeff);
        value.normalize();

        ReasonNode reasons = st.atoms[ai].reasons;
        st.atoms[ai].live = false;  // equality consumed
        registerSubstitution(st, chosen, value, reasons);
        made = true;
        if (st.hasConflict) return true;
    }

    return made;
}

} // namespace xolver
