#include "theory/arith/presolve/PolynomialDefSubstitution.h"

namespace nlcolver {

namespace {

// True iff v occurs in p only as the standalone linear monomial {(v,1)}
// (no higher power, no cross term).  Returns its coefficient in `coeff`.
bool isCleanLinearVar(const RationalPolynomial& p, VarId v, mpq_class& coeff) {
    bool found = false;
    coeff = 0;
    for (const auto& [key, c] : p.terms()) {
        bool hasV = false;
        for (const auto& [var, exp] : key) {
            if (var == v) {
                if (exp != 1 || key.size() != 1) return false;  // higher power or cross term
                hasV = true;
            }
        }
        if (hasV) { coeff = c; found = true; }
    }
    return found;
}

}  // namespace

bool PolynomialDefSubstitution::run(PresolveState& st) {
    bool made = false;
    for (size_t ai = 0; ai < st.atoms.size(); ++ai) {
        if (!st.atoms[ai].live || st.atoms[ai].rel != Relation::Eq) continue;

        VarId chosen = NullVar;
        mpq_class chosenCoeff;
        for (VarId v : st.atoms[ai].poly.variables()) {
            if (st.substMap.count(v)) continue;
            mpq_class c;
            if (!isCleanLinearVar(st.atoms[ai].poly, v, c)) continue;
            if (st.integerDomain) {
                if (c == 1 || c == -1) { chosen = v; chosenCoeff = c; break; }
            } else {
                if (c != 0) { chosen = v; chosenCoeff = c; break; }
            }
        }
        if (chosen == NullVar) continue;

        // Int discipline: integer coefficients (so v is integer-valued).
        if (st.integerDomain) {
            bool allInt = true;
            for (const auto& [key, c] : st.atoms[ai].poly.terms()) {
                (void)key;
                if (c.get_den() != 1) { allInt = false; break; }
            }
            if (!allInt) continue;
        }

        // value = -(poly - chosenCoeff*v) / chosenCoeff  (polynomial in other vars)
        RationalPolynomial value =
            st.atoms[ai].poly - RationalPolynomial::fromVar(chosen, 1, chosenCoeff);
        value.normalize();
        value *= (mpq_class(-1) / chosenCoeff);
        value.normalize();
        if (value.contains(chosen)) continue;                  // defensive
        if (value.terms().size() > kMaxTermBudget) continue;    // budget

        ReasonNode reasons = st.atoms[ai].reasons;
        st.atoms[ai].live = false;
        registerSubstitution(st, chosen, value, reasons);
        made = true;
        if (st.hasConflict) return true;
    }
    return made;
}

} // namespace nlcolver
