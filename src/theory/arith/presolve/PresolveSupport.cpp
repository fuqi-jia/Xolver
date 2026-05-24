#include "theory/arith/presolve/Presolve.h"

namespace nlcolver {

RationalPolynomial substituteVar(const RationalPolynomial& p, VarId v,
                                 const RationalPolynomial& value) {
    RationalPolynomial result;
    for (const auto& [key, coeff] : p.terms()) {
        int ev = 0;
        MonomialKey rest;
        for (const auto& [var, exp] : key) {
            if (var == v) ev = exp;
            else rest.push_back({var, exp});
        }
        // term = coeff * (rest monomial) * value^ev
        RationalPolynomial term = RationalPolynomial::fromConstant(coeff);
        if (!rest.empty()) {
            RationalPolynomial restPoly;
            restPoly.addTerm(rest, mpq_class(1));
            term = term * restPoly;
        }
        if (ev > 0) {
            term = term * value.pow(static_cast<uint32_t>(ev));
        }
        result += term;
    }
    result.normalize();
    return result;
}

int totalDegree(const RationalPolynomial& p) {
    int maxd = 0;
    for (const auto& [key, coeff] : p.terms()) {
        (void)coeff;
        int d = 0;
        for (const auto& [var, exp] : key) { (void)var; d += exp; }
        if (d > maxd) maxd = d;
    }
    return maxd;
}

bool registerSubstitution(PresolveState& st, VarId v, RationalPolynomial value,
                          const ReasonNode& reasons) {
    value.normalize();
    // Reduce by existing substitutions so `value` is over non-eliminated vars.
    for (const auto& [ev, entry] : st.substMap) {
        if (value.contains(ev)) value = substituteVar(value, ev, entry.value);
    }
    value.normalize();

    DerivedFact f;
    if (value.isConstant()) f.payload = DerivedFixedValue{v, value.constantValue()};
    else                    f.payload = DerivedSubst{v, value};
    f.reasons = reasons;
    size_t fidx = st.ledger.append(f);

    st.substMap[v] = PresolveState::SubstEntry{value, fidx};
    if (value.isConstant()) st.fixedValues[v] = FixedVal{value.constantValue(), reasons};

    // Apply to every live atom containing v.
    for (auto& B : st.atoms) {
        if (!B.live || !B.poly.contains(v)) continue;
        B.poly = substituteVar(B.poly, v, value);
        B.poly.normalize();
        B.reasons.upstreamIndices.push_back(fidx);
        if (B.poly.isConstant()) {
            if (!relationHoldsForConstant(B.poly.constantValue(), B.rel)) {
                st.hasConflict = true;
                st.conflict.clause = st.ledger.flattenReasons(B.reasons);
                return true;
            }
            B.live = false;  // satisfied
        }
    }

    // Compose backward: eliminate v from earlier substitution values.
    for (auto& [ev, entry] : st.substMap) {
        if (ev == v) continue;
        if (entry.value.contains(v)) {
            entry.value = substituteVar(entry.value, v, value);
            entry.value.normalize();
        }
    }
    return true;
}

bool relationHoldsForConstant(const mpq_class& c, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return c == 0;
        case Relation::Neq: return c != 0;
        case Relation::Lt:  return c < 0;
        case Relation::Leq: return c <= 0;
        case Relation::Gt:  return c > 0;
        case Relation::Geq: return c >= 0;
    }
    return false;
}

} // namespace nlcolver
