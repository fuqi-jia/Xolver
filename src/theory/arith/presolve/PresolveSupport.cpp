#include "theory/arith/presolve/Presolve.h"

#include <algorithm>

namespace zolver {

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

namespace {
bool endpointEqual(const BoundEndpoint& a, const BoundEndpoint& b) {
    if (a.kind != b.kind) return false;
    if (a.kind == BoundEndpoint::Kind::Rational) return a.rationalValue == b.rationalValue;
    return true;  // ±Inf same kind; algebraic treated as equal (approximate)
}
bool sameSet(const IntervalSet& a, const IntervalSet& b) {
    if (a.intervals.size() != b.intervals.size()) return false;
    for (size_t i = 0; i < a.intervals.size(); ++i) {
        const auto& x = a.intervals[i];
        const auto& y = b.intervals[i];
        if (x.lowerOpen != y.lowerOpen || x.upperOpen != y.upperOpen) return false;
        if (!endpointEqual(x.lower, y.lower) || !endpointEqual(x.upper, y.upper)) return false;
    }
    return true;
}
}  // namespace

bool addBound(PresolveState& st, VarId v, const IntervalSet& incoming,
              const ReasonNode& reasons) {
    auto dom = st.integerDomain ? IntervalSet::Domain::Int : IntervalSet::Domain::Real;
    IntervalSet cur = st.bounds.count(v) ? st.bounds[v].set : IntervalSet::universe(dom);
    IntervalSet next = incoming.intersect(cur);

    // Combine reasons: flattened incoming literals + existing bound's literals.
    ReasonNode combined;
    {
        std::vector<SatLit> lits = st.ledger.flattenReasons(reasons);
        if (st.bounds.count(v)) {
            const auto& prev = st.bounds[v].reasons.baseLiterals;
            lits.insert(lits.end(), prev.begin(), prev.end());
        }
        std::sort(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
            if (a.var != b.var) return a.var < b.var;
            return a.sign < b.sign;
        });
        lits.erase(std::unique(lits.begin(), lits.end(), [](SatLit a, SatLit b) {
            return a.var == b.var && a.sign == b.sign;
        }), lits.end());
        combined.baseLiterals = std::move(lits);
    }

    bool empty = st.integerDomain ? !next.hasIntegerPoint() : next.isEmpty();
    if (empty) {
        st.hasConflict = true;
        st.conflict.clause = combined.baseLiterals;
        return true;
    }
    if (!st.bounds.count(v) || !sameSet(next, st.bounds[v].set)) {
        st.bounds[v] = BoundVal{next, combined};
        return true;
    }
    return false;
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

} // namespace zolver
