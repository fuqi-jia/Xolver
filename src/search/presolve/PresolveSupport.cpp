#include "search/presolve/Presolve.h"

#include <algorithm>
#include <limits>
#include <numeric>

namespace xolver {

namespace {
bool expired(const PresolveState& st) {
    return st.deadline != std::chrono::steady_clock::time_point::max() &&
           std::chrono::steady_clock::now() >= st.deadline;
}

// Number of multisets of `power` factors chosen from `terms` monomials.
// This bounds the expanded term count even when different products coincide.
// Saturate before multiplication; no polynomial expansion is needed to decide.
size_t powerTermBound(size_t terms, unsigned power, size_t limit) {
    if (!power) return 1;
    if (!terms) return 0;
    if (terms == 1) return 1;
    if (terms > std::numeric_limits<size_t>::max() - (power - 1)) return limit + 1;
    const size_t n = terms + power - 1, k = std::min<size_t>(power, terms - 1);
    size_t count = 1;
    for (size_t i = 1; i <= k; ++i) {
        size_t numerator = n - k + i, denominator = i;
        auto g = std::gcd(numerator, denominator);
        numerator /= g; denominator /= g;
        g = std::gcd(count, denominator);
        count /= g; denominator /= g;
        // A binomial recurrence is integral after exact cancellation.
        if (denominator != 1 || count > limit / numerator) return limit + 1;
        count *= numerator;
    }
    return count;
}

std::optional<RationalPolynomial> boundedSubstitute(
    const PresolveState& st, const RationalPolynomial& input, VarId variable,
    const RationalPolynomial& value) {
    if (expired(st)) return std::nullopt;
    if (!input.contains(variable)) return input;
    const size_t limit = std::max(PresolveState::kSubstitutionTermBudget, input.terms().size());
    size_t terms = 0;
    std::map<VarId, int> degrees;
    for (const auto& [key, coefficient] : value.terms()) {
        (void)coefficient;
        for (const auto& [v, degree] : key) degrees[v] = std::max(degrees[v], degree);
    }
    for (const auto& [key, coefficient] : input.terms()) {
        (void)coefficient;
        if (expired(st)) return std::nullopt;
        unsigned power = 0;
        for (const auto& [v, degree] : key)
            if (v == variable) power = static_cast<unsigned>(degree);
        const size_t bound = powerTermBound(value.terms().size(), power, limit);
        if (bound > limit - terms) return std::nullopt;
        terms += bound;
        // The polynomial representation uses signed int exponents. Reject an
        // unrepresentable composition before arithmetic can overflow.
        for (const auto& [v, degree] : degrees) {
            int rest = 0;
            for (const auto& [w, exponent] : key)
                if (v == w && w != variable) rest = exponent;
            if (uint64_t(power) * static_cast<unsigned>(degree) + rest >
                static_cast<uint64_t>(std::numeric_limits<int>::max()))
                return std::nullopt;
        }
    }
    auto result = input.substitute(variable, value);
    if (expired(st)) return std::nullopt;
    return result;
}

DerivedFact substitutionFact(VarId variable, const RationalPolynomial& value,
                             ReasonNode reasons) {
    DerivedFact fact;
    if (value.isConstant()) fact.payload = DerivedFixedValue{variable, value.constantValue()};
    else fact.payload = DerivedSubst{variable, value};
    fact.reasons = std::move(reasons);
    return fact;
}
} // namespace

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
    if (v == NullVar || st.substMap.count(v) || expired(st)) return false;
    value.normalize();
    if (value.terms().size() > PresolveState::kSubstitutionTermBudget) return false;
    // Reduce by existing substitutions so `value` is over non-eliminated vars.
    // iter-74: track `value.variables()` so the inner check is an O(log V) set
    // lookup on a refreshed snapshot instead of O(value terms × vars-per-term)
    // RationalPolynomial::contains scan.
    std::set<VarId> valueVars = value.variables();
    ReasonNode combined = reasons;
    for (const auto& [ev, entry] : st.substMap) {
        if (valueVars.count(ev)) {
            auto next = boundedSubstitute(st, value, ev, entry.value);
            if (!next) return false;
            value = std::move(*next);
            combined.upstreamIndices.push_back(entry.factIndex);
            valueVars = value.variables();
        }
    }
    value.normalize();
    if (value.contains(v)) return false;

    // Prepare every rewrite before committing any of them. In particular, a
    // declined expansion must not consume its defining equality or leave a
    // partly composed substitution map behind.
    std::vector<std::pair<size_t, RationalPolynomial>> atoms;
    for (size_t i = 0; i < st.atoms.size(); ++i) {
        const auto& atom = st.atoms[i];
        if (!atom.live || !atom.poly.contains(v)) continue;
        auto next = boundedSubstitute(st, atom.poly, v, value);
        if (!next) return false;
        atoms.emplace_back(i, std::move(*next));
    }
    std::vector<std::pair<VarId, RationalPolynomial>> previous;
    for (const auto& [ev, entry] : st.substMap) {
        if (entry.vars.count(v)) {
            auto next = boundedSubstitute(st, entry.value, v, value);
            if (!next) return false;
            previous.emplace_back(ev, std::move(*next));
        }
    }
    if (expired(st)) return false;

    const size_t fidx = st.ledger.append(substitutionFact(v, value, combined));
    st.substMap[v] = PresolveState::SubstEntry{value, fidx, value.variables()};
    if (value.isConstant()) st.fixedValues[v] = FixedVal{value.constantValue(), combined};
    for (auto& [ev, next] : previous) {
        auto& entry = st.substMap.at(ev);
        ReasonNode composed;
        composed.upstreamIndices = {entry.factIndex, fidx};
        entry.factIndex = st.ledger.append(substitutionFact(ev, next, composed));
        entry.value = std::move(next);
        entry.vars = entry.value.variables();
        if (entry.value.isConstant())
            st.fixedValues[ev] = FixedVal{entry.value.constantValue(), std::move(composed)};
    }
    for (auto& [index, next] : atoms) {
        auto& atom = st.atoms[index];
        atom.poly = std::move(next);
        atom.reasons.upstreamIndices.push_back(fidx);
        if (!atom.poly.isConstant()) continue;
        if (!relationHoldsForConstant(atom.poly.constantValue(), atom.rel)) {
            st.hasConflict = true;
            st.conflict.clause = st.ledger.flattenReasons(atom.reasons);
        } else atom.live = false;
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

} // namespace xolver
