#include "search/presolve/IntLinearEqualityCoreHNF.h"
#include "search/linear/IntegerLinearSystem.h"

#include <map>
#include <set>
#include <cstdlib>

namespace xolver {

namespace {

// Extract a linear form Σ coeff_v·v + cst from p.  Returns false if any
// monomial has total degree ≥ 2.
bool extractLinear(const RationalPolynomial& p,
                   std::map<VarId, mpq_class>& coeffs, mpq_class& cst) {
    coeffs.clear();
    cst = 0;
    for (const auto& [key, c] : p.terms()) {
        if (key.empty()) { cst = c; continue; }
        if (key.size() != 1 || key[0].second != 1) return false;  // nonlinear
        coeffs[key[0].first] = c;
    }
    return true;
}

mpz_class lcm2(const mpz_class& a, const mpz_class& b) {
    if (a == 0 || b == 0) return (a == 0) ? abs(b) : abs(a);
    mpz_class g;
    mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return abs(a / g * b);
}

}  // namespace

bool IntLinearEqualityCoreHNF::run(PresolveState& st) {
    if (!st.integerDomain) return false;

    // Collect live linear equality atoms with at least one variable.
    struct Eq { std::map<VarId, mpq_class> coeffs; mpq_class cst; size_t atomIdx; };
    std::vector<Eq> eqs;
    std::set<VarId> varset;
    // Exact duplicate equalities do not change the lattice. Retain the first
    // occurrence's valid reason; different constants remain distinct rows.
    std::set<std::pair<std::map<VarId, mpq_class>, mpq_class>> seenEq;
    for (size_t i = 0; i < st.atoms.size(); ++i) {
        const auto& A = st.atoms[i];
        if (!A.live || A.rel != Relation::Eq) continue;
        std::map<VarId, mpq_class> coeffs;
        mpq_class cst;
        if (!extractLinear(A.poly, coeffs, cst)) continue;
        if (coeffs.empty()) continue;  // pure constant — handled elsewhere
        if (!seenEq.insert({coeffs, cst}).second) continue;
        for (const auto& [v, c] : coeffs) { (void)c; varset.insert(v); }
        eqs.push_back({std::move(coeffs), cst, i});
    }
    if (eqs.empty()) return false;

    std::vector<VarId> cols(varset.begin(), varset.end());
    std::map<VarId, int> colIdx;
    for (int j = 0; j < static_cast<int>(cols.size()); ++j) colIdx[cols[j]] = j;
    const int n = static_cast<int>(cols.size());
    const int m = static_cast<int>(eqs.size());

    // Build the integer system A·x = b (clear denominators per row).
    std::vector<IntegerLinearEquation> equations(m);
    for (int i = 0; i < m; ++i) {
        mpz_class den = 1;
        for (const auto& [v, c] : eqs[i].coeffs) { (void)v; den = lcm2(den, c.get_den()); }
        den = lcm2(den, eqs[i].cst.get_den());
        for (const auto& [v, c] : eqs[i].coeffs) {
            mpq_class scaled = c * den;            // integer
            equations[i].coefficients.emplace_back(colIdx[v], scaled.get_num());
        }
        mpq_class rhs = (-eqs[i].cst) * den;       // Σ c·x = -cst
        equations[i].rhs = rhs.get_num();
    }

    const auto lattice = solveIntegerLinearSystem(cols.size(), equations);

    // Combined reasons: the flattened base literals of every equality used.
    ReasonNode reasons;
    {
        std::set<std::pair<uint32_t, bool>> seen;
        for (const auto& e : eqs) {
            auto lits = st.ledger.flattenReasons(st.atoms[e.atomIdx].reasons);
            for (const auto& l : lits)
                if (seen.insert({l.var, l.sign}).second) reasons.baseLiterals.push_back(l);
        }
    }

    if (!lattice.consistent) {
        // Each supporting row belongs to a checked inconsistent component.
        // Expand its original premise rather than unrelated equalities.
        st.hasConflict = true;
        std::set<std::pair<uint32_t, bool>> seen;
        for (const size_t row : lattice.conflictRows) {
            const auto lits = st.ledger.flattenReasons(st.atoms[eqs[row].atomIdx].reasons);
            for (const auto& literal : lits)
                if (seen.insert({literal.var, literal.sign}).second)
                    st.conflict.clause.push_back(literal);
        }
        if (st.conflict.clause.empty()) st.conflict.clause = reasons.baseLiterals;
        return true;
    }

    // Per variable: fixed (kernel row all zero) → value; else gcd>1 → congruence.
    bool made = false;
    for (int k = 0; k < n; ++k) {
        VarId var = cols[k];
        if (st.substMap.count(var)) continue;
        const auto& g = lattice.coordinatePeriods[k];
        const auto& value = lattice.particular[k];
        if (g == 0) {
            made |= registerSubstitution(st, var,
                                 RationalPolynomial::fromConstant(mpq_class(value)), reasons);
            if (st.hasConflict) return true;
        } else if (g > 1) {
            mpz_class res = ((value % g) + g) % g;
            const auto previous = st.congruences.find(var);
            if (previous == st.congruences.end() || previous->second.modulus != g ||
                previous->second.residue != res) {
                st.congruences[var] = PresolveState::CongruenceVal{g, res, reasons};
                made = true;
            }
        }
    }
    return made;
}

} // namespace xolver
