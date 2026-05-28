#include "theory/arith/presolve/IntLinearEqualityCoreHNF.h"
#include "theory/arith/presolve/IntegerLinearAlgebra.h"

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
    // XOLVER_PRESOLVE_DEDUP_ROWS (default-OFF): skip an equality whose
    // (coeffs, cst) is byte-identical to one already collected. Such a row is
    // the SAME linear constraint (E ∧ E ≡ E), so its presence does not change
    // the solution set, the existence/feasibility test, or any SNF-derived
    // substitution/congruence — only the matrix row count. On EVM/SVCOMP-style
    // QF_ANIA inputs the live equality set is up to ~98% exact duplicates
    // (floppy2: 19847 rows → 415 unique), so SNF (super-linear in rows) is
    // computed on a massively redundant matrix. Deduping is solution-set exact;
    // we keep the FIRST occurrence's atomIdx as the reason representative (a
    // valid, possibly tighter, conflict justification). Same-coeffs/different-
    // cst rows have distinct keys → both kept → the SNF existence check still
    // detects the contradiction. Gate proves no-verdict-change OFF vs ON.
    const bool dedupRows = std::getenv("XOLVER_PRESOLVE_DEDUP_ROWS") != nullptr;
    std::set<std::pair<std::map<VarId, mpq_class>, mpq_class>> seenEq;
    for (size_t i = 0; i < st.atoms.size(); ++i) {
        const auto& A = st.atoms[i];
        if (!A.live || A.rel != Relation::Eq) continue;
        std::map<VarId, mpq_class> coeffs;
        mpq_class cst;
        if (!extractLinear(A.poly, coeffs, cst)) continue;
        if (coeffs.empty()) continue;  // pure constant — handled elsewhere
        if (dedupRows && !seenEq.insert({coeffs, cst}).second) continue;  // exact duplicate
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
    IntMatrix Amat(m, std::vector<mpz_class>(n, mpz_class(0)));
    std::vector<mpz_class> bvec(m, mpz_class(0));
    for (int i = 0; i < m; ++i) {
        mpz_class den = 1;
        for (const auto& [v, c] : eqs[i].coeffs) { (void)v; den = lcm2(den, c.get_den()); }
        den = lcm2(den, eqs[i].cst.get_den());
        for (const auto& [v, c] : eqs[i].coeffs) {
            mpq_class scaled = c * den;            // integer
            Amat[i][colIdx[v]] = scaled.get_num();
        }
        mpq_class rhs = (-eqs[i].cst) * den;       // Σ c·x = -cst
        bvec[i] = rhs.get_num();
    }

    SmithNormalForm snf = smithNormalForm(Amat);
    std::vector<mpz_class> bp = matVec(snf.U, bvec);  // b' = U·b

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

    const int diagN = std::min(snf.m, snf.n);

    // Existence: d_i | b'_i for nonzero diagonals; b'_i = 0 for zero rows.
    for (int i = 0; i < snf.m; ++i) {
        mpz_class d = (i < diagN) ? snf.D[i][i] : mpz_class(0);
        bool bad = (d != 0) ? (bp[i] % d != 0) : (bp[i] != 0);
        if (bad) {
            st.hasConflict = true;
            st.conflict.clause = reasons.baseLiterals;
            return true;
        }
    }

    // Particular solution y, free indices, x0 = V·y.
    std::vector<mpz_class> y(n, mpz_class(0));
    std::vector<bool> isFree(n, true);
    for (int i = 0; i < diagN; ++i) {
        if (snf.D[i][i] != 0) { y[i] = bp[i] / snf.D[i][i]; isFree[i] = false; }
    }
    std::vector<mpz_class> x0 = matVec(snf.V, y);
    std::vector<int> freeCols;
    for (int j = 0; j < n; ++j) if (isFree[j]) freeCols.push_back(j);

    // Per variable: fixed (kernel row all zero) → value; else gcd>1 → congruence.
    bool made = false;
    for (int k = 0; k < n; ++k) {
        VarId var = cols[k];
        if (st.substMap.count(var)) continue;
        bool allZero = true;
        mpz_class g = 0;
        for (int fj : freeCols) {
            const mpz_class& e = snf.V[k][fj];
            if (e != 0) {
                allZero = false;
                mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), e.get_mpz_t());
                g = abs(g);
            }
        }
        if (allZero) {
            registerSubstitution(st, var,
                                 RationalPolynomial::fromConstant(mpq_class(x0[k])), reasons);
            made = true;
            if (st.hasConflict) return true;
        } else if (g > 1) {
            mpz_class res = ((x0[k] % g) + g) % g;
            st.congruences[var] = PresolveState::CongruenceVal{g, res, reasons};
            made = true;
        }
    }
    return made;
}

} // namespace xolver
