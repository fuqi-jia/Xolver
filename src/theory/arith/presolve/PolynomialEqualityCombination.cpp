#include "theory/arith/presolve/PolynomialEqualityCombination.h"

#include <algorithm>
#include <map>
#include <set>
#include <vector>

namespace zolver {

namespace {

int keyDegree(const MonomialKey& key) {
    int d = 0;
    for (const auto& [v, e] : key) { (void)v; d += e; }
    return d;
}

// Basis of the null space {x ∈ Q^cols : M·x = 0} via RREF.
std::vector<std::vector<mpq_class>> nullSpace(std::vector<std::vector<mpq_class>> M,
                                              int rows, int cols) {
    std::vector<int> where(cols, -1);  // where[col] = its pivot row, else -1
    int r = 0;
    for (int c = 0; c < cols && r < rows; ++c) {
        int sel = -1;
        for (int i = r; i < rows; ++i) if (M[i][c] != 0) { sel = i; break; }
        if (sel < 0) continue;
        std::swap(M[sel], M[r]);
        mpq_class pv = M[r][c];
        for (int j = 0; j < cols; ++j) M[r][j] /= pv;
        for (int i = 0; i < rows; ++i) {
            if (i == r || M[i][c] == 0) continue;
            mpq_class f = M[i][c];
            for (int j = 0; j < cols; ++j) M[i][j] -= f * M[r][j];
        }
        where[c] = r;
        ++r;
    }
    std::vector<std::vector<mpq_class>> basis;
    for (int fc = 0; fc < cols; ++fc) {
        if (where[fc] != -1) continue;            // pivot column, not free
        std::vector<mpq_class> v(cols, mpq_class(0));
        v[fc] = 1;
        for (int c = 0; c < cols; ++c)
            if (where[c] != -1) v[c] = -M[where[c]][fc];
        basis.push_back(std::move(v));
    }
    return basis;
}

}  // namespace

bool PolynomialEqualityCombination::run(PresolveState& st) {
    std::vector<size_t> eqIdx;
    for (size_t i = 0; i < st.atoms.size(); ++i)
        if (st.atoms[i].live && st.atoms[i].rel == Relation::Eq)
            eqIdx.push_back(i);
    if (eqIdx.size() < 2) return false;

    // Collect the degree-≥2 monomials across the selected equalities.
    std::map<MonomialKey, int> monoIndex;
    std::vector<MonomialKey> monos;
    for (size_t idx : eqIdx) {
        for (const auto& [key, coeff] : st.atoms[idx].poly.terms()) {
            (void)coeff;
            if (keyDegree(key) >= 2 && !monoIndex.count(key)) {
                monoIndex[key] = static_cast<int>(monos.size());
                monos.push_back(key);
            }
        }
    }
    if (monos.empty()) return false;  // all linear → handled by Cap. 5 / Cap. 1

    const int k = static_cast<int>(eqIdx.size());
    const int c = static_cast<int>(monos.size());

    // M = E_high^T (c × k); its null space gives left-null vectors λ ∈ Q^k.
    std::vector<std::vector<mpq_class>> M(c, std::vector<mpq_class>(k, mpq_class(0)));
    for (int pi = 0; pi < k; ++pi) {
        for (const auto& [key, coeff] : st.atoms[eqIdx[pi]].poly.terms()) {
            auto it = monoIndex.find(key);
            if (it != monoIndex.end()) M[it->second][pi] = coeff;
        }
    }
    auto basis = nullSpace(M, c, k);

    bool made = false;
    for (const auto& lambda : basis) {
        RationalPolynomial combo;
        ReasonNode rn;
        std::set<std::pair<uint32_t, bool>> seen;
        for (int pi = 0; pi < k; ++pi) {
            if (lambda[pi] == 0) continue;
            RationalPolynomial t = st.atoms[eqIdx[pi]].poly;
            t *= lambda[pi];
            combo += t;
            for (const auto& l : st.ledger.flattenReasons(st.atoms[eqIdx[pi]].reasons))
                if (seen.insert({l.var, l.sign}).second) rn.baseLiterals.push_back(l);
        }
        combo.normalize();
        if (combo.isZero()) continue;

        if (combo.isConstant()) {
            // Σ λᵢ pᵢ = nonzero constant, yet each pᵢ = 0 ⇒ contradiction.
            st.hasConflict = true;
            st.conflict.clause = rn.baseLiterals;
            return true;
        }
        if (totalDegree(combo) > 1) continue;  // safety; should be ≤ 1 by construction

        // Canonicalize sign: make the first term's coefficient positive.
        if (!combo.terms().empty() && combo.terms().begin()->second < 0)
            combo = -combo;

        // Deduplicate against existing equalities.
        bool dup = false;
        for (const auto& E : st.atoms) {
            if (E.live && E.rel == Relation::Eq && E.poly.terms() == combo.terms()) { dup = true; break; }
        }
        if (dup) continue;

        PresolveAtom na;
        na.poly = combo;
        na.rel = Relation::Eq;
        na.reasons = rn;
        na.live = true;
        st.atoms.push_back(std::move(na));
        made = true;
    }
    return made;
}

} // namespace zolver
