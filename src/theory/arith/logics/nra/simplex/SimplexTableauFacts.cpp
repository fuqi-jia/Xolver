#include "theory/arith/logics/nra/simplex/SimplexTableauFacts.h"
#include "theory/arith/logics/lra/GeneralSimplex.h"
#include "theory/arith/logics/lra/DeltaRational.h"
#include "theory/arith/logics/lra/SparseTableau.h"
#include <string>
#include <unordered_map>

namespace xolver {

std::pair<std::optional<mpq_class>, std::optional<mpq_class>>
deriveBasicInterval(const mpq_class& rhs, const std::vector<RowTermBound>& terms) {
    std::optional<mpq_class> lo = rhs, hi = rhs;
    for (const auto& t : terms) {
        if (t.coeff > 0) {            // lower uses col.lo, upper uses col.hi
            if (lo) { if (t.lo) *lo += t.coeff * *t.lo; else lo.reset(); }
            if (hi) { if (t.hi) *hi += t.coeff * *t.hi; else hi.reset(); }
        } else if (t.coeff < 0) {     // lower uses col.hi, upper uses col.lo
            if (lo) { if (t.hi) *lo += t.coeff * *t.hi; else lo.reset(); }
            if (hi) { if (t.lo) *hi += t.coeff * *t.lo; else hi.reset(); }
        }
    }
    return { lo, hi };
}

SimplexTableauFacts computeSimplexTableauFacts(
    const PolynomialKernel& kernel,
    const std::vector<LinearAtom>& linear) {
    SimplexTableauFacts F;
    GeneralSimplex gs;

    std::unordered_map<VarId,int> idx;    // kernel VarId -> simplex index
    std::unordered_map<int,VarId> orig;   // simplex index -> kernel VarId (originals only)
    auto idxOf = [&](VarId v)->int {
        auto it=idx.find(v); if (it!=idx.end()) return it->second;
        int i = gs.addVar(std::string(kernel.varName(v)));
        idx[v]=i; orig[i]=v; return i;
    };
    auto flip = [](Relation r)->Relation {
        switch(r){ case Relation::Geq:return Relation::Leq; case Relation::Leq:return Relation::Geq;
                   case Relation::Gt:return Relation::Lt;   case Relation::Lt:return Relation::Gt;  default:return r; }
    };

    for (const auto& la : linear) {
        if (la.coeffs.empty()) {                   // constant atom: constant rel 0
            int s = (la.constant > 0) ? 1 : (la.constant < 0) ? -1 : 0;
            bool ok = true;
            switch (la.rel) {
                case Relation::Eq:  ok = (s == 0); break;
                case Relation::Neq: ok = (s != 0); break;
                case Relation::Lt:  ok = (s <  0); break;
                case Relation::Leq: ok = (s <= 0); break;
                case Relation::Gt:  ok = (s >  0); break;
                case Relation::Geq: ok = (s >= 0); break;
            }
            if (!ok) { F.unsat_ = true; return F; }   // false constant => linear subset infeasible
            continue;                                 // trivially-true constant: nothing to assert
        }
        if (la.rel == Relation::Neq) continue;     // non-convex (non-constant): skip
        if (la.coeffs.size() == 1) {               // a*x + c rel 0 -> direct bound on x
            VarId v = la.coeffs[0].first;
            const mpq_class& a = la.coeffs[0].second;
            if (a == 0) continue;
            mpq_class b = -la.constant / a;
            Relation rel = (a < 0) ? flip(la.rel) : la.rel;
            int xi = idxOf(v);
            switch (rel) {
                case Relation::Eq:  gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason));
                                    gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Geq: gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Gt:  gs.assertLower(xi, BoundInfo(BoundValue(DeltaRational(b, mpq_class(1))), la.reason)); break;
                case Relation::Leq: gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b)), la.reason)); break;
                case Relation::Lt:  gs.assertUpper(xi, BoundInfo(BoundValue(DeltaRational(b, mpq_class(-1))), la.reason)); break;
                default: break;
            }
        } else {                                   // multi-var -> aux row s = Σ a_j x_j ; bound s rel -const
            std::vector<std::pair<int,mpq_class>> terms;
            for (auto&[v,c] : la.coeffs) terms.push_back({ idxOf(v), c });
            int s = gs.addConstraint(terms, mpq_class(0));
            if (s < 0) continue;
            mpq_class rhs = -la.constant;
            switch (la.rel) {
                case Relation::Eq:  gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason));
                                    gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Geq: gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Gt:  gs.assertLower(s, BoundInfo(BoundValue(DeltaRational(rhs, mpq_class(1))), la.reason)); break;
                case Relation::Leq: gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs)), la.reason)); break;
                case Relation::Lt:  gs.assertUpper(s, BoundInfo(BoundValue(DeltaRational(rhs, mpq_class(-1))), la.reason)); break;
                default: break;
            }
        }
    }

    if (gs.check() != GeneralSimplex::Result::Sat) {
        F.unsat_ = true;            // facts-only: no conflict, no verdict
        return F;
    }

    auto storedLo = [&](int i)->std::optional<mpq_class>{
        auto vs=gs.varState(i); return vs.lower.bound.isFinite()?std::optional<mpq_class>(vs.lower.bound.value.a):std::nullopt; };
    auto storedHi = [&](int i)->std::optional<mpq_class>{
        auto vs=gs.varState(i); return vs.upper.bound.isFinite()?std::optional<mpq_class>(vs.upper.bound.value.a):std::nullopt; };

    // 1+2. stored bounds and one-shot derived intervals per ORIGINAL variable.
    for (auto& [v, i] : idx) {
        if (auto lo = storedLo(i)) F.tightenLower(v, *lo);
        if (auto hi = storedHi(i)) F.tightenUpper(v, *hi);
        bool basic = gs.isBasic(i);
        F.m_[v].basic = basic;
        if (basic) {
            const SparseRow& row = gs.tableau().row(gs.basicRowOfVar(i));
            std::vector<RowTermBound> terms;
            terms.reserve(row.entries.size());
            for (const auto& e : row.entries)
                terms.push_back(RowTermBound{ e.coeff, storedLo(e.col), storedHi(e.col) });
            auto iv = deriveBasicInterval(row.rhs, terms);
            if (iv.first)  F.tightenLower(v, *iv.first);
            if (iv.second) F.tightenUpper(v, *iv.second);
        }
    }

    // 3. row + tight-row participation (zero-slack: basic var currently at a bound).
    for (int r = 0; r < gs.tableau().numRows(); ++r) {
        const SparseRow& row = gs.tableau().row(r);
        int bv = row.basicVar;
        if (bv < 0) continue;
        auto vs = gs.varState(bv);
        DeltaRational val = gs.value(bv);
        bool tight = (vs.lower.bound.isFinite() && val == vs.lower.bound.value) ||
                     (vs.upper.bound.isFinite() && val == vs.upper.bound.value);
        auto bump = [&](int simIdx){ auto it=orig.find(simIdx); if(it!=orig.end()){ ++F.rowPart_[it->second]; if(tight) ++F.tight_[it->second]; } };
        bump(bv);
        for (const auto& e : row.entries) bump(e.col);
    }
    return F;
}

} // namespace xolver
