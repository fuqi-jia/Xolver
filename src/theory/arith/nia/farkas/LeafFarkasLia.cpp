#include "theory/arith/nia/farkas/LeafFarkasLia.h"

#include "theory/arith/lia/InternalMilpEngine.h"
#include "theory/arith/poly/PolynomialKernel.h"

#include <cstdio>
#include <cstdlib>
#include <map>
#include <unordered_map>

namespace xolver {

namespace {

inline void ctDiag(const char* why) {
    if (const char* df = std::getenv("XOLVER_NIA_CT_DIAG")) if (*df)
        if (std::FILE* fp = std::fopen(df, "a")) { std::fprintf(fp, "[CT-BAIL] %s\n", why); std::fclose(fp); }
}

// A linear form over λ-variables:  Σ coeff·var + constant.
struct LF {
    std::map<VarId, mpq_class> c;
    mpq_class k = 0;
};

LF negate(const LF& a) {
    LF r;
    for (const auto& [v, co] : a.c) r.c[v] = -co;
    r.k = -a.k;
    return r;
}

// Parse `poly` (= 0 form) into  A(λ) + Σ_ct ct·S_ct(λ).  Returns false on any
// monomial that is not constant, c·λ, c·ct, or c·ct·λ (i.e. degree > 1 in λ,
// ct·ct, or λ·λ — not the Farkas leaf shape).
bool parse(PolynomialKernel& kernel, PolyId poly,
           const std::unordered_set<VarId>& ctVars,
           LF& A, std::map<VarId, LF>& ctTerms) {
    auto terms = kernel.terms(poly);
    if (!terms) return false;
    for (const auto& m : *terms) {
        mpq_class co(m.coefficient);
        VarId ct = NullVar, lam = NullVar;
        bool bad = false;
        for (const auto& [v, e] : m.powers) {
            if (e != 1) { bad = true; break; }
            if (ctVars.count(v)) { if (ct != NullVar) { bad = true; break; } ct = v; }
            else                 { if (lam != NullVar) { bad = true; break; } lam = v; }
        }
        if (bad) return false;
        if (ct == NullVar) {
            if (lam == NullVar) A.k += co; else A.c[lam] += co;
        } else {
            LF& S = ctTerms[ct];
            if (lam == NullVar) S.k += co; else S.c[lam] += co;
        }
    }
    return true;
}

// Discharge a pure-LIA system (list of (form, rel) meaning form `rel` 0) with the
// integer MILP engine. Returns true iff PROVEN integer-infeasible.
bool liaUnsat(PolynomialKernel& kernel,
              const std::vector<std::pair<LF, Relation>>& sys) {
    InternalMilpEngine milp;
    std::unordered_map<VarId, int> v2i;
    auto idx = [&](VarId v) -> int {
        auto it = v2i.find(v);
        if (it != v2i.end()) return it->second;
        int i = milp.addVar(std::string(kernel.varName(v)), InternalMilpEngine::VarKind::Int);
        v2i[v] = i;
        return i;
    };
    for (const auto& [lf, rel] : sys) {
        InternalMilpEngine::LinearConstraint lc;
        for (const auto& [v, co] : lf.c) lc.terms.push_back({idx(v), co});
        // (Σ co·v) + k  rel  0   ⇒   Σ co·v  rel  -k
        lc.rhs = -lf.k;
        lc.rel = rel;
        lc.reason = SatLit{0, true};
        milp.addConstraint(lc);
    }
    auto r = milp.solve(InternalMilpEngine::MilpMode::Complete);
    return r.kind == InternalMilpEngine::MilpResult::Kind::Unsat;
}

}  // namespace

bool niaLeafFarkasLiaUnsat(const std::vector<CdcacConstraint>& cons,
                           const std::unordered_set<VarId>& ctVars,
                           PolynomialKernel& kernel) {
    if (cons.empty()) return false;

    struct PC { LF A; std::map<VarId, LF> ct; Relation rel; };
    std::vector<PC> pcs;
    pcs.reserve(cons.size());
    for (const auto& c : cons) {
        PC pc;
        pc.rel = c.rel;
        if (!parse(kernel, c.poly, ctVars, pc.A, pc.ct)) { ctDiag("parse-shape"); return false; }
        pcs.push_back(std::move(pc));
    }

    // A CT may be eliminated only if it occurs in exactly ONE constraint.
    std::unordered_map<VarId, int> ctOcc;
    for (const auto& pc : pcs)
        for (const auto& [v, S] : pc.ct) { (void)S; ctOcc[v]++; }

    std::vector<std::pair<LF, Relation>> base;            // pure-λ constraints
    std::vector<std::vector<std::pair<LF, Relation>>> disj;  // per eliminated ineq

    for (auto& pc : pcs) {
        if (pc.ct.empty()) { base.push_back({pc.A, pc.rel}); continue; }
        // Has cost vars. Every CT here must be exclusive to this constraint.
        for (const auto& [v, S] : pc.ct) { (void)S; if (ctOcc[v] != 1) { ctDiag("ct-shared"); return false; } }

        Relation rel = pc.rel;
        LF A = pc.A;
        std::map<VarId, LF> ctm = std::move(pc.ct);
        if (rel == Relation::Lt || rel == Relation::Leq) {   // normalise to A + Σct·S {>,≥} 0
            A = negate(A);
            for (auto& [v, S] : ctm) S = negate(S);
            rel = (rel == Relation::Lt) ? Relation::Gt : Relation::Geq;
        } else if (rel == Relation::Eq) {
            ctDiag("ct-in-equality");
            return false;   // CT in an equality ⇒ divisibility case (not this prototype)
        }
        // ∃CT. A + Σ ct·S  rel 0   ≡   (∨_ct S_ct ≠ 0)  ∨  (A rel 0)
        std::vector<std::pair<LF, Relation>> d;
        for (const auto& [v, S] : ctm) {
            (void)v;
            d.push_back({S, Relation::Gt});            // S > 0
            d.push_back({negate(S), Relation::Gt});    // S < 0  ≡  -S > 0
        }
        d.push_back({A, rel});                          // A rel 0
        disj.push_back(std::move(d));
    }

    // Enumerate disjunct combinations; leaf is UNSAT iff every combo is LIA-UNSAT.
    std::size_t combos = 1;
    for (const auto& d : disj) { combos *= d.size(); if (combos > 4096) return false; }

    std::vector<std::size_t> sel(disj.size(), 0);
    while (true) {
        std::vector<std::pair<LF, Relation>> sys = base;
        for (std::size_t i = 0; i < disj.size(); ++i) sys.push_back(disj[i][sel[i]]);
        if (!liaUnsat(kernel, sys)) return false;   // a branch is SAT/unknown ⇒ not proven

        std::size_t p = 0;
        while (p < sel.size()) {
            if (++sel[p] < disj[p].size()) break;
            sel[p] = 0; ++p;
        }
        if (p == sel.size()) break;
    }
    return true;   // every disjunct combination is integer-infeasible
}

} // namespace xolver
