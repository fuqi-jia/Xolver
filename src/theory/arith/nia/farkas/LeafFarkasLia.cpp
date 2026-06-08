#include "theory/arith/nia/farkas/LeafFarkasLia.h"

#include "theory/arith/poly/PolynomialKernel.h"
#include "xolver/Solver.h"      // nested QF_LIA solve = the real CDCL(LIA) backend

#include <cstdio>
#include <cstdlib>
#include <map>
#include <set>
#include <string>
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

// A parsed leaf constraint:  A(λ) + Σ_ct ct·S_ct(λ)  `rel`  0.
struct PC { LF A; std::map<VarId, LF> ct; Relation rel; };

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

// Discharge the leaf's over-approximation  base ∧ ∧_i(∨ disjunct)  with a nested
// QF_LIA solve — the EXISTING CDCL(LIA) pipeline (SAT core + LiaSolver) handles
// the disjunctions natively, so no DNF enumeration. Returns true iff PROVEN
// integer-infeasible (a leaf UNSAT). Sound: a coefficient that does not fit a
// machine integer aborts the claim (false), never a wrong UNSAT.
// CEGAR Gate 2 (diag-only for now): under the validated λ model, substitute λ
// into the ORIGINAL constraints so each becomes linear in the cost vars CT, and
// check ∃CT feasibility with a nested QF_LIA solve. CT-UNSAT ⇒ the λ model is
// spurious (the abstraction was too weak there); CT-SAT ⇒ the leaf is genuinely
// feasible at this λ. Returns 'u' (unsat), 's' (sat), '?' (unknown/none).
char ctFeasibility(PolynomialKernel& kernel, const std::vector<PC>& pcs,
                   const std::unordered_map<VarId, mpq_class>& Mlam) {
    Solver s;
    s.setLogic("QF_LIA");
    Sort I = s.intSort();
    std::unordered_map<VarId, Term> ctT;
    bool ok = true, any = false;
    auto kc = [](Kind kk) { return static_cast<uint32_t>(kk); };
    auto evalLF = [&](const LF& lf) -> mpq_class {
        mpq_class acc = lf.k;
        for (const auto& [v, c] : lf.c) {
            auto it = Mlam.find(v);
            if (it == Mlam.end()) { ok = false; return 0; }
            acc += c * it->second;
        }
        return acc;
    };
    auto intT = [&](const mpq_class& c) -> Term {
        if (c.get_den() != 1 || !c.get_num().fits_slong_p()) { ok = false; return s.mkInt(0); }
        return s.mkInt(static_cast<int64_t>(c.get_num().get_si()));
    };
    auto ctVar = [&](VarId v) -> Term {
        auto it = ctT.find(v);
        if (it != ctT.end()) return it->second;
        Term t = s.mkVar(I, std::string(kernel.varName(v)));
        ctT.emplace(v, t);
        return t;
    };
    auto relK = [](Relation r) -> Kind {
        switch (r) { case Relation::Gt: return Kind::Gt; case Relation::Geq: return Kind::Geq;
            case Relation::Lt: return Kind::Lt; case Relation::Leq: return Kind::Leq; default: return Kind::Eq; }
    };
    for (const auto& pc : pcs) {
        if (pc.ct.empty()) continue;   // λ-only: held by the validated abstraction
        any = true;
        std::vector<Term> sum;
        mpq_class a = evalLF(pc.A);                 // A(λ) → constant
        for (const auto& [v, S] : pc.ct) {
            mpq_class s_v = evalLF(S);              // S_ct(λ) → constant coeff of ct
            sum.push_back(s.mkOp(kc(Kind::Mul), {intT(s_v), ctVar(v)}));
        }
        sum.push_back(intT(a));
        Term lhs = sum.size() == 1 ? sum[0] : s.mkOp(kc(Kind::Add), sum);
        s.assertFormula(s.mkOp(kc(relK(pc.rel)), {lhs, s.mkInt(0)}));
    }
    if (!ok) return '?';
    if (!any) return 's';     // no CT constraints ⇒ trivially feasible
    Result r = s.checkSat();
    return r == Result::Sat ? 's' : (r == Result::Unsat ? 'u' : '?');
}

bool disjLiaUnsat(PolynomialKernel& kernel,
                  const std::vector<std::pair<LF, Relation>>& base,
                  const std::vector<std::vector<std::pair<LF, Relation>>>& disj,
                  const std::vector<PC>& pcs) {
    // Reuse one nested Solver across the many bounded-B leaves: reset() clears
    // assertions/symbols without re-paying the per-instance (CaDiCaL) setup.
    static thread_local Solver s;
    s.reset();
    s.setLogic("QF_LIA");
    Sort I = s.intSort();
    std::unordered_map<VarId, Term> vt;
    bool ok = true;
    auto kc = [](Kind kk) { return static_cast<uint32_t>(kk); };
    auto var = [&](VarId v) -> Term {
        auto it = vt.find(v);
        if (it != vt.end()) return it->second;
        Term t = s.mkVar(I, std::string(kernel.varName(v)));
        vt.emplace(v, t);
        return t;
    };
    auto intT = [&](const mpq_class& c) -> Term {
        if (c.get_den() != 1 || !c.get_num().fits_slong_p()) { ok = false; return s.mkInt(0); }
        return s.mkInt(static_cast<int64_t>(c.get_num().get_si()));
    };
    auto formT = [&](const LF& lf) -> Term {
        std::vector<Term> sum;
        for (const auto& [v, c] : lf.c) sum.push_back(s.mkOp(kc(Kind::Mul), {intT(c), var(v)}));
        sum.push_back(intT(lf.k));
        return sum.size() == 1 ? sum[0] : s.mkOp(kc(Kind::Add), sum);
    };
    auto relK = [](Relation r) -> Kind {
        switch (r) { case Relation::Gt: return Kind::Gt; case Relation::Geq: return Kind::Geq;
            case Relation::Lt: return Kind::Lt; case Relation::Leq: return Kind::Leq; default: return Kind::Eq; }
    };
    auto atomT = [&](const std::pair<LF, Relation>& a) -> Term {
        return s.mkOp(kc(relK(a.second)), {formT(a.first), s.mkInt(0)});
    };
    for (const auto& a : base) s.assertFormula(atomT(a));
    for (const auto& d : disj) {
        std::vector<Term> ors;
        for (const auto& a : d) ors.push_back(atomT(a));
        s.assertFormula(ors.size() == 1 ? ors[0] : s.mkOp(kc(Kind::Or), ors));
    }
    if (!ok) return false;
    Result r = s.checkSat();
    if (r == Result::Unsat) return true;    // abstraction UNSAT ⇒ leaf UNSAT (sound filter)
    if (r != Result::Sat) return false;      // unknown ⇒ bail

    // ── CEGAR Gate 1: extract the λ model and VALIDATE it satisfies the
    // abstraction. No verdict change yet (still bail on abstraction-SAT). This
    // proves the extraction is correct before any later gate trusts it for
    // CT-feasibility / refinement — a wrong extraction would later become a
    // wrong UNSAT, so it is fully validated here first. Diag-gated.
    if (std::getenv("XOLVER_NIA_CT_DIAG")) {
        Model m = s.getModel();
        std::unordered_map<VarId, mpq_class> Mlam;
        bool extractOk = true;
        for (const auto& [v, t] : vt) {
            const std::string* sv = m.getValue(t.id());
            if (!sv) { extractOk = false; break; }
            try { Mlam[v] = mpq_class(mpz_class(*sv)); }
            catch (...) { extractOk = false; break; }
        }
        bool absOk = extractOk;
        if (extractOk) {
            auto evalLF = [&](const LF& lf) -> mpq_class {
                mpq_class acc = lf.k;
                for (const auto& [v, c] : lf.c) acc += c * Mlam[v];
                return acc;
            };
            auto holds = [&](const std::pair<LF, Relation>& a) -> bool {
                mpq_class val = evalLF(a.first);
                switch (a.second) {
                    case Relation::Gt: return val > 0;  case Relation::Geq: return val >= 0;
                    case Relation::Lt: return val < 0;  case Relation::Leq: return val <= 0;
                    case Relation::Eq: return val == 0; default: return false;
                }
            };
            for (const auto& a : base) if (!holds(a)) absOk = false;
            for (const auto& d : disj) {
                bool any = false;
                for (const auto& a : d) if (holds(a)) any = true;
                if (!any) absOk = false;
            }
        }
        ctDiag(extractOk ? (absOk ? "gate1-model-OK" : "gate1-model-FAIL-abs")
                         : "gate1-extract-FAIL");
        // ── CEGAR Gate 2: exact ∃CT feasibility under the validated λ model.
        // For an UNSAT (pentagon) leaf we EXPECT CT-UNSAT (the abstraction model
        // is spurious); a CT-SAT means the leaf is genuinely feasible at this λ.
        if (extractOk && absOk) {
            char cf = ctFeasibility(kernel, pcs, Mlam);
            ctDiag(cf == 'u' ? "gate2-CT-UNSAT(spurious)"
                 : cf == 's' ? "gate2-CT-SAT(feasible)" : "gate2-CT-unknown");
        }
    }
    return false;   // abstraction SAT ⇒ not proven UNSAT (unchanged)
}

// Dump one leaf's over-approximation (base ∧ ∧disj) as QF_LIA SMT-LIB to
// XOLVER_NIA_CT_SMT (first call only) — for checking whether it is really UNSAT
// and whether the LIA backend decides it.
void dumpSmt(PolynomialKernel& kernel,
             const std::vector<std::pair<LF, Relation>>& base,
             const std::vector<std::vector<std::pair<LF, Relation>>>& disj) {
    const char* path = std::getenv("XOLVER_NIA_CT_SMT");
    if (!path || !*path) return;
    static thread_local bool done = false;
    if (done) return;
    done = true;
    std::FILE* fp = std::fopen(path, "w");
    if (!fp) return;
    std::set<VarId> vars;
    auto collect = [&](const LF& lf) { for (const auto& [v, c] : lf.c) { (void)c; vars.insert(v); } };
    for (const auto& [lf, r] : base) { (void)r; collect(lf); }
    for (const auto& d : disj) for (const auto& [lf, r] : d) { (void)r; collect(lf); }
    auto lit = [](const mpq_class& c) -> std::string {
        mpz_class n = c.get_num();
        return n < 0 ? "(- " + mpz_class(-n).get_str() + ")" : n.get_str();
    };
    auto form = [&](const LF& lf) -> std::string {
        std::string s = "(+";
        for (const auto& [v, c] : lf.c) s += " (* " + lit(c) + " " + std::string(kernel.varName(v)) + ")";
        s += " " + lit(lf.k) + ")";
        return s;
    };
    auto relStr = [](Relation r) -> const char* {
        switch (r) { case Relation::Gt: return ">"; case Relation::Geq: return ">=";
            case Relation::Lt: return "<"; case Relation::Leq: return "<="; default: return "="; }
    };
    auto atom = [&](const std::pair<LF, Relation>& a) -> std::string {
        return std::string("(") + relStr(a.second) + " " + form(a.first) + " 0)";
    };
    std::fputs("(set-logic QF_LIA)\n", fp);
    for (VarId v : vars) std::fprintf(fp, "(declare-fun %s () Int)\n", std::string(kernel.varName(v)).c_str());
    for (const auto& a : base) std::fprintf(fp, "(assert %s)\n", atom(a).c_str());
    for (const auto& d : disj) {
        std::string s = "(or";
        for (const auto& a : d) s += " " + atom(a);
        s += ")";
        std::fprintf(fp, "(assert %s)\n", s.c_str());
    }
    std::fputs("(check-sat)\n", fp);
    std::fclose(fp);
}

}  // namespace

bool niaLeafFarkasLiaUnsat(const std::vector<CdcacConstraint>& cons,
                           const std::unordered_set<VarId>& ctVars,
                           PolynomialKernel& kernel) {
    if (cons.empty()) return false;

    std::vector<PC> pcs;
    pcs.reserve(cons.size());
    for (const auto& c : cons) {
        PC pc;
        pc.rel = c.rel;
        if (!parse(kernel, c.poly, ctVars, pc.A, pc.ct)) { ctDiag("parse-shape"); return false; }
        pcs.push_back(std::move(pc));
    }

    // A CT may be eliminated only if it occurs in exactly ONE constraint.
    std::unordered_map<VarId, int> ctOcc;     // # constraints a CT appears in
    std::unordered_map<VarId, bool> ctLamDep;  // S λ-dependent in ANY occurrence
    for (const auto& pc : pcs)
        for (const auto& [v, S] : pc.ct) { ctOcc[v]++; if (!S.c.empty()) ctLamDep[v] = true; }
    if (std::getenv("XOLVER_NIA_CT_DIAG")) {
        for (const auto& [v, n] : ctOcc) {
            std::string msg = "CT " + std::string(kernel.varName(v)) + " occ=" + std::to_string(n)
                            + (ctLamDep.count(v) ? " S=lam-dep" : " S=const");
            ctDiag(msg.c_str());
        }
    }

    // Vars known nonnegative from a base bound (v ≥ 0 / v > 0): lets us drop the
    // impossible sign branch of an S≠0 split, curbing the combination blow-up.
    std::unordered_set<VarId> nonnegVars;
    for (const auto& pc : pcs) {
        if (!pc.ct.empty()) continue;
        if (pc.A.c.size() == 1 && pc.A.k == 0
            && (pc.rel == Relation::Geq || pc.rel == Relation::Gt)) {
            const auto& [v, c] = *pc.A.c.begin();
            if (c > 0) nonnegVars.insert(v);
        }
    }
    auto sgn = [&](const LF& S) -> int {   // +1: S≥0, -1: S≤0, 0: sign unknown
        if (S.c.empty()) return S.k > 0 ? 1 : (S.k < 0 ? -1 : 0);
        if (S.c.size() == 1 && S.k == 0) {
            const auto& [v, c] = *S.c.begin();
            if (nonnegVars.count(v)) return c > 0 ? 1 : (c < 0 ? -1 : 0);
        }
        return 0;
    };

    std::vector<std::pair<LF, Relation>> base;            // pure-λ constraints
    std::vector<std::vector<std::pair<LF, Relation>>> disj;  // per CT-bearing constraint

    // SOUNDNESS (the key generalisation, valid for ANY cost vars — shared, λ-dep,
    // or in equalities): ∃CT. A + Σ ct·S ⋈ 0  ⟹  (∨_ct S_ct≠0) ∨ (A ⋈' 0).
    // (In any solution each constraint has some S_ct≠0, else S=0 and A⋈0 holds.)
    // It is a NECESSARY condition, so a pure-LIA UNSAT of the over-approximation
    // is a SOUND leaf UNSAT — possibly incomplete, never wrong.
    for (auto& pc : pcs) {
        if (pc.ct.empty()) { base.push_back({pc.A, pc.rel}); continue; }
        Relation rel = pc.rel;
        LF A = pc.A;
        std::map<VarId, LF> ctm = std::move(pc.ct);
        if (rel == Relation::Lt || rel == Relation::Leq) {   // normalise to {>,≥} 0
            A = negate(A);
            for (auto& [v, S] : ctm) S = negate(S);
            rel = (rel == Relation::Lt) ? Relation::Gt : Relation::Geq;
        }
        std::vector<std::pair<LF, Relation>> d;
        for (auto& [v, S] : ctm) {
            (void)v;
            int s = sgn(S);
            if (s >= 0) d.push_back({S, Relation::Gt});          // S > 0
            if (s <= 0) d.push_back({negate(S), Relation::Gt});  // S < 0 (skipped if S≥0)
        }
        // A-branch: equality ⇒ A = 0; inequality ⇒ A {>,≥} 0.
        d.push_back({A, rel});
        disj.push_back(std::move(d));
    }

    dumpSmt(kernel, base, disj);

    // Discharge the conjunction-of-disjunctions with the existing CDCL(LIA)
    // pipeline — no DNF enumeration, no combo blow-up.
    return disjLiaUnsat(kernel, base, disj, pcs);
}

} // namespace xolver
