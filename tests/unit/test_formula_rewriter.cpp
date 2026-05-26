// Soundness gate for the generic FormulaRewriter (ZOLVER_PP_REWRITE).
//
// A wrong rewrite rule is instant unsoundness that ModelValidator cannot catch
// when it yields a wrong UNSAT. So every rule is verified against a brute-force
// model oracle: build an expression, rewrite it, and assert the rewritten form
// evaluates identically to the original under EVERY assignment in a small grid.
#include <doctest/doctest.h>
#include "frontend/preprocess/FormulaRewriter.h"
#include "expr/ir.h"
#include <gmpxx.h>
#include <random>
#include <variant>
#include <vector>
#include <optional>
#include <string>
#include <map>
#include <functional>
#include <array>
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include "zolver/Solver.h"

using namespace zolver;

namespace {

// ---- a tiny CoreIr builder + evaluator used only by the oracle ----
struct Harness {
    CoreIr ir;
    SortId boolS, intS, realS;

    Harness() {
        boolS = ir.allocateSortId(); ir.registerSort(boolS, SortKind::Bool); ir.setBoolSortId(boolS);
        intS  = ir.allocateSortId(); ir.registerSort(intS,  SortKind::Int);  ir.setIntSortId(intS);
        realS = ir.allocateSortId(); ir.registerSort(realS, SortKind::Real); ir.setRealSortId(realS);
    }

    ExprId mk(Kind k, SortId s, std::vector<ExprId> ch, Payload p = Payload()) {
        CoreExpr e; e.kind = k; e.sort = s;
        e.children = SmallVector<ExprId,4>(ch.begin(), ch.end());
        e.payload = std::move(p);
        return ir.add(std::move(e));
    }
    ExprId boolVar(const std::string& n) { return mk(Kind::Variable, boolS, {}, Payload(n)); }
    ExprId intVar(const std::string& n)  { return mk(Kind::Variable, intS,  {}, Payload(n)); }
    ExprId cbool(bool b) { return mk(Kind::ConstBool, boolS, {}, Payload(b)); }
    ExprId cint(int64_t v) { return mk(Kind::ConstInt, intS, {}, Payload(v)); }
    ExprId creal(const std::string& s) { return mk(Kind::ConstReal, realS, {}, Payload(s)); }
};

using Val = std::variant<bool, mpq_class>;
using Asg = std::map<std::string, Val>;

// Evaluate a (total) expression. Returns nullopt only for shapes the oracle's
// generator never produces (so a nullopt in practice signals a test bug).
std::optional<Val> eval(const CoreIr& ir, ExprId id, const Asg& asg) {
    const CoreExpr& e = ir.get(id);
    auto asBool = [](const Val& v){ return std::get<bool>(v); };
    auto asNum  = [](const Val& v){ return std::get<mpq_class>(v); };
    switch (e.kind) {
        case Kind::ConstBool: return Val(std::get<bool>(e.payload.value));
        case Kind::ConstInt: {
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) return Val(mpq_class(*i));
            if (auto* s = std::get_if<std::string>(&e.payload.value)) return Val(mpq_class(*s));
            return std::nullopt;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) return Val(mpq_class(*s));
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) return Val(mpq_class(*i));
            return std::nullopt;
        }
        case Kind::Variable: {
            auto it = asg.find(std::get<std::string>(e.payload.value));
            if (it == asg.end()) return std::nullopt;
            return it->second;
        }
        case Kind::Not: { auto a = eval(ir,e.children[0],asg); if(!a) return std::nullopt; return Val(!asBool(*a)); }
        case Kind::And: {
            bool r = true;
            for (ExprId c : e.children) { auto v = eval(ir,c,asg); if(!v) return std::nullopt; r = r && asBool(*v); }
            return Val(r);
        }
        case Kind::Or: {
            bool r = false;
            for (ExprId c : e.children) { auto v = eval(ir,c,asg); if(!v) return std::nullopt; r = r || asBool(*v); }
            return Val(r);
        }
        case Kind::Implies: {
            auto a = eval(ir,e.children[0],asg); auto b = eval(ir,e.children[1],asg);
            if(!a||!b) return std::nullopt; return Val(!asBool(*a) || asBool(*b));
        }
        case Kind::Xor: {
            auto a = eval(ir,e.children[0],asg); auto b = eval(ir,e.children[1],asg);
            if(!a||!b) return std::nullopt; return Val(asBool(*a) != asBool(*b));
        }
        case Kind::Ite: {
            auto c = eval(ir,e.children[0],asg); if(!c) return std::nullopt;
            return eval(ir, asBool(*c) ? e.children[1] : e.children[2], asg);
        }
        case Kind::Eq: {
            // homogeneous (all bool or all numeric)
            std::vector<Val> vs;
            for (ExprId c : e.children) { auto v = eval(ir,c,asg); if(!v) return std::nullopt; vs.push_back(*v); }
            bool allEq = true;
            for (size_t i=1;i<vs.size();++i) {
                if (std::holds_alternative<bool>(vs[0])) { if (asBool(vs[i]) != asBool(vs[0])) allEq=false; }
                else { if (asNum(vs[i]) != asNum(vs[0])) allEq=false; }
            }
            return Val(allEq);
        }
        case Kind::Distinct: {
            std::vector<Val> vs;
            for (ExprId c : e.children) { auto v = eval(ir,c,asg); if(!v) return std::nullopt; vs.push_back(*v); }
            for (size_t i=0;i<vs.size();++i) for (size_t j=i+1;j<vs.size();++j) {
                if (std::holds_alternative<bool>(vs[0])) { if (asBool(vs[i])==asBool(vs[j])) return Val(false); }
                else { if (asNum(vs[i])==asNum(vs[j])) return Val(false); }
            }
            return Val(true);
        }
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
            auto a = eval(ir,e.children[0],asg); auto b = eval(ir,e.children[1],asg);
            if(!a||!b) return std::nullopt;
            mpq_class x = asNum(*a), y = asNum(*b);
            switch (e.kind) {
                case Kind::Lt:  return Val(x <  y);
                case Kind::Leq: return Val(x <= y);
                case Kind::Gt:  return Val(x >  y);
                default:        return Val(x >= y);
            }
        }
        case Kind::Neg: { auto a = eval(ir,e.children[0],asg); if(!a) return std::nullopt; return Val(-asNum(*a)); }
        case Kind::Add: { mpq_class r=0; for (ExprId c:e.children){auto v=eval(ir,c,asg); if(!v) return std::nullopt; r+=asNum(*v);} return Val(r); }
        case Kind::Mul: { mpq_class r=1; for (ExprId c:e.children){auto v=eval(ir,c,asg); if(!v) return std::nullopt; r*=asNum(*v);} return Val(r); }
        case Kind::Sub: {
            auto a = eval(ir,e.children[0],asg); auto b = eval(ir,e.children[1],asg);
            if(!a||!b) return std::nullopt; return Val(asNum(*a)-asNum(*b));
        }
        default: return std::nullopt;
    }
}

bool valEq(const Val& a, const Val& b) {
    if (std::holds_alternative<bool>(a) != std::holds_alternative<bool>(b)) return false;
    if (std::holds_alternative<bool>(a)) return std::get<bool>(a)==std::get<bool>(b);
    return std::get<mpq_class>(a)==std::get<mpq_class>(b);
}

// Enumerate all bool assignments × int grid, and assert eval(orig)==eval(rw).
void checkEquivalent(Harness& h, ExprId orig, ExprId rw,
                     const std::vector<std::string>& boolVars,
                     const std::vector<std::string>& intVars,
                     const std::vector<int>& grid) {
    size_t bN = boolVars.size(), iN = intVars.size();
    for (uint32_t mask = 0; mask < (1u << bN); ++mask) {
        // iterate int grid as a mixed-radix counter
        std::vector<size_t> idx(iN, 0);
        bool done = false;
        while (!done) {
            Asg asg;
            for (size_t b=0;b<bN;++b) asg[boolVars[b]] = Val(((mask>>b)&1)!=0);
            for (size_t i=0;i<iN;++i) asg[intVars[i]] = Val(mpq_class(grid[idx[i]]));
            auto vo = eval(h.ir, orig, asg);
            auto vr = eval(h.ir, rw,   asg);
            REQUIRE(vo.has_value());
            REQUIRE(vr.has_value());
            CHECK(valEq(*vo, *vr));
            // advance counter
            if (iN == 0) break;
            size_t k = 0;
            for (; k < iN; ++k) { if (++idx[k] < grid.size()) break; idx[k] = 0; }
            if (k == iN) done = true;
        }
        if (bN == 0 && iN == 0) break;
    }
}

} // namespace

TEST_CASE("rewriter: boolean identities") {
    Harness h;
    ExprId p = h.boolVar("p"), q = h.boolVar("q");
    FormulaRewriter rw(h.ir, h.boolS);

    CHECK(rw.rewrite(h.mk(Kind::Not, h.boolS, {h.mk(Kind::Not, h.boolS, {p})})) == p); // ¬¬p → p
    CHECK(h.ir.get(rw.rewrite(h.mk(Kind::And, h.boolS, {p, h.cbool(false)}))).kind == Kind::ConstBool); // p∧⊥ → ⊥
    CHECK(rw.rewrite(h.mk(Kind::And, h.boolS, {p, h.cbool(true)})) == p);   // p∧⊤ → p
    CHECK(rw.rewrite(h.mk(Kind::Or,  h.boolS, {p, h.cbool(false)})) == p);  // p∨⊥ → p
    // p ∧ ¬p → ⊥
    ExprId notP = h.mk(Kind::Not, h.boolS, {p});
    ExprId contradiction = rw.rewrite(h.mk(Kind::And, h.boolS, {p, notP}));
    bool b; CHECK((h.ir.get(contradiction).kind == Kind::ConstBool &&
                   (b = std::get<bool>(h.ir.get(contradiction).payload.value), b == false)));
    // p ∨ ¬p → ⊤
    ExprId tauto = rw.rewrite(h.mk(Kind::Or, h.boolS, {p, notP}));
    CHECK((h.ir.get(tauto).kind == Kind::ConstBool && std::get<bool>(h.ir.get(tauto).payload.value)));
    // ite(⊤,p,q) → p ; ite(c,p,p) → p
    CHECK(rw.rewrite(h.mk(Kind::Ite, h.boolS, {h.cbool(true), p, q})) == p);
    CHECK(rw.rewrite(h.mk(Kind::Ite, h.boolS, {q, p, p})) == p);
    (void)q;
}

TEST_CASE("rewriter: arithmetic const fold + identities") {
    Harness h;
    ExprId x = h.intVar("x");
    FormulaRewriter rw(h.ir, h.boolS);

    // (+ 2 3) → 5
    ExprId five = rw.rewrite(h.mk(Kind::Add, h.intS, {h.cint(2), h.cint(3)}));
    CHECK(h.ir.get(five).kind == Kind::ConstInt);
    CHECK(std::get<int64_t>(h.ir.get(five).payload.value) == 5);
    // (+ x 0) → x ; (* x 1) → x ; (* x 0) → 0
    CHECK(rw.rewrite(h.mk(Kind::Add, h.intS, {x, h.cint(0)})) == x);
    CHECK(rw.rewrite(h.mk(Kind::Mul, h.intS, {x, h.cint(1)})) == x);
    ExprId zero = rw.rewrite(h.mk(Kind::Mul, h.intS, {x, h.cint(0)}));
    CHECK((h.ir.get(zero).kind == Kind::ConstInt && std::get<int64_t>(h.ir.get(zero).payload.value)==0));
    // (< 2 3) → ⊤ ; (< 3 3) → ⊥
    CHECK((h.ir.get(rw.rewrite(h.mk(Kind::Lt,h.intS,{h.cint(2),h.cint(3)}))).kind==Kind::ConstBool &&
           std::get<bool>(h.ir.get(rw.rewrite(h.mk(Kind::Lt,h.intS,{h.cint(2),h.cint(3)}))).payload.value)));
    ExprId f = rw.rewrite(h.mk(Kind::Lt,h.intS,{h.cint(3),h.cint(3)}));
    CHECK((h.ir.get(f).kind==Kind::ConstBool && !std::get<bool>(h.ir.get(f).payload.value)));
    // (= x x) → ⊤
    CHECK((h.ir.get(rw.rewrite(h.mk(Kind::Eq,h.intS,{x,x}))).kind==Kind::ConstBool));
}

TEST_CASE("rewriter: top-level verdict + commit") {
    Harness h;
    ExprId x = h.intVar("x");
    // assert (< 3 3)  → const false → Unsat
    h.ir.addAssertion(h.mk(Kind::Lt, h.intS, {h.cint(3), h.cint(3)}));
    FormulaRewriter rw(h.ir, h.boolS);
    CHECK(rw.run() == FormulaRewriter::Verdict::Unsat);

    // assert (<= 1 2) (tautology) and (< x 5) → tautology dropped, real one kept
    Harness h2;
    ExprId xx = h2.intVar("x");
    h2.ir.addAssertion(h2.mk(Kind::Leq, h2.intS, {h2.cint(1), h2.cint(2)}));
    h2.ir.addAssertion(h2.mk(Kind::Lt, h2.intS, {xx, h2.cint(5)}));
    FormulaRewriter rw2(h2.ir, h2.boolS);
    CHECK(rw2.run() == FormulaRewriter::Verdict::Normal);
    rw2.commit();
    CHECK(h2.ir.assertions().size() == 1); // tautology dropped
    (void)x;
}

// ---------------------------------------------------------------------------
// The brute-force oracle: random formulas, equivalence over the whole grid.
// ---------------------------------------------------------------------------
TEST_CASE("rewriter: random equivalence oracle") {
    std::mt19937 rng(0xC0FFEE);
    const std::vector<std::string> boolVars = {"p", "q"};
    const std::vector<std::string> intVars  = {"x", "y"};
    const std::vector<int> grid = {-2, -1, 0, 1, 2};

    for (int iter = 0; iter < 400; ++iter) {
        Harness h;
        std::vector<ExprId> bvars = {h.boolVar("p"), h.boolVar("q")};
        std::vector<ExprId> ivars = {h.intVar("x"), h.intVar("y")};

        std::function<ExprId(int)> genInt = [&](int depth) -> ExprId {
            if (depth <= 0 || (rng()%3==0)) {
                if (rng()%2==0) return ivars[rng()%ivars.size()];
                return h.cint(static_cast<int64_t>(rng()%7) - 3);
            }
            int r = rng()%4;
            if (r==0) return h.mk(Kind::Add, h.intS, {genInt(depth-1), genInt(depth-1)});
            if (r==1) return h.mk(Kind::Sub, h.intS, {genInt(depth-1), genInt(depth-1)});
            if (r==2) return h.mk(Kind::Mul, h.intS, {genInt(depth-1), genInt(depth-1)});
            return h.mk(Kind::Neg, h.intS, {genInt(depth-1)});
        };
        std::function<ExprId(int)> genBool = [&](int depth) -> ExprId {
            if (depth <= 0 || (rng()%4==0)) {
                int r = rng()%3;
                if (r==0) return bvars[rng()%bvars.size()];
                if (r==1) return h.cbool(rng()%2==0);
                // arithmetic atom
                static const std::array<Kind,6> rels = {Kind::Lt,Kind::Leq,Kind::Gt,Kind::Geq,Kind::Eq,Kind::Distinct};
                Kind rel = rels[rng()%rels.size()];
                return h.mk(rel, h.intS, {genInt(2), genInt(2)});
            }
            int r = rng()%7;
            if (r==0) return h.mk(Kind::Not, h.boolS, {genBool(depth-1)});
            if (r==1) return h.mk(Kind::And, h.boolS, {genBool(depth-1), genBool(depth-1)});
            if (r==2) return h.mk(Kind::Or,  h.boolS, {genBool(depth-1), genBool(depth-1)});
            if (r==3) return h.mk(Kind::Implies, h.boolS, {genBool(depth-1), genBool(depth-1)});
            if (r==4) return h.mk(Kind::Xor, h.boolS, {genBool(depth-1), genBool(depth-1)});
            if (r==5) return h.mk(Kind::Ite, h.boolS, {genBool(depth-1), genBool(depth-1), genBool(depth-1)});
            // bool equality (iff)
            return h.mk(Kind::Eq, h.boolS, {genBool(depth-1), genBool(depth-1)});
        };

        ExprId orig = genBool(4);
        FormulaRewriter rw(h.ir, h.boolS);
        ExprId rewritten = rw.rewrite(orig);
        checkEquivalent(h, orig, rewritten, boolVars, intVars, grid);
    }
}

// End-to-end guard: with the flag ON, rewriting deep EUF f-chains must not
// corrupt nodes. (Regression: rewriteRec held a reference into CoreIr's exprs_
// across a child-rewrite that called ir_.add(), reallocating the vector; the
// dangling read produced a garbage node and a wrong SAT at exactly the chain
// depth where the realloc boundary fell — euf_055.)
TEST_CASE("rewriter: deep EUF chains stay unsat under ZOLVER_PP_REWRITE") {
    struct EnvGuard {
        EnvGuard()  { setenv("ZOLVER_PP_REWRITE", "1", 1); }
        ~EnvGuard() { unsetenv("ZOLVER_PP_REWRITE"); }
    } guard;

    for (int depth = 1; depth <= 9; ++depth) {
        std::string fx = "x", fy = "y";
        for (int i = 0; i < depth; ++i) { fx = "(f " + fx + ")"; fy = "(f " + fy + ")"; }
        std::string smt =
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n"
            "(declare-const x U)(declare-const y U)\n(assert (= x y))\n"
            "(assert (distinct " + fx + " " + fy + "))\n(check-sat)\n";
        std::string path = (std::filesystem::temp_directory_path() /
                            ("zolver_rw_euf_" + std::to_string(depth) + ".smt2")).string();
        { std::ofstream(path) << smt; }

        zolver::Solver solver;
        REQUIRE(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
    }
}
