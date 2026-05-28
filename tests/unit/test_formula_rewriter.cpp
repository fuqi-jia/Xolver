// Soundness gate for the generic FormulaRewriter (XOLVER_PP_REWRITE).
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
#include "xolver/Solver.h"

using namespace xolver;

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

// ===========================================================================
// Widened soundness oracle: REALS + UF + ARRAYS.
//
// The bool+int oracle above does not exercise: real-valued arithmetic folding,
// uninterpreted-function applications (which the rewriter rebuilds and whose
// numeric args it folds), or array select/store/const-array (rebuilt, with
// numeric index/value args folded) plus eq/distinct reflexivity over those
// sorts. This widened oracle covers them so XOLVER_PP_REWRITE is trustworthy
// on QF_*RA / UF / array logics (prerequisite for default-on promotion).
//
// A self-contained typed value + evaluator (kept separate from the bool/int
// oracle so as not to disturb it). UF is modelled deterministically (same name
// + same arg values -> same result, in BOTH original and rewritten eval), so
// arg-folding like f(2+3)=f(5) is required to agree. Arrays are Int->Int maps
// (default + finite overrides) with extensional equality.
// ===========================================================================
namespace {

struct WHarness {
    CoreIr ir;
    SortId boolS, intS, realS, arrS;  // arrS = (Array Int Int)
    WHarness() {
        boolS = ir.allocateSortId(); ir.registerSort(boolS, SortKind::Bool); ir.setBoolSortId(boolS);
        intS  = ir.allocateSortId(); ir.registerSort(intS,  SortKind::Int);  ir.setIntSortId(intS);
        realS = ir.allocateSortId(); ir.registerSort(realS, SortKind::Real); ir.setRealSortId(realS);
        arrS  = ir.allocateSortId(); ir.registerSort(arrS,  SortKind::Array);
        ir.registerArraySort(arrS, intS, intS);
    }
    ExprId mk(Kind k, SortId s, std::vector<ExprId> ch, Payload p = Payload()) {
        CoreExpr e; e.kind = k; e.sort = s;
        e.children = SmallVector<ExprId,4>(ch.begin(), ch.end());
        e.payload = std::move(p);
        return ir.add(std::move(e));
    }
};

struct WV {
    enum K { B, N, A } k = N;
    bool b = false;
    mpq_class n = 0;
    mpq_class adef = 0;                       // array default element
    std::map<mpq_class, mpq_class> aov;       // array overrides index->value
};

// Deterministic, consistent UF interpretation (filled lazily; same key -> same
// value across both eval calls). retKind: 'b' bool, 'i' numeric.
struct UFModel {
    std::map<std::string, WV> cache;
    WV get(const std::string& fname, const std::vector<mpq_class>& args, char retKind) {
        std::string key = fname;
        for (const auto& a : args) key += "#" + a.get_str();
        auto it = cache.find(key);
        if (it != cache.end()) return it->second;
        std::size_t h = std::hash<std::string>{}(key);
        WV v;
        if (retKind == 'b') { v.k = WV::B; v.b = (h & 1u) != 0; }
        else { v.k = WV::N; v.n = mpq_class(static_cast<long>(h % 11) - 5); }
        cache[key] = v;
        return v;
    }
};

using WAsg = std::map<std::string, WV>;

bool wArraysEqual(const WV& a, const WV& b) {
    // Extensional equality. Our generator only produces finite override sets
    // over a common default, so two arrays are equal iff their defaults match
    // and they agree at every overridden index (a missing override = default).
    if (a.adef != b.adef) return false;
    auto at = [](const WV& arr, const mpq_class& i) {
        auto it = arr.aov.find(i); return it != arr.aov.end() ? it->second : arr.adef;
    };
    std::map<mpq_class, mpq_class> idx;
    for (const auto& kv : a.aov) idx[kv.first];
    for (const auto& kv : b.aov) idx[kv.first];
    for (const auto& kv : idx) if (at(a, kv.first) != at(b, kv.first)) return false;
    return true;
}

std::optional<WV> weval(const CoreIr& ir, ExprId id, const WAsg& asg, UFModel& uf) {
    const CoreExpr& e = ir.get(id);
    auto num = [](mpq_class v){ WV w; w.k=WV::N; w.n=std::move(v); return w; };
    auto bl  = [](bool v){ WV w; w.k=WV::B; w.b=v; return w; };
    switch (e.kind) {
        case Kind::ConstBool: return bl(std::get<bool>(e.payload.value));
        case Kind::ConstInt: {
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) return num(mpq_class(*i));
            if (auto* s = std::get_if<std::string>(&e.payload.value)) return num(mpq_class(*s));
            return std::nullopt;
        }
        case Kind::ConstReal: {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) return num(mpq_class(*s));
            if (auto* i = std::get_if<int64_t>(&e.payload.value)) return num(mpq_class(*i));
            return std::nullopt;
        }
        case Kind::Variable: {
            auto it = asg.find(std::get<std::string>(e.payload.value));
            if (it == asg.end()) return std::nullopt;
            return it->second;
        }
        case Kind::Not: { auto a=weval(ir,e.children[0],asg,uf); if(!a)return std::nullopt; return bl(!a->b); }
        case Kind::And: { bool r=true; for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v)return std::nullopt; r=r&&v->b;} return bl(r); }
        case Kind::Or:  { bool r=false; for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v)return std::nullopt; r=r||v->b;} return bl(r); }
        case Kind::Implies: { auto a=weval(ir,e.children[0],asg,uf); auto b=weval(ir,e.children[1],asg,uf); if(!a||!b)return std::nullopt; return bl(!a->b||b->b); }
        case Kind::Xor: { auto a=weval(ir,e.children[0],asg,uf); auto b=weval(ir,e.children[1],asg,uf); if(!a||!b)return std::nullopt; return bl(a->b!=b->b); }
        case Kind::Ite: { auto c=weval(ir,e.children[0],asg,uf); if(!c)return std::nullopt; return weval(ir, c->b?e.children[1]:e.children[2], asg, uf); }
        case Kind::Neg: { auto a=weval(ir,e.children[0],asg,uf); if(!a)return std::nullopt; return num(-a->n); }
        case Kind::Add: { mpq_class r=0; for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v)return std::nullopt; r+=v->n;} return num(r); }
        case Kind::Mul: { mpq_class r=1; for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v)return std::nullopt; r*=v->n;} return num(r); }
        case Kind::Sub: { auto a=weval(ir,e.children[0],asg,uf); auto b=weval(ir,e.children[1],asg,uf); if(!a||!b)return std::nullopt; return num(a->n-b->n); }
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
            auto a=weval(ir,e.children[0],asg,uf); auto b=weval(ir,e.children[1],asg,uf); if(!a||!b)return std::nullopt;
            const mpq_class& x=a->n; const mpq_class& y=b->n;
            switch(e.kind){case Kind::Lt:return bl(x<y);case Kind::Leq:return bl(x<=y);case Kind::Gt:return bl(x>y);default:return bl(x>=y);}
        }
        case Kind::Eq: case Kind::Distinct: {
            std::vector<WV> vs; for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v)return std::nullopt; vs.push_back(*v);}
            auto same=[&](const WV&a,const WV&b)->bool{
                if(a.k!=b.k)return false;
                if(a.k==WV::B)return a.b==b.b;
                if(a.k==WV::N)return a.n==b.n;
                return wArraysEqual(a,b);
            };
            if(e.kind==Kind::Eq){bool all=true; for(size_t i=1;i<vs.size();++i) if(!same(vs[0],vs[i]))all=false; return bl(all);}
            for(size_t i=0;i<vs.size();++i)for(size_t j=i+1;j<vs.size();++j) if(same(vs[i],vs[j])) return bl(false);
            return bl(true);
        }
        case Kind::UFApply: {
            std::vector<mpq_class> args;
            for(ExprId c:e.children){auto v=weval(ir,c,asg,uf); if(!v||v->k!=WV::N)return std::nullopt; args.push_back(v->n);}
            char ret = (e.sort==ir.boolSortId())?'b':'i';
            return uf.get(std::get<std::string>(e.payload.value), args, ret);
        }
        case Kind::ConstArray: { auto v=weval(ir,e.children[0],asg,uf); if(!v)return std::nullopt; WV w; w.k=WV::A; w.adef=v->n; return w; }
        case Kind::Store: {
            auto a=weval(ir,e.children[0],asg,uf); auto i=weval(ir,e.children[1],asg,uf); auto v=weval(ir,e.children[2],asg,uf);
            if(!a||!i||!v||a->k!=WV::A)return std::nullopt; WV w=*a; w.aov[i->n]=v->n; return w;
        }
        case Kind::Select: {
            auto a=weval(ir,e.children[0],asg,uf); auto i=weval(ir,e.children[1],asg,uf);
            if(!a||!i||a->k!=WV::A)return std::nullopt;
            auto it=a->aov.find(i->n); return num(it!=a->aov.end()?it->second:a->adef);
        }
        default: return std::nullopt;
    }
}

TEST_CASE("rewriter: random equivalence oracle over REALS + UF + ARRAYS") {
    std::mt19937 rng(0xBADC0DE);
    // numeric vars: int x,y ; real r,s.  array a,b.  numeric-UF fi.  bool-UF fp.
    const std::vector<std::pair<std::string,char>> numVars = {{"x",'i'},{"y",'i'},{"r",'r'},{"s",'r'}};
    const std::vector<std::string> arrVars = {"a","b"};
    const std::vector<int> grid = {-1, 0, 2};            // values for int/real vars

    for (int iter = 0; iter < 300; ++iter) {
        WHarness h;
        std::map<std::string,ExprId> V;
        for (auto& [nm,t] : numVars) V[nm] = h.mk(Kind::Variable, t=='i'?h.intS:h.realS, {}, Payload(nm));
        for (auto& nm : arrVars) V[nm] = h.mk(Kind::Variable, h.arrS, {}, Payload(nm));

        // Mutually-recursive generators: forward-declared std::functions, all
        // capturing by reference, so each can call the others once assigned.
        std::function<ExprId(int)> genNum, genArr, genBool;
        genArr = [&](int d)->ExprId {
            if (d<=0 || rng()%2==0) return V[arrVars[rng()%arrVars.size()]];
            if (rng()%2==0) return h.mk(Kind::ConstArray,h.arrS,{genNum(d-1)});
            return h.mk(Kind::Store,h.arrS,{genArr(d-1),genNum(d-1),genNum(d-1)});
        };
        static const std::array<const char*,6> realLits = {"0","1/2","-1/2","3/2","-2","2"};
        genNum = [&](int d)->ExprId {
            if (d<=0 || rng()%3==0) {
                int r=rng()%4;
                if(r==0) return V["x"]; if(r==1) return V["r"];
                if(r==2) return h.mk(Kind::ConstInt,h.intS,{},Payload((int64_t)((int)(rng()%5)-2)));
                return h.mk(Kind::ConstReal,h.realS,{},Payload(std::string(realLits[rng()%realLits.size()])));
            }
            int r=rng()%6; SortId s=(rng()%2)?h.intS:h.realS;
            if(r==0) return h.mk(Kind::Add,s,{genNum(d-1),genNum(d-1)});
            if(r==1) return h.mk(Kind::Sub,s,{genNum(d-1),genNum(d-1)});
            if(r==2) return h.mk(Kind::Mul,s,{genNum(d-1),genNum(d-1)});
            if(r==3) return h.mk(Kind::Neg,s,{genNum(d-1)});
            if(r==4) return h.mk(Kind::UFApply,h.intS,{genNum(d-1)},Payload(std::string("fi")));
            return h.mk(Kind::Select,h.intS,{genArr(d-1),genNum(d-1)});
        };
        genBool = [&](int d)->ExprId {
            if (d<=0 || rng()%4==0) {
                int r=rng()%5;
                if(r==0) return h.mk(Kind::ConstBool,h.boolS,{},Payload(rng()%2==0));
                if(r==1) return h.mk(Kind::UFApply,h.boolS,{genNum(d-1)},Payload(std::string("fp")));  // bool UF
                static const std::array<Kind,4> rel={Kind::Lt,Kind::Leq,Kind::Gt,Kind::Geq};
                if(r==2) return h.mk(rel[rng()%4],h.boolS,{genNum(d-1),genNum(d-1)});
                if(r==3) return h.mk(Kind::Eq,h.boolS,{genNum(d-1),genNum(d-1)});       // numeric eq
                return h.mk(Kind::Eq,h.boolS,{genArr(d-1),genArr(d-1)});                // array eq (reflexivity etc.)
            }
            int r=rng()%6;
            if(r==0) return h.mk(Kind::Not,h.boolS,{genBool(d-1)});
            if(r==1) return h.mk(Kind::And,h.boolS,{genBool(d-1),genBool(d-1)});
            if(r==2) return h.mk(Kind::Or,h.boolS,{genBool(d-1),genBool(d-1)});
            if(r==3) return h.mk(Kind::Ite,h.boolS,{genBool(d-1),genBool(d-1),genBool(d-1)});
            if(r==4) return h.mk(Kind::Distinct,h.boolS,{genArr(d-1),genArr(d-1)});
            return h.mk(Kind::Eq,h.boolS,{genBool(d-1),genBool(d-1)});
        };

        ExprId orig = genBool(4);
        FormulaRewriter rw(h.ir, h.boolS);
        ExprId rewritten = rw.rewrite(orig);

        // Enumerate assignments: numeric vars over the grid, arrays over a few
        // shapes. Check eval(orig)==eval(rewritten) under a shared UF model.
        std::vector<std::map<std::string,mpq_class>> numAssigns;
        // small cartesian: int x=y over {-1,0,2}; real r=s over a RATIONAL grid
        // (incl. 1/2) so true real folding is exercised, not just integer-valued.
        const std::array<mpq_class,3> rgrid = {mpq_class(-1), mpq_class(1,2), mpq_class(2)};
        for (int vx : grid) for (const mpq_class& vr : rgrid) {
            numAssigns.push_back({{"x",mpq_class(vx)},{"y",mpq_class(vx)},
                                  {"r",vr},{"s",vr}});
        }
        auto mkArr = [](mpq_class def, std::map<mpq_class,mpq_class> ov){ WV w; w.k=WV::A; w.adef=def; w.aov=std::move(ov); return w; };
        std::vector<std::pair<WV,WV>> arrAssigns = {
            {mkArr(0,{}), mkArr(0,{})},                       // a=b=const0
            {mkArr(0,{{0,1}}), mkArr(0,{})},                  // a[0]=1 ; b=0
            {mkArr(1,{{2,3}}), mkArr(1,{{2,3}})},             // a=b (same shape)
        };
        for (auto& na : numAssigns) {
            for (auto& [av,bv] : arrAssigns) {
                WAsg asg;
                for (auto& [k,v] : na) { WV w; w.k=WV::N; w.n=v; asg[k]=w; }
                asg["a"]=av; asg["b"]=bv;
                UFModel uf;  // fresh per assignment, shared by both eval calls
                auto vo = weval(h.ir, orig, asg, uf);
                auto vr = weval(h.ir, rewritten, asg, uf);
                REQUIRE(vo.has_value());
                REQUIRE(vr.has_value());
                REQUIRE(vo->k == WV::B);  // top is boolean
                REQUIRE(vr->k == WV::B);
                CHECK(vo->b == vr->b);
            }
        }
    }
}

} // namespace

// End-to-end guard: with the flag ON, rewriting deep EUF f-chains must not
// corrupt nodes. (Regression: rewriteRec held a reference into CoreIr's exprs_
// across a child-rewrite that called ir_.add(), reallocating the vector; the
// dangling read produced a garbage node and a wrong SAT at exactly the chain
// depth where the realloc boundary fell — euf_055.)
TEST_CASE("rewriter: deep EUF chains stay unsat under XOLVER_PP_REWRITE") {
    struct EnvGuard {
        EnvGuard()  { setenv("XOLVER_PP_REWRITE", "1", 1); }
        ~EnvGuard() { unsetenv("XOLVER_PP_REWRITE"); }
    } guard;

    for (int depth = 1; depth <= 9; ++depth) {
        std::string fx = "x", fy = "y";
        for (int i = 0; i < depth; ++i) { fx = "(f " + fx + ")"; fy = "(f " + fy + ")"; }
        std::string smt =
            "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun f (U) U)\n"
            "(declare-const x U)(declare-const y U)\n(assert (= x y))\n"
            "(assert (distinct " + fx + " " + fy + "))\n(check-sat)\n";
        std::string path = (std::filesystem::temp_directory_path() /
                            ("xolver_rw_euf_" + std::to_string(depth) + ".smt2")).string();
        { std::ofstream(path) << smt; }

        xolver::Solver solver;
        REQUIRE(solver.parseFile(path));
        Result r = solver.checkSat();
        CHECK(static_cast<int>(r) == static_cast<int>(Result::Unsat));
    }
}
