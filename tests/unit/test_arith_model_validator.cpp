#include <doctest/doctest.h>
#include "proof/ArithModelValidator.h"
#include "expr/ir.h"

using namespace zolver;

namespace {
struct Fix {
    CoreIr ir;
    SortId boolS, intS, realS;
    Fix() {
        boolS = ir.allocateSortId(); ir.registerSort(boolS, SortKind::Bool); ir.setBoolSortId(boolS);
        intS  = ir.allocateSortId(); ir.registerSort(intS, SortKind::Int);   ir.setIntSortId(intS);
        realS = ir.allocateSortId(); ir.registerSort(realS, SortKind::Real);  ir.setRealSortId(realS);
    }
    ExprId var(const std::string& n, SortId s) {
        return ir.add(CoreExpr{Kind::Variable, s, {}, Payload(n)});
    }
    ExprId cint(int64_t v) { return ir.add(CoreExpr{Kind::ConstInt, intS, {}, Payload(v)}); }
    ExprId bin(Kind k, ExprId a, ExprId b, SortId s) {
        CoreExpr e; e.kind = k; e.sort = s; e.children.push_back(a); e.children.push_back(b);
        return ir.add(std::move(e));
    }
};
}

TEST_CASE("ArithModelValidator: satisfied model") {
    Fix f;
    ExprId x = f.var("x", f.intS), y = f.var("y", f.intS);
    // (= (+ x y) 5) ∧ (>= x 2)
    ExprId sum = f.bin(Kind::Add, x, y, f.intS);
    ExprId a1 = f.bin(Kind::Eq, sum, f.cint(5), f.boolS);
    ExprId a2 = f.bin(Kind::Geq, x, f.cint(2), f.boolS);

    ArithModelValidator::NumAssignment num{{"x", 3}, {"y", 2}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({a1, a2}) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("ArithModelValidator: violated model") {
    Fix f;
    ExprId x = f.var("x", f.intS), y = f.var("y", f.intS);
    ExprId sum = f.bin(Kind::Add, x, y, f.intS);
    ExprId a1 = f.bin(Kind::Eq, sum, f.cint(5), f.boolS);

    // x=1, y=1 → x+y=2 ≠ 5  → definite violation
    ArithModelValidator::NumAssignment num{{"x", 1}, {"y", 1}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Violated);
}

TEST_CASE("ArithModelValidator: distinct violation (matches the UFLRA model-bug shape)") {
    Fix f;
    ExprId a = f.var("a", f.realS), b = f.var("b", f.realS);
    CoreExpr d; d.kind = Kind::Distinct; d.sort = f.boolS;
    d.children.push_back(a); d.children.push_back(b);
    ExprId distinct = f.ir.add(std::move(d));

    // a=b=0 violates (distinct a b)
    ArithModelValidator::NumAssignment num{{"a", 0}, {"b", 0}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({distinct}) == ArithModelValidator::Verdict::Violated);
}

TEST_CASE("ArithModelValidator: indeterminate on missing variable") {
    Fix f;
    ExprId x = f.var("x", f.intS);
    ExprId a1 = f.bin(Kind::Geq, x, f.cint(2), f.boolS);

    // x not assigned → cannot evaluate → indeterminate (never Violated)
    ArithModelValidator v(f.ir, {}, {});
    CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Indeterminate);
}

TEST_CASE("ArithModelValidator: Int div/mod use Euclidean semantics") {
    Fix f;
    ExprId x = f.var("x", f.intS);
    // (= (div x 3) 2) ∧ (= (mod x 3) 1) — x=7 satisfies (7/3=2, 7%3=1).
    CoreExpr dv; dv.kind = Kind::Div; dv.sort = f.intS;
    dv.children.push_back(x); dv.children.push_back(f.cint(3));
    ExprId divv = f.ir.add(std::move(dv));
    CoreExpr md; md.kind = Kind::Mod; md.sort = f.intS;
    md.children.push_back(x); md.children.push_back(f.cint(3));
    ExprId modv = f.ir.add(std::move(md));
    ExprId a1 = f.bin(Kind::Eq, divv, f.cint(2), f.boolS);
    ExprId a2 = f.bin(Kind::Eq, modv, f.cint(1), f.boolS);

    ArithModelValidator::NumAssignment num{{"x", 7}};
    ArithModelValidator v(f.ir, num, {});
    // Must be Satisfied — a rational-division reading of `div` would wrongly
    // report Violated (7/3 ≠ 2).
    CHECK(v.validate({a1, a2}) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("ArithModelValidator: indeterminate on uninterpreted function") {
    Fix f;
    // (= (f x) 3) — UFApply is unsupported → indeterminate, not Violated
    ExprId fsym = f.var("f", f.intS);
    ExprId x = f.var("x", f.intS);
    CoreExpr app; app.kind = Kind::UFApply; app.sort = f.intS;
    app.children.push_back(fsym); app.children.push_back(x);
    app.payload = Payload(std::string("f"));
    ExprId fa = f.ir.add(std::move(app));
    ExprId eq = f.bin(Kind::Eq, fa, f.cint(3), f.boolS);

    ArithModelValidator::NumAssignment num{{"x", 1}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({eq}) == ArithModelValidator::Verdict::Indeterminate);
}
