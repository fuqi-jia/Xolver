#include <doctest/doctest.h>
#include "evidence/ArithModelValidator.h"
#include "ir/NativeTerms.h"

using namespace xolver;

namespace {
struct Fix {
    NativeTerms ir;
    SortId boolS, intS, realS;
    Fix() {
        boolS = ir.allocateSortId(); ir.registerSort(boolS, SortKind::Bool); ir.setBoolSortId(boolS);
        intS  = ir.allocateSortId(); ir.registerSort(intS, SortKind::Int);   ir.setIntSortId(intS);
        realS = ir.allocateSortId(); ir.registerSort(realS, SortKind::Real);  ir.setRealSortId(realS);
    }
    ExprId var(const std::string& n, SortId s) {
        return ir.add(TermExpr{Kind::Variable, s, {}, Payload(n)});
    }
    ExprId cint(int64_t v) { return ir.add(TermExpr{Kind::ConstInt, intS, {}, Payload(v)}); }
    ExprId bin(Kind k, ExprId a, ExprId b, SortId s) {
        TermExpr e; e.kind = k; e.sort = s; e.children.push_back(a); e.children.push_back(b);
        return ir.add(std::move(e));
    }
};
}

TEST_CASE("ArithModelValidator: integer zero extensions are explicit model data") {
    Fix f;
    auto x = f.var("x", f.intS);
    auto zero = f.cint(0);
    auto div = f.bin(Kind::Div, x, zero, f.intS);
    auto mod = f.bin(Kind::Mod, x, zero, f.intS);
    auto divGoal = f.bin(Kind::Eq, div, f.cint(5), f.boolS);
    auto modGoal = f.bin(Kind::Eq, mod, f.cint(-3), f.boolS);
    ArithModelValidator validator(f.ir, {{"x", 2}}, {});
    CHECK(validator.validate({divGoal}) == ArithModelValidator::Verdict::Indeterminate);
    ArithModelValidator::IntegerZeroTable divTable{{mpq_class(2), mpq_class(5)}};
    ArithModelValidator::IntegerZeroTable modTable{{mpq_class(2), mpq_class(-3)}};
    validator.setIntegerZeroExtensions(&divTable, &modTable);
    CHECK(validator.validate({divGoal, modGoal}) == ArithModelValidator::Verdict::Satisfied);
    divTable[2] = 6;
    validator.setIntegerZeroExtensions(&divTable, &modTable);
    CHECK(validator.validate({divGoal}) == ArithModelValidator::Verdict::Violated);
    divTable[2] = mpq_class(1, 2);
    validator.setIntegerZeroExtensions(&divTable, &modTable);
    CHECK(validator.validate({divGoal}) == ArithModelValidator::Verdict::Indeterminate);
    auto realZero = f.ir.add(TermExpr{Kind::ConstReal, f.realS, {}, Payload(std::string("0"))});
    auto realDiv = f.bin(Kind::Div, realZero, realZero, f.realS);
    CHECK_FALSE(validator.evalNumber(realDiv));
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
    TermExpr d; d.kind = Kind::Distinct; d.sort = f.boolS;
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

TEST_CASE("ArithModelValidator: UFApply evaluated via function interpretation") {
    Fix f;
    ExprId x = f.var("x", f.intS);
    // (f x): UFApply "f" over Int.
    TermExpr app; app.kind = Kind::UFApply; app.sort = f.intS;
    app.children.push_back(x); app.payload = Payload(std::string("f"));
    ExprId fx = f.ir.add(std::move(app));
    ExprId a1 = f.bin(Kind::Eq, fx, f.cint(5), f.boolS);  // (= (f x) 5)

    ArithModelValidator::NumAssignment num{{"x", 2}};
    ArithModelValidator::FuncInterpMap interps;
    TheoryModel::FuncInterp fi;
    fi.argSorts = {"Int"}; fi.retSort = "Int"; fi.deflt = "0";
    fi.entries.push_back({{"2"}, "5"});  // f(2) = 5
    interps["f"] = fi;

    SUBCASE("with matching interp -> satisfied") {
        ArithModelValidator v(f.ir, num, {});
        v.setFunctionInterps(&interps);
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Satisfied);
    }
    SUBCASE("no interp -> indeterminate (never Violated)") {
        ArithModelValidator v(f.ir, num, {});
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Indeterminate);
    }
    SUBCASE("wrong interp value -> violated") {
        interps["f"].entries[0].value = "7";  // f(2)=7 != 5
        ArithModelValidator v(f.ir, num, {});
        v.setFunctionInterps(&interps);
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Violated);
    }
    SUBCASE("an opaque numeric result is not a concrete value") {
        interps["f"].entries[0].value = "@unresolved";
        ArithModelValidator v(f.ir, num, {});
        v.setFunctionInterps(&interps);
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Indeterminate);
    }
    SUBCASE("a fractional integer result is not a typed model") {
        interps["f"].entries[0].value = "3/2";
        ArithModelValidator v(f.ir, num, {});
        v.setFunctionInterps(&interps);
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Indeterminate);
    }
    SUBCASE("arg not in table -> default value") {
        ArithModelValidator::NumAssignment num2{{"x", 9}};  // f(9) -> deflt "0"
        ArithModelValidator v(f.ir, num2, {});
        v.setFunctionInterps(&interps);
        // (= (f 9) 5) with f(9)=deflt=0 -> 0 != 5 -> Violated
        CHECK(v.validate({a1}) == ArithModelValidator::Verdict::Violated);
    }
}

TEST_CASE("ArithModelValidator: Int div/mod use Euclidean semantics") {
    Fix f;
    ExprId x = f.var("x", f.intS);
    // (= (div x 3) 2) ∧ (= (mod x 3) 1) — x=7 satisfies (7/3=2, 7%3=1).
    TermExpr dv; dv.kind = Kind::Div; dv.sort = f.intS;
    dv.children.push_back(x); dv.children.push_back(f.cint(3));
    ExprId divv = f.ir.add(std::move(dv));
    TermExpr md; md.kind = Kind::Mod; md.sort = f.intS;
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
    TermExpr app; app.kind = Kind::UFApply; app.sort = f.intS;
    app.children.push_back(fsym); app.children.push_back(x);
    app.payload = Payload(std::string("f"));
    ExprId fa = f.ir.add(std::move(app));
    ExprId eq = f.bin(Kind::Eq, fa, f.cint(3), f.boolS);

    ArithModelValidator::NumAssignment num{{"x", 1}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({eq}) == ArithModelValidator::Verdict::Indeterminate);
}


TEST_CASE("ArithModelValidator: shared-expression evaluation distinguishes all three verdicts") {
    Fix f;
    ExprId x = f.var("x", f.intS), y = f.var("y", f.intS);
    ExprId sum = f.bin(Kind::Add, x, y, f.intS);
    ExprId satA = f.bin(Kind::Eq, sum, f.cint(5), f.boolS);    // x+y=5
    ExprId vioA = f.bin(Kind::Eq, sum, f.cint(9), f.boolS);    // x+y=9 (false at 3,2)
    ExprId indetA = f.bin(Kind::Geq, f.var("z", f.intS), f.cint(0), f.boolS);  // z unassigned

    ArithModelValidator::NumAssignment num{{"x", 3}, {"y", 2}};
    auto verdict = [&](ExprId a) {
        ArithModelValidator v(f.ir, num, {});
        return v.validate({a});
    };
    // Memo must not change the verdict for any of the three outcomes.
    CHECK(verdict(satA)   == ArithModelValidator::Verdict::Satisfied);
    CHECK(verdict(vioA)   == ArithModelValidator::Verdict::Violated);
    CHECK(verdict(indetA) == ArithModelValidator::Verdict::Indeterminate);
}

TEST_CASE("ArithModelValidator: eval memo prevents shared-DAG blowup") {
    Fix f;
    // n = x doubled 50 times: a 50-node DAG whose tree unfolding is 2^50.
    // Without the memo this evaluation is infeasible; with it, it is O(50), so
    // this test completing at all is the proof the memo collapses the DAG.
    ExprId n = f.var("x", f.intS);
    for (int i = 0; i < 50; ++i) n = f.bin(Kind::Add, n, n, f.intS);
    ExprId assertion = f.bin(Kind::Geq, n, f.cint(0), f.boolS);  // x*2^50 >= 0

    ArithModelValidator::NumAssignment num{{"x", 1}};
    ArithModelValidator v(f.ir, num, {});
    CHECK(v.validate({assertion}) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("ArithModelValidator: deep shared roots stay exact across model updates") {
    Fix f;
    ExprId n = f.var("x", f.intS);
    constexpr unsigned depth = 2048;
    for (unsigned i = 0; i < depth; ++i)
        n = f.bin(Kind::Add, n, n, f.intS);
    mpz_class expected = 1;
    mpz_mul_2exp(expected.get_mpz_t(), expected.get_mpz_t(), depth);
    const auto value = f.ir.add({Kind::ConstInt, f.intS, {}, Payload(expected.get_str())});
    const auto goal = f.bin(Kind::Eq, n, value, f.boolS);
    ArithModelValidator::RealAssignment numbers{{"x", RealValue::fromMpq(mpq_class(1))}};
    ArithModelValidator::BoolAssignment booleans;
    ArithModelValidator validator(f.ir, {}, booleans);
    validator.setRealAssignments(&numbers);

    CHECK(validator.validate({goal, goal}) == ArithModelValidator::Verdict::Satisfied);
    REQUIRE(validator.evalNumber(n));
    CHECK(*validator.evalNumber(n) == mpq_class(expected));
    numbers["x"] = RealValue::fromMpq(mpq_class(-1));
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Violated);
    CHECK(*validator.evalNumber(n) == -mpq_class(expected));
    numbers.erase("x");
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Indeterminate);
    CHECK_FALSE(validator.evalNumber(n));
    numbers["x"] = RealValue::fromMpq(mpq_class(1));
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("ArithModelValidator: shared array versions remain independent across cached reads") {
    Fix f;
    const auto arraySort = f.ir.allocateSortId();
    f.ir.registerArraySort(arraySort, f.intS, f.intS);
    const auto zero = f.cint(0), index = f.cint(1);
    const auto five = f.cint(5), nine = f.cint(9);
    const auto base = f.ir.add({Kind::ConstArray, arraySort, {zero}, {}});
    const auto first = f.ir.add({Kind::Store, arraySort, {base, index, five}, {}});
    const auto second = f.ir.add({Kind::Store, arraySort, {base, index, nine}, {}});
    const auto readBase = f.bin(Kind::Select, base, index, f.intS);
    const auto readFirst = f.bin(Kind::Select, first, index, f.intS);
    const auto readSecond = f.bin(Kind::Select, second, index, f.intS);
    const auto allDifferent = f.ir.add({Kind::Distinct, f.boolS, {base, first, second}, {}});
    const std::vector<ExprId> assertions{
        f.bin(Kind::Eq, readBase, zero, f.boolS),
        f.bin(Kind::Eq, readFirst, five, f.boolS),
        f.bin(Kind::Eq, readSecond, nine, f.boolS), allDifferent};
    ArithModelValidator validator(f.ir, {}, {});

    CHECK(validator.validate(assertions) == ArithModelValidator::Verdict::Satisfied);
    const auto saved = validator.evalNumber(readFirst);
    REQUIRE(saved);
    CHECK(validator.evalNumber(readSecond) == mpq_class(9));
    CHECK(validator.evalNumber(readBase) == mpq_class(0));
    CHECK(*saved == 5);
    CHECK(validator.validate({f.bin(Kind::Eq, readBase, five, f.boolS)}) ==
          ArithModelValidator::Verdict::Violated);
    CHECK(validator.validate(assertions) == ArithModelValidator::Verdict::Satisfied);
}

TEST_CASE("ArithModelValidator: mixed UF cache values are rebuilt after model changes") {
    Fix f;
    const auto arraySort = f.ir.allocateSortId();
    f.ir.registerArraySort(arraySort, f.intS, f.intS);
    const auto tokenSort = f.ir.allocateSortId();
    f.ir.registerSort(tokenSort, SortKind::Other);
    const auto array = f.var("array", arraySort);
    const auto number = f.var("number", f.realS);
    const auto flag = f.var("flag", f.boolS);
    const auto tag = f.var("tag", tokenSort);
    const auto application = f.ir.add({Kind::UFApply, f.intS,
        {array, number, flag, tag}, Payload(std::string("mixed"))});
    const auto sum = f.bin(Kind::Add, application, application, f.intS);
    const auto goal = f.bin(Kind::Eq, sum, f.cint(22), f.boolS);

    ArithModelValidator::ArrayAssignment arrays, values;
    arrays["array"] = {"Int", "Int", "#n:0", {{"#n:1", "#n:7"}}};
    values["@expected"] = arrays["array"];
    ArithModelValidator::RealAssignment numbers{
        {"number", RealValue::fromMpq(mpq_class(3, 2))}};
    ArithModelValidator::TokenAssignment tokens{{"tag", "@tag-a"}};
    ArithModelValidator::FuncInterpMap functions;
    auto& function = functions["mixed"];
    function.argSorts = {"(Array Int Int)", "Real", "Bool", "Element"};
    function.retSort = "Int";
    function.deflt = "0";
    function.entries = {{{"@expected", "3/2", "true", "@tag-a"}, "11"}};
    ArithModelValidator validator(f.ir, {}, {{"flag", true}}, arrays, tokens);
    validator.setRealAssignments(&numbers);
    validator.setFunctionInterps(&functions, &values);

    CHECK(validator.validate({goal, goal}) == ArithModelValidator::Verdict::Satisfied);
    const auto savedNumber = validator.evalNumber(sum);
    const auto savedToken = validator.evalToken(sum);
    REQUIRE(savedNumber);
    REQUIRE(savedToken);
    function.entries.front().value = "12";
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Violated);
    CHECK(validator.evalNumber(sum) == mpq_class(24));
    CHECK(*savedNumber == 22);
    CHECK(*savedToken == "#n:22");

    numbers.erase("number");
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Indeterminate);
    CHECK_FALSE(validator.evalToken(sum));
    numbers["number"] = RealValue::fromMpq(mpq_class(3, 2));
    function.entries.front().value = "11";
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Satisfied);
    arrays["array"].entries.front().second = "#n:8";
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Violated);
    arrays["array"].entries.front().second = "#n:7";
    tokens["tag"] = "@tag-b";
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Violated);
    tokens["tag"] = "@tag-a";
    CHECK(validator.validate({goal}) == ArithModelValidator::Verdict::Satisfied);
}
