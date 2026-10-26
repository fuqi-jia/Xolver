#include <doctest/doctest.h>
#include "frontend/preprocess/IntDivModConstantFold.h"
#include <gmpxx.h>

using namespace xolver;

namespace {
struct ResidueTerms {
    NativeTerms ir;
    SortId boolean, integer;
    ExprId x;
    ResidueTerms() {
        boolean = ir.allocateSortId(); ir.registerSort(boolean, SortKind::Bool); ir.setBoolSortId(boolean);
        integer = ir.allocateSortId(); ir.registerSort(integer, SortKind::Int); ir.setIntSortId(integer);
        x = ir.add(TermExpr{Kind::Variable, integer, {}, Payload(std::string("x"))});
    }
    ExprId constant(int64_t value) {
        return ir.add(TermExpr{Kind::ConstInt, integer, {}, Payload(value)});
    }
    ExprId op(Kind kind, ExprId a, ExprId b) {
        return ir.add(TermExpr{kind, integer, {a, b}, {}});
    }
    ExprId fold(ExprId expression) {
        ir.addAssertion(ir.add(TermExpr{Kind::Eq, boolean, {expression, constant(0)}, {}}));
        IntDivModConstantFold pass(ir);
        REQUIRE(pass.run());
        pass.commit();
        return ir.get(ir.assertions().back()).children[0];
    }
    void checkConstant(ExprId expression, int64_t expected) {
        const auto result = fold(expression);
        REQUIRE(ir.get(result).kind == Kind::ConstInt);
        REQUIRE(std::holds_alternative<int64_t>(ir.get(result).payload.value));
        CHECK(std::get<int64_t>(ir.get(result).payload.value) == expected);
    }
};
}

TEST_CASE("IntDivModConstantFold: falling factorials have constant residues") {
    // A product of n consecutive integers is divisible by n!, for all
    // integer inputs. Exercise both divisor signs and nonzero output residues.
    int64_t factorial = 1;
    for (int n = 2; n <= 5; ++n) {
        factorial *= n;
        for (int sign : {-1, 1}) {
            ResidueTerms t;
            auto product = t.x;
            for (int i = 1; i < n; ++i)
                product = t.op(Kind::Mul, product, t.op(Kind::Sub, t.x, t.constant(i)));
            const auto shifted = t.op(Kind::Add, product, t.constant(-1));
            auto expression = t.op(Kind::Mod, shifted, t.constant(sign * factorial));
            t.checkConstant(expression, factorial - 1);
        }
    }
}

TEST_CASE("IntDivModConstantFold: polynomial residue identities preserve exponents") {
    ResidueTerms t;
    const auto square = t.op(Kind::Pow, t.x, t.constant(2));
    t.checkConstant(t.op(Kind::Mod, t.op(Kind::Sub, square, t.x), t.constant(2)), 0);
    const auto cube = t.op(Kind::Pow, t.x, t.constant(3));
    t.checkConstant(t.op(Kind::Mod, t.op(Kind::Sub, cube, t.x), t.constant(3)), 0);
    t.checkConstant(t.op(Kind::Mod, t.op(Kind::Pow, t.x, t.constant(0)), t.constant(2)), 1);

    auto polynomial = t.constant(0);
    for (const auto [coefficient, exponent] : {std::pair{6,5}, {10,6}, {1,2}, {7,4}})
        polynomial = t.op(Kind::Add, polynomial,
            t.op(Kind::Mul, t.constant(coefficient), t.op(Kind::Pow, t.x, t.constant(exponent))));
    t.checkConstant(t.op(Kind::Mod, polynomial, t.constant(12)), 0);
}

TEST_CASE("IntDivModConstantFold: nonconstant and unsupported residue functions stay intact") {
    ResidueTerms t;
    const auto square = t.op(Kind::Pow, t.x, t.constant(2));
    for (auto expression : {
             t.op(Kind::Mod, square, t.constant(2)),
             t.op(Kind::Mod, square, t.constant(0)),
             t.op(Kind::Mod, square, t.constant(1000000007)),
             t.op(Kind::Mod, t.op(Kind::Pow, t.x, t.constant(-2)), t.constant(2)),
             t.op(Kind::Mod, t.op(Kind::Pow, t.x, t.x), t.constant(2)),
             t.op(Kind::Mod, t.op(Kind::Div, t.x, t.constant(2)), t.constant(2))})
        CHECK(t.fold(expression) == expression);
    // Distinct variable nodes cannot be identified merely by their spelling.
    auto other = t.ir.add(TermExpr{Kind::Variable, t.integer, {}, Payload(std::string("x"))});
    auto twoVariables = t.op(Kind::Mod, t.op(Kind::Sub, t.x, other), t.constant(2));
    CHECK(t.fold(twoVariables) == twoVariables);
}

TEST_CASE("IntDivModConstantFold: large coefficients and shared DAGs") {
    ResidueTerms t;
    auto huge = t.ir.add(TermExpr{Kind::ConstInt, t.integer, {},
        Payload(std::string("1234567890123456789012345678901234567890"))});
    auto consecutive = t.op(Kind::Mul, t.x, t.op(Kind::Sub, t.x, t.constant(1)));
    t.checkConstant(t.op(Kind::Mod, t.op(Kind::Add, consecutive, huge), t.constant(-2)), 0);
    auto shared = t.x;
    for (int i = 0; i < 100; ++i) shared = t.op(Kind::Add, shared, shared);
    t.checkConstant(t.op(Kind::Mod, shared, t.constant(2)), 0);
}

TEST_CASE("IntDivModConstantFold: optional work exhaustion preserves assertions and scope") {
    ResidueTerms t;
    auto large = t.x;
    for (int i = 0; i < 16000; ++i) large = t.op(Kind::Add, large, t.constant(2));
    auto expression = t.op(Kind::Mod, large, t.constant(2));
    auto assertion = t.ir.add(TermExpr{Kind::Eq, t.boolean, {expression, t.constant(1)}, {}});
    t.ir.addAssertion(assertion, 3);
    auto small = t.op(Kind::Mod, t.constant(-5), t.constant(-3));
    auto literal = t.ir.add(TermExpr{Kind::Eq, t.boolean, {small, t.constant(1)}, {}});
    t.ir.addAssertion(literal, 4);
    IntDivModConstantFold pass(t.ir);
    REQUIRE(pass.run());
    pass.commit();
    const auto& assertions = t.ir.getScopedAssertions();
    REQUIRE(assertions.size() == 2);
    CHECK(assertions[0].first == 3);
    CHECK(assertions[0].second == assertion);
    CHECK(assertions[1].first == 4);
    const auto result = t.ir.get(assertions[1].second).children[0];
    CHECK(std::get<int64_t>(t.ir.get(result).payload.value) == 1);
}

TEST_CASE("IntDivModConstantFold: symbolic zero divisors preserve their function interpretation") {
    ResidueTerms t;
    for (auto expression : {t.op(Kind::Mod, t.x, t.x),
                            t.op(Kind::Mod, t.constant(0), t.x)}) {
        auto folded = t.fold(expression);
        REQUIRE(t.ir.get(folded).kind == Kind::Mod);
        CHECK(t.ir.get(folded).children[1] == t.x);
        CHECK(std::get<int64_t>(t.ir.get(t.ir.get(folded).children[0]).payload.value) == 0);
    }
    auto nested = t.op(Kind::Mod, t.op(Kind::Mod, t.constant(7), t.x), t.x);
    auto folded = t.fold(nested);
    REQUIRE(t.ir.get(folded).kind == Kind::Mod);
    CHECK(t.ir.get(t.ir.get(folded).children[0]).kind == Kind::Mod);
}

TEST_CASE("IntDivModConstantFold: wide distribution survives term storage growth") {
    ResidueTerms t;
    TermExpr sum; sum.kind = Kind::Add; sum.sort = t.integer;
    for (int i = 0; i < 5000; ++i)
        sum.children.push_back(t.ir.add(TermExpr{Kind::Variable, t.integer, {},
            Payload(std::string("y") + std::to_string(i))}));
    auto multiple = t.op(Kind::Mul, t.x, t.ir.add(std::move(sum)));
    auto folded = t.fold(t.op(Kind::Mod, multiple, t.x));
    REQUIRE(t.ir.get(folded).kind == Kind::Mod);
    CHECK(t.ir.get(folded).children[1] == t.x);
    CHECK(std::get<int64_t>(t.ir.get(t.ir.get(folded).children[0]).payload.value) == 0);
}
