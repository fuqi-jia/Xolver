#include <doctest/doctest.h>
#include "algebra/linear/LinearExpr.h"
#include "ir/NativeTerms.h"
#include <set>

// Directly exercises extractLinearExpr's n-ary handling of Sub/Mul/Div.
// The production frontend (SOMTParser) binarizes these, so end-to-end .smt2
// tests never feed n-ary nodes here; these build the TermExpr nodes by hand to
// lock in the variadic contract (so linearization does not silently depend on
// the frontend's binarization).

using namespace xolver;

namespace {

struct Builder {
    NativeTerms ir;
    Builder() { ir.registerSort(0, SortKind::Int); ir.registerSort(1, SortKind::Real); }
    ExprId cint(int64_t v) { TermExpr e; e.kind = Kind::ConstInt; e.sort = 0; e.payload = Payload(v); return ir.add(std::move(e)); }
    ExprId creal(std::string s) { TermExpr e; e.kind = Kind::ConstReal; e.sort = 1; e.payload = Payload(std::move(s)); return ir.add(std::move(e)); }
    ExprId var(std::string n) { TermExpr e; e.kind = Kind::Variable; e.sort = 1; e.payload = Payload(std::move(n)); return ir.add(std::move(e)); }
    ExprId op(Kind k, std::vector<ExprId> ch) {
        TermExpr e; e.kind = k; e.sort = 1;
        for (ExprId c : ch) e.children.push_back(c);
        return ir.add(std::move(e));
    }
};

} // namespace

TEST_CASE("extractLinearExpr: n-ary Mul (* 2 3 x) == 6x") {
    Builder b;
    ExprId mul = b.op(Kind::Mul, {b.cint(2), b.cint(3), b.var("x")});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(mul, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs["x"] == mpq_class(6));
    CHECK(constant == 0);
}

TEST_CASE("extractLinearExpr: n-ary Mul all-const (* 2 3 4) == 24") {
    Builder b;
    ExprId mul = b.op(Kind::Mul, {b.cint(2), b.cint(3), b.cint(4)});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(mul, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs.empty());
    CHECK(constant == mpq_class(24));
}

TEST_CASE("extractLinearExpr: n-ary Mul with two vars (* x y) is nonlinear") {
    Builder b;
    ExprId mul = b.op(Kind::Mul, {b.var("x"), b.var("y")});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    CHECK_FALSE(extractLinearExpr(mul, b.ir, coeffs, constant, mpq_class(1)));
}

TEST_CASE("extractLinearExpr: n-ary Sub (- 20 a b) == 20 - a - b") {
    Builder b;
    ExprId sub = b.op(Kind::Sub, {b.cint(20), b.var("a"), b.var("b")});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(sub, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs["a"] == mpq_class(-1));
    CHECK(coeffs["b"] == mpq_class(-1));
    CHECK(constant == mpq_class(20));
}

TEST_CASE("extractLinearExpr: unary Sub (- x) == -x") {
    Builder b;
    ExprId sub = b.op(Kind::Sub, {b.var("x")});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(sub, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs["x"] == mpq_class(-1));
}

TEST_CASE("extractLinearExpr: n-ary Div (/ x 2 2) == x/4") {
    Builder b;
    ExprId div = b.op(Kind::Div, {b.var("x"), b.cint(2), b.cint(2)});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(div, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs["x"] == (mpq_class(1)/4));
    CHECK(constant == 0);
}

TEST_CASE("extractLinearExpr: Div by constant of a sum (/ (+ x y) 2)") {
    Builder b;
    ExprId sum = b.op(Kind::Add, {b.var("x"), b.var("y")});
    ExprId div = b.op(Kind::Div, {sum, b.cint(2)});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    REQUIRE(extractLinearExpr(div, b.ir, coeffs, constant, mpq_class(1)));
    CHECK(coeffs["x"] == (mpq_class(1)/2));
    CHECK(coeffs["y"] == (mpq_class(1)/2));
}

TEST_CASE("extractLinearExpr: Div by zero is rejected") {
    Builder b;
    ExprId div = b.op(Kind::Div, {b.var("x"), b.cint(0)});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    CHECK_FALSE(extractLinearExpr(div, b.ir, coeffs, constant, mpq_class(1)));
}

TEST_CASE("extractLinearExpr: Div by a variable (/ x y) is nonlinear") {
    Builder b;
    ExprId div = b.op(Kind::Div, {b.var("x"), b.var("y")});
    std::unordered_map<std::string, mpq_class> coeffs;
    mpq_class constant = 0;
    CHECK_FALSE(extractLinearExpr(div, b.ir, coeffs, constant, mpq_class(1)));
}

namespace {
auto differenceForm(std::initializer_list<std::pair<std::string, mpq_class>> terms,
                    mpq_class rhs) {
    return std::pair{LinearFormKey{terms}, std::move(rhs)};
}
}

TEST_CASE("Integer difference cover: rational scales and noncanonical forms") {
    std::vector forms{
        differenceForm({{"x", mpq_class(1, 2)}, {"y", mpq_class(-1, 2)}}, mpq_class(3, 4)),
        differenceForm({{"x", -3}}, 1)};
    CHECK(integerDifferenceCoverRadius(forms) == std::optional<mpz_class>(6));
    forms = {differenceForm({{"x", 3}, {"y", -2}, {"x", -1}, {"unused", 0}}, 3)};
    CHECK(integerDifferenceCoverRadius(forms) == std::optional<mpz_class>(6));
    forms = {differenceForm({{"x", 3}, {"x", -3}}, 100)};
    CHECK(integerDifferenceCoverRadius(forms) == std::optional<mpz_class>(0));
    const mpz_class large = (mpz_class(1) << 200) + 1;
    forms = {differenceForm({{"x", 1}}, mpq_class(large, 2))};
    CHECK(integerDifferenceCoverRadius(forms) == std::optional<mpz_class>((large + 1) / 2 + 1));
    forms = {differenceForm({{"x", 1}, {"y", -2}}, 0)};
    CHECK_FALSE(integerDifferenceCoverRadius(forms).has_value());
    forms = {differenceForm({{"x", 1}, {"y", 1}, {"z", 1}}, 0)};
    CHECK_FALSE(integerDifferenceCoverRadius(forms).has_value());
}

TEST_CASE("Integer difference cover: signs must be consistent across every atom") {
    std::vector forms{
        differenceForm({{"x", 1}, {"y", 1}}, 0),
        differenceForm({{"y", 1}, {"z", 1}}, 1),
        differenceForm({{"x", 1}, {"z", -1}}, 2)};
    CHECK(integerDifferenceCoverRadius(forms) == std::optional<mpz_class>(9));
    forms.push_back(differenceForm({{"x", 1}, {"z", 1}}, 0));
    CHECK_FALSE(integerDifferenceCoverRadius(forms).has_value());
    forms = {differenceForm({{"a", -7}, {"b", -7}}, 0),
             differenceForm({{"c", 2}, {"d", -2}}, 0),
             differenceForm({{"a", 1}, {"c", 1}}, 0),
             differenceForm({{"b", -3}, {"d", -3}}, 0)};
    CHECK_FALSE(integerDifferenceCoverRadius(forms).has_value());
}

TEST_CASE("Integer difference cover: every feasible atom sign pattern has a bounded witness") {
    const std::vector forms{differenceForm({{"x", 2}, {"y", -2}}, 4),
                           differenceForm({{"x", -3}}, 0)};
    const auto radius = integerDifferenceCoverRadius(forms);
    REQUIRE(radius == std::optional<mpz_class>(6));
    auto sign = [](int value) { return (value > 0) - (value < 0); };
    auto pattern = [&](int x, int y) { return std::pair{sign(2*x - 2*y - 4), sign(-3*x)}; };
    std::set<std::pair<int, int>> bounded;
    for (int x = -6; x <= 6; ++x)
        for (int y = -6; y <= 6; ++y) bounded.insert(pattern(x, y));
    REQUIRE(bounded.size() == 9);
    for (int x = -20; x <= 20; ++x)
        for (int y = -20; y <= 20; ++y) CHECK(bounded.contains(pattern(x, y)));
}
