#include <doctest/doctest.h>
#include "theory/arith/linear/LinearExpr.h"
#include "expr/ir.h"

// Directly exercises extractLinearExpr's n-ary handling of Sub/Mul/Div.
// The production frontend (SOMTParser) binarizes these, so end-to-end .smt2
// tests never feed n-ary nodes here; these build the CoreExpr nodes by hand to
// lock in the variadic contract (so linearization does not silently depend on
// the frontend's binarization).

using namespace xolver;

namespace {

struct Builder {
    CoreIr ir;
    ExprId cint(int64_t v) { CoreExpr e; e.kind = Kind::ConstInt; e.payload = Payload(v); return ir.add(std::move(e)); }
    ExprId creal(std::string s) { CoreExpr e; e.kind = Kind::ConstReal; e.payload = Payload(std::move(s)); return ir.add(std::move(e)); }
    ExprId var(std::string n) { CoreExpr e; e.kind = Kind::Variable; e.payload = Payload(std::move(n)); return ir.add(std::move(e)); }
    ExprId op(Kind k, std::vector<ExprId> ch) {
        CoreExpr e; e.kind = k;
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
