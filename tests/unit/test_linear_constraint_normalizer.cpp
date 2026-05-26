#include <doctest/doctest.h>
#include "theory/arith/linear/LinearConstraintNormalizer.h"

using namespace zolver;

TEST_CASE("LinearConstraintNormalizer: canonicalize merges and sorts") {
    LinearExpr e;
    e.constant = 3;
    e.terms.push_back({"y", mpq_class(2)});
    e.terms.push_back({"x", mpq_class(1)});
    e.terms.push_back({"y", mpq_class(-2)}); // cancels with first y
    e.terms.push_back({"z", mpq_class(0)});  // zero coeff dropped

    auto c = LinearConstraintNormalizer::canonicalize(e);
    CHECK(c.constant == 3);
    REQUIRE(c.terms.size() == 1);
    CHECK(c.terms[0].var == "x");
    CHECK(c.terms[0].coeff == 1);
}

TEST_CASE("LinearConstraintNormalizer: __nl_aux_0 - 4 = 0 -> __nl_aux_0 = 4") {
    ZeroLinearConstraint z;
    z.expr.constant = -4;
    z.expr.terms.push_back({"__nl_aux_0", mpq_class(1)});
    z.rel = Relation::Eq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Eq);
    CHECK(a.rhs == mpq_class(4));
    REQUIRE(a.lhs.terms.size() == 1);
    CHECK(a.lhs.terms[0].first == "__nl_aux_0");
    CHECK(a.lhs.terms[0].second == 1);
}

TEST_CASE("LinearConstraintNormalizer: __nl_aux_0 + 4 = 0 -> __nl_aux_0 = -4") {
    ZeroLinearConstraint z;
    z.expr.constant = 4;
    z.expr.terms.push_back({"__nl_aux_0", mpq_class(1)});
    z.rel = Relation::Eq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Eq);
    CHECK(a.rhs == mpq_class(-4));
}

TEST_CASE("LinearConstraintNormalizer: -__nl_aux_0 - 4 <= 0 -> -__nl_aux_0 <= 4") {
    ZeroLinearConstraint z;
    z.expr.constant = -4;
    z.expr.terms.push_back({"__nl_aux_0", mpq_class(-1)});
    z.rel = Relation::Leq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Leq);
    CHECK(a.rhs == mpq_class(4));
    REQUIRE(a.lhs.terms.size() == 1);
    CHECK(a.lhs.terms[0].first == "__nl_aux_0");
    CHECK(a.lhs.terms[0].second == -1);
}

TEST_CASE("LinearConstraintNormalizer: -__nl_aux_0 <= 0 (square nonneg)") {
    ZeroLinearConstraint z;
    z.expr.constant = 0;
    z.expr.terms.push_back({"__nl_aux_0", mpq_class(-1)});
    z.rel = Relation::Leq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Leq);
    CHECK(a.rhs == mpq_class(0));
    CHECK(a.lhs.terms[0].second == -1);
}

TEST_CASE("LinearConstraintNormalizer: x + y - 10 <= 0 -> x + y <= 10") {
    ZeroLinearConstraint z;
    z.expr.constant = -10;
    z.expr.terms.push_back({"x", mpq_class(1)});
    z.expr.terms.push_back({"y", mpq_class(1)});
    z.rel = Relation::Leq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Leq);
    CHECK(a.rhs == mpq_class(10));
    REQUIRE(a.lhs.terms.size() == 2);
    CHECK(a.lhs.terms[0].first == "x");
    CHECK(a.lhs.terms[1].first == "y");
}

TEST_CASE("LinearConstraintNormalizer: x + y + 10 <= 0 -> x + y <= -10") {
    ZeroLinearConstraint z;
    z.expr.constant = 10;
    z.expr.terms.push_back({"x", mpq_class(1)});
    z.expr.terms.push_back({"y", mpq_class(1)});
    z.rel = Relation::Leq;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rhs == mpq_class(-10));
}

TEST_CASE("LinearConstraintNormalizer: Int strict x < 4 -> x <= 3") {
    ZeroLinearConstraint z;
    z.expr.constant = -4;
    z.expr.terms.push_back({"x", mpq_class(1)});
    z.rel = Relation::Lt;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Leq);
    CHECK(a.rhs == mpq_class(3));
}

TEST_CASE("LinearConstraintNormalizer: Int strict x > 4 -> x >= 5") {
    ZeroLinearConstraint z;
    z.expr.constant = -4;
    z.expr.terms.push_back({"x", mpq_class(1)});
    z.rel = Relation::Gt;
    z.sort = SortKind::Int;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Geq);
    CHECK(a.rhs == mpq_class(5));
}

TEST_CASE("LinearConstraintNormalizer: Real strict x < 4 unchanged") {
    ZeroLinearConstraint z;
    z.expr.constant = -4;
    z.expr.terms.push_back({"x", mpq_class(1)});
    z.rel = Relation::Lt;
    z.sort = SortKind::Real;

    auto a = LinearConstraintNormalizer::toLinearAtomSpec(z);
    CHECK(a.rel == Relation::Lt);
    CHECK(a.rhs == mpq_class(4));
}

TEST_CASE("LinearConstraintNormalizer: effective false assignment x <= 4 -> x >= 5 (Int)") {
    LinearAtomPayload payload;
    payload.lhs.terms.push_back({"x", mpq_class(1)});
    payload.rel = Relation::Leq;
    payload.rhs = RealValue::fromInt(4);

    auto opt = LinearConstraintNormalizer::makeEffectiveConstraint(payload, false, SortKind::Int);
    REQUIRE(opt.has_value());
    auto a = LinearConstraintNormalizer::toLinearAtomSpec(*opt);
    CHECK(a.rel == Relation::Geq);
    CHECK(a.rhs == mpq_class(5));
}

TEST_CASE("LinearConstraintNormalizer: effective false assignment x = 4 -> nullopt (diseq)") {
    LinearAtomPayload payload;
    payload.lhs.terms.push_back({"x", mpq_class(1)});
    payload.rel = Relation::Eq;
    payload.rhs = RealValue::fromInt(4);

    auto opt = LinearConstraintNormalizer::makeEffectiveConstraint(payload, false, SortKind::Int);
    CHECK(!opt.has_value());
}

TEST_CASE("LinearConstraintNormalizer: effective true assignment x <= 4 unchanged") {
    LinearAtomPayload payload;
    payload.lhs.terms.push_back({"x", mpq_class(1)});
    payload.rel = Relation::Leq;
    payload.rhs = RealValue::fromInt(4);

    auto opt = LinearConstraintNormalizer::makeEffectiveConstraint(payload, true, SortKind::Int);
    REQUIRE(opt.has_value());
    auto a = LinearConstraintNormalizer::toLinearAtomSpec(*opt);
    CHECK(a.rel == Relation::Leq);
    CHECK(a.rhs == mpq_class(4));
}
