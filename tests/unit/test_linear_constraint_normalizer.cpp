#include <doctest/doctest.h>
#include "algebra/linear/LinearConstraintNormalizer.h"
#include "search/lra/DeltaRational.h"
#include <stdexcept>

using namespace xolver;

namespace {
bool relationTrue(Relation relation, const mpq_class& lhs, const mpq_class& rhs) {
    switch (relation) {
        case Relation::Eq: return lhs == rhs;
        case Relation::Neq: return lhs != rhs;
        case Relation::Leq: return lhs <= rhs;
        case Relation::Lt: return lhs < rhs;
        case Relation::Geq: return lhs >= rhs;
        case Relation::Gt: return lhs > rhs;
    }
    throw std::logic_error("invalid arithmetic relation");
}

mpq_class evaluate(const LinearFormKey& form, const mpq_class& x, const mpq_class& y) {
    mpq_class result;
    for (const auto& [name, coefficient] : form.terms)
        result += coefficient * (name == "x" ? x : name == "y" ? y : mpq_class(0));
    return result;
}
}

TEST_CASE("Primitive linear normalization: rational content and integer lattice endpoints") {
    for (const auto sort : {SortKind::Int, SortKind::Real}) {
        LinearFormKey form{{{"y", mpq_class(-4, 9)}, {"x", mpq_class(2, 3)},
                            {"y", mpq_class(1, 9)}}};
        auto relation = Relation::Geq;
        mpq_class rhs(5, 6);
        LinearConstraintNormalizer::normalizePrimitiveConstraint(form, relation, rhs, sort);
        CHECK(form == LinearFormKey{{{"x", 2}, {"y", -1}}});
        CHECK(relation == Relation::Geq);
        CHECK(rhs == (sort == SortKind::Int ? mpq_class(3) : mpq_class(5, 2)));
    }
}

TEST_CASE("Primitive linear normalization: exact truth on integer and rational assignments") {
    const mpq_class coefficients[] = {mpq_class(-3), mpq_class(-1, 2), 0, mpq_class(2, 3), 4};
    const mpq_class second[] = {mpq_class(-2, 5), 0, mpq_class(5, 6)};
    const mpq_class endpoints[] = {mpq_class(-7, 3), -1, 0, mpq_class(2, 7), 6};
    for (const auto sort : {SortKind::Int, SortKind::Real})
        for (const auto relation : {Relation::Eq, Relation::Neq, Relation::Leq,
                                    Relation::Lt, Relation::Geq, Relation::Gt})
            for (const auto& a : coefficients) for (const auto& b : second)
                for (const auto& endpoint : endpoints) {
                    const LinearFormKey original{{{"y", b}, {"x", a}, {"x", mpq_class(1, 7)},
                                                  {"x", mpq_class(-1, 7)}, {"z", 0}}};
                    auto form = original;
                    auto effective = relation;
                    auto rhs = endpoint;
                    LinearConstraintNormalizer::normalizePrimitiveConstraint(form, effective, rhs, sort);
                    for (int x = -3; x <= 3; ++x) for (int y = -3; y <= 3; ++y) {
                        mpq_class xv(x, sort == SortKind::Int ? 1 : 3);
                        mpq_class yv(y, sort == SortKind::Int ? 1 : 4);
                        xv.canonicalize();
                        yv.canonicalize();
                        CHECK(relationTrue(relation, evaluate(original, xv, yv), endpoint) ==
                              relationTrue(effective, evaluate(form, xv, yv), rhs));
                    }
                    for (const auto& term : form.terms) CHECK(term.second.get_den() == 1);
                    auto again = form;
                    auto nextRelation = effective;
                    auto nextRhs = rhs;
                    LinearConstraintNormalizer::normalizePrimitiveConstraint(again, nextRelation, nextRhs, sort);
                    CHECK(again == form);
                    CHECK(nextRelation == effective);
                    CHECK(nextRhs == rhs);
                }
}

TEST_CASE("Primitive linear normalization: large common factors do not control cut admission") {
    const mpz_class factor = mpz_class(1) << 2000;
    LinearFormKey form{{{"x", mpq_class(3 * factor, 7)}, {"y", mpq_class(-9 * factor, 7)}}};
    mpq_class rhs(6 * factor + 1, 7);
    auto relation = Relation::Geq;
    LinearConstraintNormalizer::normalizePrimitiveConstraint(form, relation, rhs, SortKind::Int);
    CHECK(form == LinearFormKey{{{"x", 1}, {"y", -3}}});
    CHECK(relation == Relation::Geq);
    CHECK(rhs == 3);
}

TEST_CASE("Primitive linear normalization: sign and nonintegral equality remain exact") {
    LinearFormKey form{{{"x", mpq_class(-7, 11)}}};
    mpq_class rhs(14, 33);
    auto relation = Relation::Geq;
    LinearConstraintNormalizer::normalizePrimitiveConstraint(form, relation, rhs, SortKind::Int);
    CHECK(form == LinearFormKey{{{"x", 1}}});
    CHECK(relation == Relation::Leq);
    CHECK(rhs == -1);
    for (const auto equality : {Relation::Eq, Relation::Neq}) {
        form = LinearFormKey{{{"x", 2}}}; rhs = 1; relation = equality;
        LinearConstraintNormalizer::normalizePrimitiveConstraint(form, relation, rhs, SortKind::Int);
        CHECK(form == LinearFormKey{{{"x", 1}}});
        CHECK(relation == equality);
        CHECK(rhs == mpq_class(1, 2));
    }
}

TEST_CASE("Primitive linear normalization: unsupported sorts leave inputs intact") {
    LinearFormKey form{{{"x", 2}}};
    auto relation = Relation::Leq;
    mpq_class rhs(3);
    CHECK_THROWS_AS(LinearConstraintNormalizer::normalizePrimitiveConstraint(
        form, relation, rhs, SortKind::Bool), std::invalid_argument);
    CHECK(form == LinearFormKey{{{"x", 2}}});
    CHECK(relation == Relation::Leq);
    CHECK(rhs == 3);
}

TEST_CASE("Primitive linear normalization: real strict endpoints preserve infinitesimals") {
    LinearFormKey form{{{"x", mpq_class(-2, 3)}}};
    auto relation = Relation::Lt;
    mpq_class rhs(1, 5);
    LinearConstraintNormalizer::normalizePrimitiveConstraint(form, relation, rhs, SortKind::Real);
    CHECK(form == LinearFormKey{{{"x", 1}}});
    CHECK(relation == Relation::Gt);
    CHECK(rhs == mpq_class(-3, 10));
    for (const int epsilon : {-1, 0, 1}) {
        const DeltaRational point(mpq_class(-3, 10), epsilon);
        CHECK((mpq_class(-2, 3) * point < DeltaRational(mpq_class(1, 5))) ==
              (point > DeltaRational(rhs)));
    }
}

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
