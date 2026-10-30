#include <doctest/doctest.h>
#include "search/refute/PolynomialLinearRefutation.h"
#include "search/refute/PolynomialBooleanRefutation.h"
#include <algorithm>

using namespace xolver;

namespace {
auto deadline() { return std::chrono::steady_clock::now() + std::chrono::seconds(1); }
auto variable(VarId id) { return RationalPolynomial::fromVar(id, 1, 1); }
auto constant(const mpq_class& value) { return RationalPolynomial::fromConstant(value); }
}

TEST_CASE("Polynomial linear refutation: coupled inequalities explain a nonlinear context conflict") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    const std::vector<SignRefuteConstraint> constraints{
        {x + y - constant(1), Relation::Geq, SatLit::positive(1)},
        {y + z, Relation::Leq, SatLit::negative(2)},
        {x - z, Relation::Leq, SatLit::positive(3)},
        {x * y - constant(2), Relation::Eq, SatLit::positive(4)}};
    PolynomialLinearStatistics stats;
    auto conflict = refutePolynomialLinearRelaxation(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    for (size_t i = 0; i < 3; ++i)
        CHECK(std::find(conflict->begin(), conflict->end(), constraints[i].reason) != conflict->end());
    CHECK(stats.constraints == 4);
    CHECK(stats.variables == 4);
    CHECK_FALSE(stats.exhausted);
}

TEST_CASE("Polynomial linear refutation: strict rational bounds remain exact and open relaxations are not SAT") {
    const auto x = variable(0), y = variable(1);
    const mpz_class numerator = (mpz_class(1) << 130) + 7;
    const auto form = x * constant(mpq_class(numerator, mpz_class(3))) + y - constant(2);
    std::vector<SignRefuteConstraint> constraints{
        {form, Relation::Geq, SatLit::positive(1)},
        {form, Relation::Lt, SatLit::positive(2)}};
    CHECK(refutePolynomialLinearRelaxation(constraints, deadline()).has_value());
    const mpz_class denominator = numerator * 3;
    const mpq_class tiny(mpz_class(1), denominator);
    constraints[1].poly -= constant(tiny);
    CHECK_FALSE(refutePolynomialLinearRelaxation(constraints, deadline()).has_value());
    CHECK_FALSE(refutePolynomialLinearRelaxation({{x * x + constant(1), Relation::Eq, SatLit::positive(1)}}, deadline()));
    CHECK_FALSE(refutePolynomialLinearRelaxation({
        {x, Relation::Eq, SatLit::positive(1)},
        {x, Relation::Neq, SatLit::positive(2)}}, deadline()));
    PolynomialLinearStatistics stats;
    CHECK_FALSE(refutePolynomialLinearRelaxation(constraints, std::chrono::steady_clock::now(), &stats));
    CHECK(stats.exhausted);
}

TEST_CASE("Polynomial linear refutation: Boolean arithmetic closes linear and nonlinear cores") {
    for (auto sort : {SortKind::Int, SortKind::Real}) {
        for (bool nonlinear : {false, true}) {
            NativeTerms terms;
            terms.registerSort(0, sort);
            terms.registerSort(1, SortKind::Bool);
            terms.setBoolSortId(1);
            auto op = [&](Kind kind, std::initializer_list<ExprId> children, SortId result) {
                TermExpr expression{kind, result, {}, {}};
                for (auto child : children) expression.children.push_back(child);
                return terms.add(std::move(expression));
            };
            auto numeral = [&](int64_t value) { return terms.add({Kind::ConstInt, 0, {}, Payload(value)}); };
            const auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
            const auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
            const auto z = terms.add({Kind::Variable, 0, {}, Payload(std::string("z"))});
            const auto t = terms.add({Kind::Variable, 0, {}, Payload(std::string("t"))});
            const auto a = nonlinear ? op(Kind::Mul, {x, t}, 0) : x;
            const auto b = nonlinear ? op(Kind::Mul, {y, t}, 0) : y;
            const auto c = nonlinear ? op(Kind::Mul, {z, t}, 0) : z;
            std::vector<ExprId> roots{
                op(Kind::Geq, {op(Kind::Add, {a, b}, 0), numeral(1)}, 1),
                op(Kind::Leq, {op(Kind::Add, {b, c}, 0), numeral(0)}, 1),
                op(Kind::Leq, {op(Kind::Sub, {a, c}, 0), numeral(0)}, 1),
                op(Kind::Eq, {op(Kind::Mul, {t, t}, 0), numeral(4)}, 1)};
            BooleanRefutationLimits limits;
            limits.deadline = deadline();
            PolynomialBooleanStatistics stats;
            CHECK(refutePolynomialBoolean(terms, roots, limits, &stats));
            CHECK(stats.linearCalls == 1);
            CHECK(stats.signExhaustions == 0);
        }
    }
}

TEST_CASE("Polynomial linear refutation: shared canonical products explain strict conflicts") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    const auto p = x * y, q = x * z, r = y * z;
    const std::vector<SignRefuteConstraint> constraints{
        {p + q, Relation::Gt, SatLit::negative(1)},
        {z * x + r, Relation::Leq, SatLit::positive(2)},
        {y * x - r, Relation::Leq, SatLit::positive(3)}};
    PolynomialLinearStatistics stats;
    const auto conflict = refutePolynomialLinearRelaxation(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    for (const auto& constraint : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), constraint.reason) != conflict->end());
    CHECK(stats.variables == 3);
    CHECK_FALSE(stats.exhausted);

    const auto square = x * x * y;
    CHECK(refutePolynomialLinearRelaxation({
        {square - constant(mpq_class(2, 3)), Relation::Eq, SatLit::positive(1)},
        {y * x * x - constant(mpq_class(2, 3)), Relation::Lt, SatLit::positive(2)}}, deadline()));
    // A relaxed monomial may disagree with the product of the base columns.
    // That must remain open, even though the original equations are UNSAT.
    CHECK_FALSE(refutePolynomialLinearRelaxation({
        {p - x, Relation::Eq, SatLit::positive(1)},
        {x - constant(1), Relation::Eq, SatLit::positive(2)},
        {y - constant(2), Relation::Eq, SatLit::positive(3)}}, deadline()));
}
