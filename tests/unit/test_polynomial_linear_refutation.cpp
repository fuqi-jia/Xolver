#include <doctest/doctest.h>
#include "search/refute/PolynomialLinearRefutation.h"
#include "search/refute/PolynomialBooleanRefutation.h"
#include "search/nra/simplex/NraLinearExtractor.h"
#include "search/nra/simplex/SimplexTableauFacts.h"
#include <algorithm>
#include <random>

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
    auto conflict = PolynomialLinearRefuter{}.check(constraints, deadline(), &stats);
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
    CHECK(PolynomialLinearRefuter{}.check(constraints, deadline()).has_value());
    const mpz_class denominator = numerator * 3;
    const mpq_class tiny(mpz_class(1), denominator);
    constraints[1].poly -= constant(tiny);
    CHECK_FALSE(PolynomialLinearRefuter{}.check(constraints, deadline()).has_value());
    CHECK_FALSE(PolynomialLinearRefuter{}.check({{x * x + constant(1), Relation::Eq, SatLit::positive(1)}}, deadline()));
    CHECK_FALSE(PolynomialLinearRefuter{}.check({
        {x, Relation::Eq, SatLit::positive(1)},
        {x, Relation::Neq, SatLit::positive(2)}}, deadline()));
    PolynomialLinearStatistics stats;
    CHECK_FALSE(PolynomialLinearRefuter{}.check(constraints, std::chrono::steady_clock::now(), &stats));
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
    const auto conflict = PolynomialLinearRefuter{}.check(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    for (const auto& constraint : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), constraint.reason) != conflict->end());
    CHECK(stats.variables == 3);
    CHECK_FALSE(stats.exhausted);

    const auto square = x * x * y;
    CHECK(PolynomialLinearRefuter{}.check({
        {square - constant(mpq_class(2, 3)), Relation::Eq, SatLit::positive(1)},
        {y * x * x - constant(mpq_class(2, 3)), Relation::Lt, SatLit::positive(2)}}, deadline()));
    // A relaxed monomial may disagree with the product of the base columns.
    // That must remain open, even though the original equations are UNSAT.
    CHECK_FALSE(PolynomialLinearRefuter{}.check({
        {p - x, Relation::Eq, SatLit::positive(1)},
        {x - constant(1), Relation::Eq, SatLit::positive(2)},
        {y - constant(2), Relation::Eq, SatLit::positive(3)}}, deadline()));
}

TEST_CASE("Polynomial linear refutation: cached definitions survive withdrawal but their premises do not") {
    PolynomialLinearRefuter refuter;
    const auto product = variable(0) * variable(1);
    std::vector<SignRefuteConstraint> constraints{
        {product, Relation::Geq, SatLit::positive(1)},
        {product, Relation::Lt, SatLit::positive(2)}};
    PolynomialLinearStatistics stats;
    REQUIRE(refuter.check(constraints, deadline(), &stats));
    CHECK(stats.newRows == 2);
    CHECK(stats.reusedRows == 0);
    constraints[0].rel = Relation::Lt;
    constraints[0].reason = SatLit::negative(1);
    CHECK_FALSE(refuter.check(constraints, deadline(), &stats));
    CHECK(stats.newRows == 0);
    CHECK(stats.reusedRows == 2);
    CHECK(stats.retainedRows == 2);
    constraints.erase(constraints.begin());
    CHECK_FALSE(refuter.check(constraints, deadline()));
    CHECK_FALSE(refuter.check({}, deadline()));
    constraints = {{product, Relation::Gt, SatLit::positive(3)},
                   {product, Relation::Leq, SatLit::negative(2)}};
    const auto conflict = refuter.check(constraints, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
    for (auto literal : *conflict)
        CHECK((literal == SatLit::positive(3) || literal == SatLit::negative(2)));
    CHECK_FALSE(refuter.check(constraints, std::chrono::steady_clock::now(), &stats));
    CHECK(stats.exhausted);
    CHECK_FALSE(refuter.check({constraints[0]}, deadline()));
    refuter.reset();
    CHECK_FALSE(refuter.check({}, deadline(), &stats));
    CHECK(stats.retainedRows == 0);
    CHECK(stats.variables == 0);
}

TEST_CASE("Polynomial linear refutation: source identity cannot alias a changed polynomial") {
    PolynomialLinearRefuter refuter;
    const auto x = variable(0);
    std::vector<SignRefuteConstraint> constraints{
        {x, Relation::Geq, SatLit::positive(1)},
        {x - constant(1), Relation::Leq, SatLit::positive(2)}};
    CHECK_FALSE(refuter.check(constraints, deadline()));
    constraints[0].poly = x - constant(2);
    REQUIRE(refuter.check(constraints, deadline()));
    constraints[0].poly = x;
    CHECK_FALSE(refuter.check(constraints, deadline()));
    // Two distinct definitions can carry the same conjunction premise.
    // Their columns must remain distinct despite the shared source identity.
    CHECK_FALSE(refuter.check({
        {x - constant(1), Relation::Eq, SatLit::positive(4)},
        {variable(1) - constant(2), Relation::Eq, SatLit::positive(4)}}, deadline()));
}

TEST_CASE("Polynomial linear refutation: reused branch contexts and their conflicts match fresh monomial systems") {
    auto kernel = createPolynomialKernel();
    const auto xid = kernel->getOrCreateVar("x"), yid = kernel->getOrCreateVar("y");
    const auto x = variable(xid), y = variable(yid);
    const std::unordered_map<VarId, mpq_class> point{{xid, mpq_class(1, 3)}, {yid, mpq_class(-2, 5)}};
    std::vector<RationalPolynomial> polynomials;
    for (int i = 0; i < 12; ++i) {
        auto p = constant(i % 3 - 1) * x * x + constant(i - 5) * x * y +
                 constant(i % 5 - 2) * y + x;
        p -= constant(p.evaluateRational(point));
        polynomials.push_back(std::move(p));
    }
    auto freshConflict = [&](const std::vector<SignRefuteConstraint>& constraints) {
        std::vector<CdcacConstraint> native;
        for (const auto& c : constraints) {
            CdcacConstraint item;
            item.poly = c.poly.toPolyId(*kernel);
            item.rel = c.rel;
            item.reason = c.reason;
            native.push_back(std::move(item));
        }
        return computeSimplexTableauFacts(linearizeMonomials(*kernel, native)).linearSubsetUnsat();
    };
    PolynomialLinearRefuter refuter;
    std::minstd_rand random(298990);
    for (int step = 0; step < 160; ++step) {
        CAPTURE(step);
        std::vector<SignRefuteConstraint> constraints;
        for (size_t i = 0; i < polynomials.size(); ++i) {
            if (random() % 3 == 0) continue;
            const auto rel = (random() % 2) ? Relation::Geq : Relation::Leq;
            constraints.push_back({polynomials[i], rel, SatLit(static_cast<SatVar>(i + 1), random() % 2)});
        }
        const bool inconsistent = random() % 4 == 0;
        if (inconsistent) {
            constraints.push_back({x * y, Relation::Gt, SatLit::positive(20)});
            constraints.push_back({x * y, Relation::Leq, SatLit::negative(21)});
        }
        std::shuffle(constraints.begin(), constraints.end(), random);
        REQUIRE(freshConflict(constraints) == inconsistent);
        const auto conflict = refuter.check(constraints, deadline());
        REQUIRE(conflict.has_value() == inconsistent);
        if (conflict) {
            std::vector<SignRefuteConstraint> premises;
            for (auto literal : *conflict) {
                const auto found = std::find_if(constraints.begin(), constraints.end(),
                    [&](const auto& c) { return c.reason == literal; });
                REQUIRE(found != constraints.end());
                premises.push_back(*found);
            }
            CHECK(freshConflict(premises));
        }
    }
}
