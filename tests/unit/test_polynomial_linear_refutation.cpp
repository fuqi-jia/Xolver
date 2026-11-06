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

TEST_CASE("Multiplied relaxation: even monomial factors transport exact polynomial order") {
    const auto x = variable(0), y = variable(1), s = variable(2), t = variable(3);
    const auto factor = s * s * t * t;
    std::vector<SignRefuteConstraint> constraints{
        {(x - y) * constant(mpq_class(2, 3)), Relation::Geq, SatLit::negative(101)},
        {factor * y - constant(1), Relation::Geq, SatLit::positive(503)},
        {factor * x, Relation::Leq, SatLit::negative(9001)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    const auto conflict = refuter.check(constraints, deadline(), &stats);
    REQUIRE(conflict);
    for (const auto& source : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    // Removing the transported order leaves x=0, y=s=t=1 as a witness.
    constraints.erase(constraints.begin());
    CHECK_FALSE(refuter.check(constraints, deadline()));
}

TEST_CASE("Multiplied relaxation: equality transport needs no multiplier sign assumption") {
    const auto x = variable(0), y = variable(1), s = variable(2), t = variable(3);
    const auto factor = s * t;
    std::vector<SignRefuteConstraint> constraints{
        {x - y, Relation::Eq, SatLit::negative(11)},
        {factor * y - constant(1), Relation::Geq, SatLit::positive(31)},
        {factor * x, Relation::Leq, SatLit::negative(71)}};
    PolynomialLinearRefuter refuter;
    const auto conflict = refuter.check(constraints, deadline());
    REQUIRE(conflict);
    for (const auto& source : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    // The order alone permits a negative multiplier and reverses the products.
    constraints[0].rel = Relation::Geq;
    CHECK_FALSE(refuter.check(constraints, deadline()));
    const std::unordered_map<VarId, mpq_class> point{{0, 0}, {1, -1}, {2, -1}, {3, 1}};
    CHECK(constraints[0].poly.evaluateRational(point) >= 0);
    CHECK(constraints[1].poly.evaluateRational(point) >= 0);
    CHECK(constraints[2].poly.evaluateRational(point) <= 0);
}

TEST_CASE("Multiplied relaxation: strictness retains nonzero factor premises after withdrawal") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints{
        {x - y, Relation::Gt, SatLit::negative(17)},
        {z, Relation::Geq, SatLit::positive(37)},
        {z * x - z * y, Relation::Leq, SatLit::negative(97)}};
    PolynomialLinearRefuter refuter;
    CHECK_FALSE(refuter.check(constraints, deadline())); // z=0 remains admissible.
    constraints[1].rel = Relation::Gt;
    const auto conflict = refuter.check(constraints, deadline());
    REQUIRE(conflict);
    for (const auto& source : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    constraints[1].rel = Relation::Leq;
    constraints[1].reason = SatLit::negative(37);
    CHECK_FALSE(refuter.check(constraints, deadline()));
    refuter.reset();
    CHECK_FALSE(refuter.check(constraints, deadline()));
}

TEST_CASE("Multiplied relaxation: signed upper orders and cancellation preserve caller context") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints{
        {(x - y) * constant(mpq_class(7, 5)), Relation::Leq, SatLit::negative(41)},
        {z, Relation::Geq, SatLit::positive(43)},
        {z * x - z * y, Relation::Gt, SatLit::negative(47)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    CHECK_FALSE(refuter.check(constraints, std::chrono::steady_clock::now(), &stats));
    CHECK(stats.exhausted);
    const auto conflict = refuter.check(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK_FALSE(stats.exhausted);
    for (const auto& source : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    constraints[0].rel = Relation::Geq;
    CHECK_FALSE(refuter.check(constraints, deadline()));
    PolynomialLinearRefuter limited(1);
    CHECK_FALSE(limited.check(constraints, deadline(), &stats));
    CHECK(stats.exhausted);
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

TEST_CASE("Proved polynomial facts: coupled bounds export zeros with original signed premises") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints{
        {x, Relation::Geq, SatLit::positive(101)},
        {y, Relation::Geq, SatLit::negative(503)},
        {z, Relation::Geq, SatLit::positive(9001)},
        {x * y + z, Relation::Leq, SatLit::negative(10007)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    std::vector<PolynomialConsequence> facts;
    REQUIRE_FALSE(refuter.check(constraints, deadline(), &stats, &facts));
    REQUIRE(facts.size() == 1);
    CHECK(stats.fixedMonomials == 1);
    CHECK(stats.zeroMonomials == 1);
    const auto fact = facts.front();
    CHECK(fact.rel == Relation::Eq);
    CHECK(fact.poly.terms() == (x * y).terms());
    REQUIRE(fact.premises.size() == 4);
    for (const auto& source : constraints)
        CHECK(std::find(fact.premises.begin(), fact.premises.end(), source.reason) != fact.premises.end());
    const auto holds = [](const SignRefuteConstraint& source,
                          const std::unordered_map<VarId, mpq_class>& point) {
        const auto value = source.poly.evaluateRational(point);
        return source.rel == Relation::Geq ? value >= 0 : value <= 0;
    };
    for (int a = -2; a <= 2; ++a) for (int b = -2; b <= 2; ++b) for (int c = -2; c <= 2; ++c) {
        const std::unordered_map<VarId, mpq_class> point{{0, mpq_class(a, 3)},
            {1, mpq_class(b, 3)}, {2, mpq_class(c, 3)}};
        if (std::all_of(constraints.begin(), constraints.end(), [&](const auto& source) {
                return holds(source, point);
            })) CHECK(fact.poly.evaluateRational(point) == 0);
    }
    constraints[1].rel = Relation::Lt;
    constraints[1].reason = SatLit::positive(503);
    REQUIRE_FALSE(refuter.check(constraints, deadline(), &stats, &facts));
    CHECK(facts.empty());
    CHECK(stats.zeroMonomials == 0);
    constraints[1].rel = Relation::Geq;
    constraints[1].reason = SatLit::negative(503);
    refuter.reset();
    REQUIRE_FALSE(refuter.check(constraints, deadline(), &stats, &facts));
    CHECK(facts.size() == 1);
}

TEST_CASE("Proved polynomial facts: fractional fixed values stay exact and point zeros are not proofs") {
    const auto x = variable(0), y = variable(1);
    std::vector<SignRefuteConstraint> constraints{
        {x * y - constant(mpq_class(1, 3)), Relation::Eq, SatLit::negative(1001)},
        {x, Relation::Geq, SatLit::positive(4001)},
        {y, Relation::Geq, SatLit::positive(9001)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    std::vector<PolynomialConsequence> facts;
    REQUIRE_FALSE(refuter.check(constraints, deadline(), &stats, &facts));
    REQUIRE(facts.size() == 1);
    CHECK(facts.front().poly.terms() == constraints.front().poly.terms());
    CHECK(stats.fixedMonomials == 1);
    CHECK(stats.zeroMonomials == 0);
    CHECK(std::find(facts.front().premises.begin(), facts.front().premises.end(),
                    constraints.front().reason) != facts.front().premises.end());
    constraints.front().poly = x * y;
    constraints.front().rel = Relation::Geq;
    refuter.reset();
    REQUIRE_FALSE(refuter.check(constraints, deadline(), &stats, &facts));
    WorkBudget work;
    const auto candidate = refuter.projectCandidate(constraints, work);
    REQUIRE(candidate);
    CHECK((x * y).evaluateRational(*candidate) == 0);
    CHECK(facts.empty());
    CHECK(stats.fixedMonomials == 0);
    const std::unordered_map<VarId, mpq_class> other{{0, 1}, {1, 1}};
    CHECK((x * y).evaluateRational(other) > 0);
}

TEST_CASE("Proved polynomial facts: conflict and exhausted checks discard earlier exported context") {
    const auto x = variable(0), y = variable(1);
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    std::vector<PolynomialConsequence> facts{{x * y, Relation::Eq, {SatLit::positive(777)}}};
    CHECK(refuter.check({{x, Relation::Geq, SatLit::positive(101)},
        {x, Relation::Lt, SatLit::negative(503)}}, deadline(), &stats, &facts));
    CHECK(facts.empty());
    facts.push_back({x * y, Relation::Eq, {SatLit::positive(777)}});
    CHECK_FALSE(refuter.check({{x * y, Relation::Eq, SatLit::positive(101)}},
        std::chrono::steady_clock::now() - std::chrono::milliseconds(1), &stats, &facts));
    CHECK(stats.exhausted);
    CHECK(facts.empty());
    CHECK(stats.fixedMonomials == 0);
    refuter.reset();
    CHECK_FALSE(refuter.check({{x * y - constant(2), Relation::Eq, SatLit::positive(503)}},
        deadline(), &stats, &facts));
    REQUIRE(facts.size() == 1);
    CHECK(facts.front().poly.terms() == (x * y - constant(2)).terms());
}

TEST_CASE("Polynomial relaxation projection preserves exact infinitesimals and current variables") {
    const auto x = variable(0), y = variable(1);
    const mpq_class width(1, mpz_class(1) << 256);
    const mpq_class upper = 1 + width;
    std::vector<SignRefuteConstraint> constraints{
        {x - constant(1), Relation::Gt, SatLit::positive(1)},
        {x - constant(upper), Relation::Lt, SatLit::positive(2)},
        {x * x - constant(1), Relation::Gt, SatLit::positive(3)}};
    PolynomialLinearRefuter refuter;
    REQUIRE_FALSE(refuter.check(constraints, deadline()));
    WorkBudget work(10000);
    const auto projected = refuter.projectCandidate(constraints, work);
    REQUIRE(projected);
    REQUIRE(projected->size() == 1);
    CHECK(projected->at(0) > 1);
    CHECK(projected->at(0) < upper);
    CHECK((x * x - constant(1)).evaluateRational(*projected) > 0);

    constraints = {{y - constant(3), Relation::Geq, SatLit::positive(4)}};
    REQUIRE_FALSE(refuter.check(constraints, deadline()));
    WorkBudget next(10000);
    const auto current = refuter.projectCandidate(constraints, next);
    REQUIRE(current);
    REQUIRE(current->size() == 1);
    CHECK_FALSE(current->contains(0));
    CHECK(current->at(1) >= 3);
    WorkBudget exhausted(1);
    CHECK_FALSE(refuter.projectCandidate(constraints, exhausted));
}

TEST_CASE("Polynomial relaxation projection is not a nonlinear or integer satisfiability claim") {
    const auto x = variable(0);
    const std::vector<SignRefuteConstraint> constraints{
        {x * x - constant(2), Relation::Eq, SatLit::positive(1)}};
    PolynomialLinearRefuter refuter;
    REQUIRE_FALSE(refuter.check(constraints, deadline()));
    WorkBudget work(10000);
    const auto point = refuter.projectCandidate(constraints, work);
    REQUIRE(point);
    CHECK(point->at(0) == 0);
    CHECK(constraints[0].poly.evaluateRational(*point) != 0);
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
    CHECK(PolynomialLinearRefuter{}.check({{x * x + constant(1), Relation::Eq, SatLit::positive(1)}}, deadline()));
    CHECK(PolynomialLinearRefuter{}.check({
        {x, Relation::Eq, SatLit::positive(1)},
        {x, Relation::Neq, SatLit::positive(2)}}, deadline()));
    PolynomialLinearStatistics stats;
    CHECK_FALSE(PolynomialLinearRefuter{}.check(constraints, std::chrono::steady_clock::now(), &stats));
    CHECK(stats.exhausted);
}

TEST_CASE("Polynomial linear disequalities use explained fixed values rather than candidate points") {
    const auto x = variable(0), y = variable(1);
    const std::vector<SignRefuteConstraint> constraints{
        {x + y - constant(3), Relation::Eq, SatLit::negative(1)},
        {x - y - constant(1), Relation::Eq, SatLit::positive(2)},
        {x * constant(5) - y * constant(2) - constant(8), Relation::Neq, SatLit::negative(3)},
        {variable(2), Relation::Geq, SatLit::positive(4)}};
    auto conflict = PolynomialLinearRefuter{}.check(constraints, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    for (size_t i = 0; i < 3; ++i)
        CHECK(std::find(conflict->begin(), conflict->end(), constraints[i].reason) != conflict->end());

    const mpq_class tiny(1, mpz_class(1) << 180);
    PolynomialLinearRefuter refuter;
    CHECK_FALSE(refuter.check({
        {x, Relation::Geq, SatLit::positive(1)},
        {x, Relation::Neq, SatLit::negative(2)}}, deadline()));
    CHECK_FALSE(refuter.check({
        {x, Relation::Gt, SatLit::positive(1)},
        {x - constant(tiny), Relation::Lt, SatLit::positive(3)},
        {x, Relation::Neq, SatLit::negative(2)}}, deadline()));
    CHECK_FALSE(refuter.check({
        {x - constant(tiny), Relation::Eq, SatLit::positive(1)},
        {x, Relation::Neq, SatLit::negative(2)}}, deadline()));
    conflict = refuter.check({
        {x - constant(mpq_class(2, 3)), Relation::Eq, SatLit::positive(1)},
        {x * constant(mpq_class(-3, 7)) + constant(mpq_class(2, 7)),
            Relation::Neq, SatLit::negative(2)}}, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
}

TEST_CASE("Polynomial linear disequalities follow exact product closure and premise withdrawal") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    const SignRefuteConstraint excluded{x * y + x * z, Relation::Neq, SatLit::negative(2)};
    PolynomialLinearRefuter refuter;
    const auto conflict = refuter.check({
        {x, Relation::Eq, SatLit::positive(1)}, excluded}, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
    CHECK(std::find(conflict->begin(), conflict->end(), excluded.reason) != conflict->end());
    CHECK_FALSE(refuter.check({excluded}, deadline()));
    CHECK_FALSE(refuter.check({
        {x - constant(1), Relation::Eq, SatLit::positive(1)},
        {y - constant(1), Relation::Eq, SatLit::positive(3)},
        {z, Relation::Eq, SatLit::positive(4)}, excluded}, deadline()));
    CHECK(refuter.check({
        {x * y + x * z, Relation::Eq, SatLit::positive(2)}, excluded}, deadline()));
    CHECK_FALSE(refuter.check({excluded}, deadline()));
    refuter.reset();
    CHECK_FALSE(refuter.check({excluded}, deadline()));
    PolynomialLinearStatistics stats;
    CHECK_FALSE(refuter.check({excluded}, std::chrono::steady_clock::now(), &stats));
    CHECK(stats.exhausted);
}

TEST_CASE("Polynomial linear disequality endpoints preserve exact rational coefficients") {
    const auto x = variable(0);
    PolynomialLinearRefuter refuter;
    for (int numerator = -4; numerator <= 4; ++numerator) {
        mpq_class value(numerator, 3);
        value.canonicalize();
        for (int sign : {-1, 1}) for (int offset = -1; offset <= 1; ++offset) {
            CAPTURE(numerator);
            CAPTURE(sign);
            CAPTURE(offset);
            const mpq_class scale(sign * 5, 7);
            const auto excluded = x * constant(scale) - constant(scale * value) + constant(offset);
            const auto conflict = refuter.check({
                {x - constant(value), Relation::Eq, SatLit::positive(1)},
                {excluded, Relation::Neq, SatLit::negative(2)}}, deadline());
            CHECK(conflict.has_value() == (offset == 0));
        }
    }
}

TEST_CASE("Polynomial monomial signs refute a coupled zero sum and retain every active premise") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> sources{
        {x, Relation::Geq, SatLit::positive(1)},
        {y, Relation::Geq, SatLit::negative(2)},
        {z, Relation::Geq, SatLit::positive(3)},
        {x * y + y * z, Relation::Leq, SatLit::positive(4)},
        {x * y, Relation::Neq, SatLit::negative(5)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics statistics;
    auto conflict = refuter.check(sources, deadline(), &statistics);
    REQUIRE(conflict);
    CHECK(statistics.signFacts >= 2);
    // The tight face proves the excluded product value directly, so neither
    // strict alternative needs a temporary feasibility check.
    CHECK(statistics.disequalityChecks == 0);
    for (const auto& source : sources)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    const auto removed = sources[2];
    sources.erase(sources.begin() + 2);
    CHECK_FALSE(refuter.check(sources, deadline()));
    sources.push_back(removed);
    CHECK(refuter.check(sources, deadline()));
}

TEST_CASE("Polynomial monomial signs preserve even powers and strict signed factors") {
    const auto x = variable(0), y = variable(1);
    PolynomialLinearRefuter refuter;
    const auto product = x * x * y;
    auto conflict = refuter.check({
        {y, Relation::Geq, SatLit::positive(1)},
        {product, Relation::Lt, SatLit::negative(2)}}, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
    CHECK_FALSE(refuter.check({{product, Relation::Lt, SatLit::negative(2)}}, deadline()));
    conflict = refuter.check({
        {x, Relation::Lt, SatLit::positive(1)},
        {y, Relation::Gt, SatLit::positive(2)},
        {x * y, Relation::Geq, SatLit::negative(3)}}, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    CHECK_FALSE(refuter.check({
        {x, Relation::Leq, SatLit::positive(1)},
        {y, Relation::Gt, SatLit::positive(2)},
        {x * y, Relation::Eq, SatLit::negative(3)}}, deadline()));
    CHECK(refuter.check({{x * x + constant(1), Relation::Eq, SatLit::positive(4)}}, deadline()));
    CHECK_FALSE(refuter.check({}, deadline()));
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
    // Exact fixed base values now justify an explained product identity.
    CHECK(PolynomialLinearRefuter{}.check({
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
    CHECK(stats.newRows == 0); // Direct monomial bounds need no slack definitions.
    CHECK(stats.reusedRows == 0);
    constraints[0].rel = Relation::Lt;
    constraints[0].reason = SatLit::negative(1);
    CHECK_FALSE(refuter.check(constraints, deadline(), &stats));
    CHECK(stats.newRows == 0);
    CHECK(stats.reusedRows == 2);
    CHECK(stats.retainedRows == 0);
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

TEST_CASE("Polynomial linear refutation: direct monomial endpoints preserve exact signed strict bounds") {
    const auto product = variable(0) * variable(1);
    const mpq_class point((mpz_class(1) << 130) + 7, mpz_class(3));
    const mpq_class width(1, mpz_class(1) << 256);
    for (const mpq_class& coefficient : {mpq_class(1, 3), mpq_class(-2, 7)}) {
        PolynomialLinearRefuter refuter;
        std::vector<SignRefuteConstraint> sources{
            {(product - constant(point)) * constant(coefficient),
                coefficient > 0 ? Relation::Gt : Relation::Lt, SatLit::negative(1)},
            {product - constant(point + width), Relation::Lt, SatLit::positive(2)}};
        CHECK_FALSE(refuter.check(sources, deadline()));
        sources[1].poly = product - constant(point);
        sources[1].rel = Relation::Leq;
        const auto conflict = refuter.check(sources, deadline());
        REQUIRE(conflict);
        REQUIRE(conflict->size() == 2);
        for (auto literal : *conflict)
            CHECK((literal == sources[0].reason || literal == sources[1].reason));
        sources.erase(sources.begin());
        CHECK_FALSE(refuter.check(sources, deadline()));
    }
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

TEST_CASE("Polynomial linear refutation: constant disequalities retain their exact verdict") {
    PolynomialLinearRefuter refuter;
    CHECK_FALSE(refuter.check({{constant(1), Relation::Neq, SatLit::positive(8)}}, deadline()));
    const auto conflict = refuter.check({{constant(0), Relation::Neq, SatLit::negative(9)}}, deadline());
    REQUIRE(conflict);
    CHECK(*conflict == std::vector<SatLit>{SatLit::negative(9)});
    CHECK_FALSE(refuter.check({}, deadline()));
}

TEST_CASE("Polynomial consequences: nonlinear premises lift through a coupled linear conflict") {
    const auto x = variable(0), z = variable(1), a = variable(2), b = variable(3), c = variable(4);
    std::vector<SignRefuteConstraint> constraints{
        {x, Relation::Geq, SatLit::positive(1)},
        {z, Relation::Geq, SatLit::negative(2)},
        {x * z - constant(1), Relation::Geq, SatLit::positive(3)},
        {a + b - x, Relation::Geq, SatLit::positive(4)},
        {b + c, Relation::Leq, SatLit::negative(5)},
        {a - c, Relation::Leq, SatLit::positive(6)}};
    // z>=0 and x*z>=1 imply x>0. The three coupled affine rows imply
    // x<=0, while the original monomial relaxation can retain x=0.
    const std::vector<PolynomialConsequence> consequences{
        {x, Relation::Gt, {SatLit::negative(2), SatLit::positive(3), SatLit::negative(2)}}};
    PolynomialLinearRefuter refuter;
    CHECK_FALSE(refuter.check(constraints, deadline()));
    const auto conflict = refuteByPolynomialConsequences(refuter, constraints, consequences, deadline());
    REQUIRE(conflict);
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::positive(3)) != conflict->end());
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::negative(2)) != conflict->end());
    for (auto premise : *conflict)
        CHECK(std::any_of(constraints.begin(), constraints.end(),
            [&](const auto& source) { return source.reason == premise; }));

    // Withdraw x>=0 and reverse the z premise. x=z=-1,a=b=c=0 is
    // feasible; a retained explanation for the opposite polarity is unusable.
    constraints.erase(constraints.begin(), constraints.begin() + 2);
    constraints.push_back({z, Relation::Leq, SatLit::positive(2)});
    const std::unordered_map<VarId, mpq_class> point{{0, -1}, {1, -1}, {2, 0}, {3, 0}, {4, 0}};
    for (const auto& source : constraints) {
        const auto value = source.poly.evaluateRational(point);
        if (source.rel == Relation::Geq) CHECK(value >= 0);
        else { REQUIRE(source.rel == Relation::Leq); CHECK(value <= 0); }
    }
    CHECK_FALSE(refuteByPolynomialConsequences(refuter, constraints, consequences, deadline()));
    CHECK_FALSE(refuteByPolynomialConsequences(refuter, {}, consequences, deadline()));
}

TEST_CASE("Polynomial consequences: unconditional facts and exhausted checks preserve source explanations") {
    const auto x = variable(0);
    const std::vector<SignRefuteConstraint> constraints{
        {x * x, Relation::Lt, SatLit::negative(5)}};
    const std::vector<PolynomialConsequence> consequences{{x * x, Relation::Geq, {}}};
    PolynomialLinearRefuter refuter;
    REQUIRE(refuter.check(constraints, deadline()));
    const auto conflict = refuteByPolynomialConsequences(refuter, constraints, consequences, deadline());
    REQUIRE(conflict);
    CHECK(*conflict == std::vector<SatLit>{SatLit::negative(5)});
    CHECK_FALSE(refuteByPolynomialConsequences(refuter, {}, consequences, deadline()));
    PolynomialLinearStatistics statistics;
    CHECK_FALSE(refuteByPolynomialConsequences(refuter, constraints, consequences,
        std::chrono::steady_clock::now(), &statistics));
    CHECK(statistics.exhausted);
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


TEST_CASE("Polynomial linear refutation: exact factor identities reuse definitions and withdraw their explanations") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    std::vector<SignRefuteConstraint> constraints{
        {x - constant(2), Relation::Eq, SatLit::positive(1)},
        {x * y - constant(6), Relation::Eq, SatLit::positive(2)},
        {y * z - constant(12), Relation::Eq, SatLit::positive(3)},
        {z - constant(5), Relation::Eq, SatLit::positive(4)}};
    PolynomialLinearRefuter refuter;
    PolynomialLinearStatistics stats;
    const auto conflict = refuter.check(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 4);
    CHECK(stats.productFacts >= 2);
    for (const auto& c : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), c.reason) != conflict->end());
    auto withdrawn = constraints;
    withdrawn.erase(withdrawn.begin());
    REQUIRE_FALSE(refuter.check(withdrawn, deadline(), &stats));
    CHECK(stats.reusedProductRows > 0);
    WorkBudget work;
    const auto model = refuter.projectCandidate(withdrawn, work);
    REQUIRE(model);
    for (const auto& c : withdrawn) CHECK(c.poly.evaluateRational(*model) == 0);
    CHECK(model->at(0) == mpq_class(5, 2));
    CHECK(model->at(1) == mpq_class(12, 5));
    constraints[0].reason = SatLit::negative(20);
    const auto rebound = refuter.check(constraints, deadline());
    REQUIRE(rebound);
    CHECK(std::find(rebound->begin(), rebound->end(), SatLit::positive(1)) == rebound->end());
    CHECK(std::find(rebound->begin(), rebound->end(), SatLit::negative(20)) != rebound->end());
    constraints[0].poly = x - constant(mpq_class(5, 2));
    CHECK_FALSE(refuter.check(constraints, deadline()));
    refuter.reset();
    CHECK_FALSE(refuter.check({}, deadline(), &stats));
    CHECK(stats.retainedRows == 0);
}

TEST_CASE("Polynomial linear refutation: zero products avoid huge powers and optional coefficient growth is bounded") {
    const auto x = variable(0), y = RationalPolynomial::fromVar(1, 2147483647, 1);
    PolynomialLinearRefuter refuter(0);
    PolynomialLinearStatistics stats;
    std::vector<SignRefuteConstraint> constraints{
        {x, Relation::Eq, SatLit::positive(1)},
        {x * y, Relation::Gt, SatLit::negative(2)}};
    const auto conflict = refuter.check(constraints, deadline(), &stats);
    REQUIRE(conflict);
    CHECK(conflict->size() == 2);
    CHECK(stats.productFacts + stats.signFacts == 1);
    CHECK_FALSE(stats.exhausted);
    constraints.erase(constraints.begin());
    CHECK_FALSE(refuter.check(constraints, deadline()));
    const auto huge = RationalPolynomial::fromVar(0, 2147483647, 1);
    constraints = {{x - constant(2), Relation::Eq, SatLit::positive(3)},
                   {huge - constant(1), Relation::Eq, SatLit::positive(4)}};
    CHECK_FALSE(refuter.check(constraints, deadline(), &stats));
    CHECK(stats.exhausted);
    constraints[0].poly = x - constant(1);
    CHECK_FALSE(refuter.check(constraints, deadline(), &stats));
    CHECK_FALSE(stats.exhausted);
}

TEST_CASE("Polynomial fixed monomials: exact product values constrain every divisible word") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    for (const mpq_class value : {mpq_class(0), mpq_class(2), mpq_class(-3), mpq_class(2, 3)}) {
        CAPTURE(value.get_str());
        const std::vector<SignRefuteConstraint> constraints{
            {x * y - constant(value), Relation::Eq, SatLit::negative(1)},
            {x * y * z - constant(value) * z, Relation::Neq, SatLit::positive(2)}};
        PolynomialLinearStatistics statistics;
        const auto conflict = PolynomialLinearRefuter{}.check(constraints, deadline(), &statistics);
        REQUIRE(conflict);
        CHECK(conflict->size() == 2);
        CHECK(statistics.productFacts > 0);
        CHECK_FALSE(statistics.exhausted);
        for (const auto& source : constraints)
            CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    }
}

TEST_CASE("Polynomial fixed monomials: coupled values retain current explanations across withdrawal") {
    const auto x = variable(0), y = variable(1), z = variable(2), w = variable(3);
    std::vector<SignRefuteConstraint> constraints{
        {x * y + w - constant(5), Relation::Eq, SatLit::positive(1)},
        {w - constant(5), Relation::Eq, SatLit::negative(2)},
        {x * y * z, Relation::Neq, SatLit::negative(3)}};
    PolynomialLinearRefuter refuter;
    auto conflict = refuter.check(constraints, deadline());
    REQUIRE(conflict);
    CHECK(conflict->size() == 3);
    for (const auto& source : constraints)
        CHECK(std::find(conflict->begin(), conflict->end(), source.reason) != conflict->end());
    CHECK_FALSE(refuter.check({constraints[0], constraints[2]}, deadline()));
    constraints[1].reason = SatLit::positive(20);
    conflict = refuter.check(constraints, deadline());
    REQUIRE(conflict);
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::negative(2)) == conflict->end());
    CHECK(std::find(conflict->begin(), conflict->end(), SatLit::positive(20)) != conflict->end());
    constraints[1].poly = w - constant(4);
    CHECK_FALSE(refuter.check(constraints, deadline())); // x=y=z=1,w=4
    refuter.reset();
    CHECK_FALSE(refuter.check({}, deadline()));
}

TEST_CASE("Polynomial fixed monomials: repeated factors preserve exact signed rational powers") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    for (const mpq_class value : {mpq_class(0), mpq_class(-2, 3), mpq_class(1), mpq_class(2)}) {
        mpq_class raised = value;
        for (int exponent = 2; exponent <= 4; ++exponent) {
            raised *= value;
            CAPTURE(value.get_str());
            CAPTURE(exponent);
            const std::vector<SignRefuteConstraint> constraints{
                {x * y - constant(value), Relation::Eq, SatLit::positive(1)},
                {x.pow(exponent) * y.pow(exponent) * z - constant(raised) * z,
                    Relation::Neq, SatLit::negative(2)}};
            const auto conflict = PolynomialLinearRefuter{}.check(constraints, deadline());
            REQUIRE(conflict);
            CHECK(conflict->size() == 2);
        }
    }
}

TEST_CASE("Polynomial fixed monomials: overlapping factors and feasible points cannot create conflicts") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    PolynomialLinearRefuter refuter;
    for (int a = -2; a <= 2; ++a) for (int b = -2; b <= 2; ++b) for (int c = -1; c <= 1; ++c) {
        const std::unordered_map<VarId, mpq_class> point{{0, a}, {1, b}, {2, mpq_class(c, 3)}};
        std::vector<SignRefuteConstraint> constraints;
        for (const auto& polynomial : {x * y, x * x * y, x * z, x * y * y * z, y * z * z})
            constraints.push_back({polynomial - constant(polynomial.evaluateRational(point)), Relation::Eq,
                SatLit(static_cast<SatVar>(constraints.size() + 1), constraints.size() % 2)});
        for (const auto& source : constraints) REQUIRE(source.poly.evaluateRational(point) == 0);
        CHECK_FALSE(refuter.check(constraints, deadline()));
    }
    CHECK_FALSE(refuter.check({
        {x * y, Relation::Eq, SatLit::positive(1)},
        {x * z - constant(1), Relation::Eq, SatLit::positive(2)}}, deadline())); // x=z=1,y=0
}

TEST_CASE("Polynomial fixed monomials: huge powers respect exact values and construction limits") {
    const auto x = variable(0), y = variable(1), z = variable(2);
    const auto large = x.pow(2147483647) * y.pow(2147483647) * z;
    PolynomialLinearRefuter refuter(0);
    PolynomialLinearStatistics statistics;
    const auto conflict = refuter.check({
        {x * y - constant(1), Relation::Eq, SatLit::positive(1)},
        {large - z, Relation::Neq, SatLit::negative(2)}}, deadline(), &statistics);
    REQUIRE(conflict);
    CHECK_FALSE(statistics.exhausted);
    CHECK_FALSE(refuter.check({
        {x * y - constant(2), Relation::Eq, SatLit::positive(1)},
        {large - z, Relation::Neq, SatLit::negative(2)}}, deadline(), &statistics));
    CHECK(statistics.exhausted);
    CHECK_FALSE(refuter.check({}, deadline(), &statistics));
    CHECK_FALSE(statistics.exhausted);
}
