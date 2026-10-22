#include <doctest/doctest.h>
#include "search/nra/simplex/NraLinearExtractor.h"
#include "search/nra/simplex/SimplexTableauFacts.h"
#include <random>

using namespace xolver;

namespace {
CdcacConstraint constraint(PolyId polynomial, Relation relation, SatVar reason) {
    CdcacConstraint result;
    result.poly = polynomial;
    result.rel = relation;
    result.reason = SatLit::positive(reason);
    return result;
}
}

TEST_CASE("native monomial relaxation refutes incompatible nonlinear affine bounds") {
    auto kernel = createPolynomialKernel();
    auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    auto xx = kernel->mul(x, x), yy = kernel->mul(y, y);
    const auto constraints = std::vector{
        constraint(kernel->sub(kernel->add(xx, yy), kernel->mkConst(3)), Relation::Geq, 1),
        constraint(kernel->sub(xx, kernel->mkConst(1)), Relation::Leq, 2),
        constraint(kernel->sub(yy, kernel->mkConst(1)), Relation::Leq, 3)
    };
    auto relaxed = linearizeMonomials(*kernel, constraints);
    REQUIRE(relaxed.size() == constraints.size());
    CHECK(computeSimplexTableauFacts(relaxed).linearSubsetUnsat());
    for (size_t i = 0; i < relaxed.size(); ++i) CHECK(relaxed[i].reason == constraints[i].reason);
}

TEST_CASE("native monomial relaxation preserves strict bounds and scalar signs") {
    auto kernel = createPolynomialKernel();
    auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    auto xy = kernel->mul(x, y);
    // xy > 1 and -3*yx >= -3 cannot both hold.
    auto relaxed = linearizeMonomials(*kernel, {
        constraint(kernel->sub(xy, kernel->mkConst(1)), Relation::Gt, 1),
        constraint(kernel->add(kernel->mul(kernel->mkConst(-3), kernel->mul(y, x)),
                               kernel->mkConst(3)), Relation::Geq, 2)
    });
    CHECK(computeSimplexTableauFacts(relaxed).linearSubsetUnsat());
}

TEST_CASE("native monomial relaxation does not decide nonlinear satisfiability") {
    auto kernel = createPolynomialKernel();
    auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    auto xx = kernel->mul(x, x);
    // x^2 < 0 is infeasible over the reals, but the independent monomial
    // variable can be negative. Its feasible relaxation is not a SAT proof.
    auto relaxed = linearizeMonomials(*kernel, {constraint(xx, Relation::Lt, 1)});
    CHECK_FALSE(computeSimplexTableauFacts(relaxed).linearSubsetUnsat());
    // Different powers must remain distinct. x=-2 witnesses this conjunction.
    relaxed = linearizeMonomials(*kernel, {
        constraint(kernel->sub(xx, kernel->mkConst(4)), Relation::Eq, 1),
        constraint(kernel->add(x, kernel->mkConst(2)), Relation::Eq, 2)
    });
    CHECK_FALSE(computeSimplexTableauFacts(relaxed).linearSubsetUnsat());
}

TEST_CASE("native monomial relaxation retains known polynomial witnesses") {
    std::mt19937 random(20261020);
    std::uniform_int_distribution<int> coefficient(-5, 5), coordinate(-3, 3);
    for (int instance = 0; instance < 120; ++instance) {
        CAPTURE(instance);
        auto kernel = createPolynomialKernel();
        const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
        const int vx = coordinate(random), vy = coordinate(random);
        std::vector<CdcacConstraint> original;
        for (int i = 0; i < 6; ++i) {
            const int a = coefficient(random), b = coefficient(random);
            const int c = coefficient(random), d = coefficient(random);
            const int value = a * vx * vx + b * vx * vy + c * vy + d;
            const int offset = i % 2;
            auto p = kernel->mkFromMonomials({
                {mpz_class(a), {{x, 2}}}, {mpz_class(b), {{x, 1}, {y, 1}}},
                {mpz_class(c), {{y, 1}}}, {mpz_class(d - value + offset), {}}
            });
            original.push_back(constraint(p, offset ? Relation::Gt : Relation::Eq, i + 1));
        }
        auto relaxed = linearizeMonomials(*kernel, original);
        REQUIRE(relaxed.size() == original.size());
        CHECK_FALSE(computeSimplexTableauFacts(relaxed).linearSubsetUnsat());
    }
}

TEST_CASE("native monomial relaxation explains conflicts without unrelated assumptions") {
    auto kernel = createPolynomialKernel();
    auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    auto xx = kernel->mul(x, x);
    auto relaxed = linearizeMonomials(*kernel, {
        constraint(kernel->sub(xx, kernel->mkConst(1)), Relation::Gt, 1),
        constraint(kernel->sub(xx, kernel->mkConst(1)), Relation::Leq, 2),
        constraint(kernel->sub(y, kernel->mkConst(19)), Relation::Eq, 3)
    });
    auto facts = computeSimplexTableauFacts(relaxed);
    REQUIRE(facts.linearSubsetUnsat());
    REQUIRE(facts.conflictReasons().size() == 2);
    for (const auto& literal : facts.conflictReasons())
        CHECK((literal.var == 1 || literal.var == 2));
}
