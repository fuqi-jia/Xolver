#include <doctest/doctest.h>
#include "search/candidate/BoundaryCandidates.h"
#include "search/candidate/PartialLinearModelSearch.h"
#include "search/lra/GeneralSimplex.h"
#include <chrono>

using namespace xolver;

TEST_CASE("boundary candidates: theory endpoints are upper first without arithmetic assumptions") {
    CHECK((boundaryCandidates<int>(1, 5) == std::vector<int>{5, 1}));
    CHECK((boundaryCandidates<int>(5, 5) == std::vector<int>{5}));
    CHECK((boundaryCandidates<std::string>(std::string("a"), std::string("z")) ==
          std::vector<std::string>{"z", "a"}));
    CHECK(boundaryCandidates<int>(std::nullopt, std::nullopt).empty());
}

TEST_CASE("partial linear model: upper parameter boundary completes coupled large coordinates") {
    auto kernel = createPolynomialKernel();
    const auto p = kernel->getOrCreateVar("p"), x = kernel->getOrCreateVar("x"),
               y = kernel->getOrCreateVar("y");
    const auto pv = kernel->mkVar(p), xv = kernel->mkVar(x), yv = kernel->mkVar(y);
    auto number = [&](int n) { return kernel->mkConst(mpq_class(n)); };
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {pv, Relation::Geq}, {kernel->sub(pv, number(1)), Relation::Leq},
        {kernel->sub(kernel->pow(pv, 2), pv), Relation::Leq},
        {kernel->sub(kernel->sub(kernel->mul(number(1000), xv),
                                kernel->mul(number(999), kernel->mul(pv, yv))), number(1000)), Relation::Geq},
        {kernel->sub(kernel->sub(yv, xv), number(1)), Relation::Geq}
    };
    const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel);
    REQUIRE(model.has_value());
    CHECK(model->size() == 3);
    CHECK(model->at(p) == 1);
    CHECK(model->at(x) >= 1999);
    CHECK(model->at(y) >= model->at(x) + 1);
    for (const auto& c : constraints) {
        const auto sign = kernel->sgnVarId(c.poly, *model);
        CHECK((c.rel == Relation::Geq ? sign >= 0 : sign <= 0));
    }
}

TEST_CASE("partial linear model: open endpoints and strict residual rows have concrete witnesses") {
    auto kernel = createPolynomialKernel();
    const auto p = kernel->getOrCreateVar("p"), x = kernel->getOrCreateVar("x");
    const auto pv = kernel->mkVar(p), xv = kernel->mkVar(x), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {pv, Relation::Gt}, {kernel->sub(pv, one), Relation::Lt},
        {kernel->sub(kernel->pow(pv, 2), pv), Relation::Lt},
        {kernel->sub(kernel->mul(pv, xv), one), Relation::Gt}
    };
    const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel);
    REQUIRE(model.has_value());
    CHECK(model->at(p) > 0);
    CHECK(model->at(p) < 1);
    CHECK(model->at(p) * model->at(x) > 1);
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, true));
}

TEST_CASE("partial linear model: integer clients reject fractional completions and retain integral ones") {
    auto kernel = createPolynomialKernel();
    const auto p = kernel->getOrCreateVar("p"), x = kernel->getOrCreateVar("x");
    const auto pv = kernel->mkVar(p), xv = kernel->mkVar(x), one = kernel->mkOne();
    const auto product = kernel->mul(pv, xv);
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {kernel->sub(pv, one), Relation::Eq},
        {kernel->sub(kernel->pow(pv, 2), pv), Relation::Eq},
        {kernel->sub(kernel->mul(kernel->mkConst(mpq_class(2)), product), one), Relation::Eq}
    };
    const auto realModel = PartialLinearModelSearch::trySolve(constraints, *kernel);
    REQUIRE(realModel.has_value());
    CHECK(realModel->at(x) == mpq_class(1, 2));
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, true));
    constraints.back().poly = kernel->sub(product, kernel->mkConst(mpq_class(2)));
    const auto integerModel = PartialLinearModelSearch::trySolve(constraints, *kernel, true);
    REQUIRE(integerModel.has_value());
    CHECK(integerModel->at(x) == 2);
    constraints.push_back({kernel->sub(xv, kernel->mkConst(mpq_class(2))), Relation::Neq});
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, true));
    CHECK_FALSE(PartialLinearModelSearch::trySolve({{NullPoly, Relation::Eq}}, *kernel));
}

TEST_CASE("GeneralSimplex: local model-search deadline leaves ordinary feasibility resumable") {
    GeneralSimplex simplex;
    const int x = simplex.addVar("x");
    const auto reason = SatLit::positive(1);
    REQUIRE(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(mpq_class(10))), reason)));
    CHECK((simplex.checkUntil(std::chrono::steady_clock::time_point::min()) == GeneralSimplex::Result::Unknown));
    CHECK((simplex.check() == GeneralSimplex::Result::Sat));
    CHECK(simplex.value(x).a >= 10);
    CHECK(simplex.debugCheckInvariants());
    CHECK_FALSE(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(mpq_class(9))), reason)));
    CHECK((simplex.check() == GeneralSimplex::Result::Unsat));
}
