#include <doctest/doctest.h>
#include "search/candidate/BoundaryCandidates.h"
#include "search/candidate/PartialLinearModelSearch.h"
#include "search/lra/GeneralSimplex.h"
#include <chrono>
#include <stdexcept>
#include <random>

using namespace xolver;

TEST_CASE("boundary candidates: theory endpoints are upper first without arithmetic assumptions") {
    CHECK((boundaryCandidates<int>(1, 5) == std::vector<int>{5, 1}));
    CHECK((boundaryCandidates<int>(5, 5) == std::vector<int>{5}));
    CHECK((boundaryCandidates<std::string>(std::string("a"), std::string("z")) ==
          std::vector<std::string>{"z", "a"}));
    CHECK(boundaryCandidates<int>(std::nullopt, std::nullopt).empty());
}

TEST_CASE("boundary candidates: propagated string choices unwind rejected and successful branches") {
    std::vector<std::string> prefix;
    size_t pushes = 0, pops = 0;
    const auto result = searchBoundaryCandidates(2,
        [](size_t) {
            return CandidateChoices<std::string>{boundaryCandidates<std::string>("lower", "upper"), {}};
        },
        [&](size_t depth, const std::string& value) {
            REQUIRE(prefix.size() == depth);
            prefix.push_back(value);
            ++pushes;
            if (depth == 0 || (prefix[0] == "lower" && value == "upper"))
                return CandidatePropagation::accept();
            return CandidatePropagation::reject({0, 1});
        },
        [&](size_t depth) {
            CHECK(prefix.size() == depth + 1);
            prefix.pop_back();
            ++pops;
        },
        [&]() -> std::optional<std::vector<std::string>> { return prefix; });
    REQUIRE(result.has_value());
    CHECK((*result == std::vector<std::string>{"lower", "upper"}));
    CHECK(prefix.empty());
    CHECK(pushes == 5);
    CHECK(pops == pushes);
}

TEST_CASE("boundary candidates: interrupted propagation unwinds partially constructed choices") {
    std::vector<int> prefix;
    auto run = [&]() {
        return searchBoundaryCandidates(3,
            [](size_t) { return CandidateChoices<int>{{1}, {}}; },
            [&](size_t depth, int value) {
                prefix.push_back(value);
                if (depth == 1) throw std::runtime_error("local allocation expired");
                return CandidatePropagation::accept();
            },
            [&](size_t depth) {
                CHECK(prefix.size() == depth + 1);
                prefix.pop_back();
            },
            []() -> std::optional<int> { return 1; });
    };
    CHECK_THROWS_AS(run(), std::runtime_error);
    CHECK(prefix.empty());
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

TEST_CASE("partial linear model: mixed boundaries propagate and backtrack coupled products") {
    auto kernel = createPolynomialKernel();
    const auto a = kernel->getOrCreateVar("a"), b = kernel->getOrCreateVar("b"),
               c = kernel->getOrCreateVar("c"), w = kernel->getOrCreateVar("w");
    const auto av = kernel->mkVar(a), bv = kernel->mkVar(b), cv = kernel->mkVar(c),
               wv = kernel->mkVar(w), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints;
    for (auto v : {av, bv, cv}) {
        constraints.push_back({v, Relation::Geq});
        constraints.push_back({kernel->sub(v, one), Relation::Leq});
    }
    constraints.push_back({kernel->sub(kernel->add(av, bv), one), Relation::Eq});
    constraints.push_back({kernel->mul(av, bv), Relation::Eq});
    constraints.push_back({kernel->mul(av, cv), Relation::Eq});
    constraints.push_back({kernel->sub(kernel->mul(bv, cv), one), Relation::Eq});
    constraints.push_back({kernel->sub(kernel->sub(wv, bv),
                                     kernel->mkConst(mpq_class(1000))), Relation::Geq});
    for (const bool integerDomain : {false, true}) {
        PartialLinearModelSearch::Statistics stats;
        const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, integerDomain, &stats);
        REQUIRE(model.has_value());
        CHECK(stats.contexts == 1);
        CHECK(model->at(a) == 0);
        CHECK(model->at(b) == 1);
        CHECK(model->at(c) == 1);
        CHECK(model->at(w) >= 1001);
        for (const auto& constraint : constraints) {
            const int sign = kernel->sgnVarId(constraint.poly, *model);
            if (constraint.rel == Relation::Eq) CHECK(sign == 0);
            else if (constraint.rel == Relation::Geq) CHECK(sign >= 0);
            else CHECK(sign <= 0);
        }
    }
    constraints.push_back({kernel->sub(wv, kernel->mkConst(mpq_class(1000))), Relation::Leq});
    for (const bool integerDomain : {false, true})
        CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, integerDomain));
}

TEST_CASE("partial linear model: coupled equalities complete a shared unknown off the candidate grid") {
    for (const bool centerFirst : {false, true}) {
        for (const int sign : {-1, 1}) {
            auto kernel = createPolynomialKernel();
            if (centerFirst) kernel->getOrCreateVar("r");
            std::vector<VarId> leaves;
            for (const auto* name : {"a", "b", "c"}) leaves.push_back(kernel->getOrCreateVar(name));
            const auto r = kernel->getOrCreateVar("r");
            const auto rv = kernel->mkVar(r);
            auto number = [&](int n) { return kernel->mkConst(mpq_class(n)); };
            const auto positive = kernel->mul(number(sign), rv);
            std::vector<PartialLinearModelSearch::Constraint> constraints{
                {kernel->sub(kernel->mul(number(6), positive), number(1)), Relation::Gt},
                {kernel->sub(kernel->mul(number(4), positive), number(1)), Relation::Lt}
            };
            int target = 1;
            for (const auto leaf : leaves) {
                const auto v = kernel->mkVar(leaf);
                constraints.push_back({kernel->sub(kernel->mul(v, rv), number(sign * target)), Relation::Eq});
                constraints.push_back({kernel->sub(v, number(5 * target)), Relation::Eq});
                ++target;
            }
            PartialLinearModelSearch::Statistics stats;
            const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, false, &stats);
            REQUIRE(model.has_value());
            CHECK(model->at(r) == mpq_class(sign, 5));
            CHECK_FALSE(stats.exhausted);
            for (const auto& constraint : constraints) {
                const int value = kernel->sgnVarId(constraint.poly, *model);
                if (constraint.rel == Relation::Eq) CHECK(value == 0);
                else if (constraint.rel == Relation::Gt) CHECK(value > 0);
                else CHECK(value < 0);
            }
            CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, true));
        }
    }
}

TEST_CASE("partial linear model: inequality products limit the jointly affine equality block") {
    auto kernel = createPolynomialKernel();
    const auto r = kernel->getOrCreateVar("r"), s = kernel->getOrCreateVar("s");
    const auto rv = kernel->mkVar(r), sv = kernel->mkVar(s), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints;
    for (const auto variable : {rv, sv}) {
        constraints.push_back({kernel->sub(variable, one), Relation::Eq});
        constraints.push_back({kernel->sub(kernel->mul(kernel->mkConst(mpq_class(2)), variable),
                                           kernel->mkConst(mpq_class(2))), Relation::Eq});
    }
    constraints.push_back({kernel->mul(rv, sv), Relation::Gt});
    PartialLinearModelSearch::Statistics stats;
    const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, false, &stats);
    REQUIRE(model.has_value());
    CHECK(model->at(r) == 1);
    CHECK(model->at(s) == 1);
    CHECK(stats.retainedEqualityVariables == 1);
    CHECK(stats.parameters == 1);
    constraints.back().rel = Relation::Lt;
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel));
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

TEST_CASE("partial linear model: a fully covered power uses an admissible interior point") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->getOrCreateVar("x");
    const auto xv = kernel->mkVar(x), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {xv, Relation::Lt},
        {kernel->add(xv, kernel->mkConst(mpq_class(2))), Relation::Gt},
        {kernel->sub(kernel->pow(xv, 2), one), Relation::Eq}
    };
    for (const bool integerDomain : {false, true}) {
        const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, integerDomain);
        REQUIRE(model.has_value());
        CHECK(model->at(x) == -1);
    }
    constraints.push_back({kernel->add(xv, one), Relation::Neq});
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel));
}

TEST_CASE("partial linear model: quotient chains retain multiple parameter powers") {
    auto kernel = createPolynomialKernel();
    const auto a = kernel->getOrCreateVar("a"), b = kernel->getOrCreateVar("b");
    const auto av = kernel->mkVar(a), bv = kernel->mkVar(b), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {av, Relation::Geq}, {kernel->sub(av, one), Relation::Leq},
        {kernel->sub(bv, one), Relation::Geq},
        {kernel->sub(bv, kernel->mkConst(mpq_class(2))), Relation::Leq},
        {kernel->sub(kernel->mul(kernel->pow(av, 2), kernel->pow(bv, 3)),
                     kernel->mkConst(mpq_class(8))), Relation::Eq}
    };
    for (const bool integerDomain : {false, true}) {
        const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, integerDomain);
        REQUIRE(model.has_value());
        CHECK(model->at(a) == 1);
        CHECK(model->at(b) == 2);
    }
    constraints.push_back({kernel->sub(bv, kernel->mkConst(mpq_class(2))), Relation::Neq});
    CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel));
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

TEST_CASE("partial linear model: explained reasoning avoids enumerating unrelated nonlinear parameters") {
    auto kernel = createPolynomialKernel();
    const auto p = kernel->getOrCreateVar("choice");
    const auto pv = kernel->mkVar(p), one = kernel->mkOne();
    std::vector<PartialLinearModelSearch::Constraint> constraints;
    auto bounds = [&](PolyId poly, int upper) {
        constraints.push_back({poly, Relation::Geq});
        constraints.push_back({kernel->sub(poly, kernel->mkConst(upper)), Relation::Leq});
    };
    bounds(pv, 2);
    const auto offset = kernel->sub(pv, one);
    constraints.push_back({kernel->mul(offset, kernel->sub(pv, kernel->mkConst(2))), Relation::Eq});
    std::vector<VarId> independent;
    for (int i = 0; i < 24; ++i) {
        const auto var = kernel->getOrCreateVar("independent_" + std::to_string(i));
        independent.push_back(var);
        const auto poly = kernel->mkVar(var);
        bounds(poly, 1);
        constraints.push_back({kernel->sub(kernel->pow(poly, 11), poly), Relation::Eq});
    }
    const auto q = kernel->getOrCreateVar("last");
    const auto qv = kernel->mkVar(q);
    bounds(qv, 2);
    constraints.push_back({kernel->sub(kernel->add(pv, qv), kernel->mkConst(2)), Relation::Eq});
    constraints.push_back({kernel->mul(kernel->pow(offset, 4),
        kernel->add(kernel->pow(qv, 2), one)), Relation::Eq});
    PartialLinearModelSearch::Statistics statistics;
    const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, false, &statistics);
    REQUIRE(model.has_value());
    CHECK(model->at(p) == 1);
    CHECK(model->at(q) == 1);
    for (const auto var : independent)
        CHECK((model->at(var) == 0 || model->at(var) == 1));
    CHECK((statistics.backjumps > 0 || statistics.propagatedFacts > 0));
    CHECK(statistics.choices < 200);
    CHECK(statistics.explanationFallbacks == 0);
}

TEST_CASE("partial linear model: exact singleton chains are scoped to each call and domain") {
    auto kernel = createPolynomialKernel();
    const auto a = kernel->getOrCreateVar("a"), r = kernel->getOrCreateVar("r"),
               b = kernel->getOrCreateVar("b"), c = kernel->getOrCreateVar("c");
    const auto av = kernel->mkVar(a), rv = kernel->mkVar(r), bv = kernel->mkVar(b), cv = kernel->mkVar(c);
    std::vector<PartialLinearModelSearch::Constraint> constraints{
        {kernel->sub(av, kernel->mkOne()), Relation::Eq},
        {kernel->sub(kernel->mul(av, rv), kernel->mkOne()), Relation::Eq},
        {kernel->sub(kernel->mul(bv, rv), kernel->mkConst(2)), Relation::Eq},
        {kernel->sub(kernel->mul(cv, rv), kernel->mkConst(3)), Relation::Eq},
        {rv, Relation::Gt}
    };
    for (const int anchor : {1, 2, 1}) {
        constraints[0].poly = kernel->sub(av, kernel->mkConst(anchor));
        PartialLinearModelSearch::Statistics stats;
        const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, false, &stats);
        REQUIRE(model.has_value());
        CHECK(model->at(a) == anchor);
        CHECK(model->at(r) == mpq_class(1, anchor));
        CHECK(model->at(b) == 2 * anchor);
        CHECK(model->at(c) == 3 * anchor);
        CHECK(stats.choices == 0);
        CHECK(stats.propagatedFacts >= 3);
        CHECK_FALSE(stats.exhausted);
        for (const auto& constraint : constraints) {
            const int sign = kernel->sgnVarId(constraint.poly, *model);
            CHECK((constraint.rel == Relation::Eq ? sign == 0 : sign > 0));
        }
        const auto integral = PartialLinearModelSearch::trySolve(constraints, *kernel, true);
        CHECK(integral.has_value() == (anchor == 1));
    }
}

TEST_CASE("partial linear model: substitution combines cancelling nonlinear residual monomials") {
    auto kernel = createPolynomialKernel();
    const auto r = kernel->getOrCreateVar("r"), u = kernel->getOrCreateVar("u"), b = kernel->getOrCreateVar("b");
    const auto rv = kernel->mkVar(r), uv = kernel->mkVar(u), bv = kernel->mkVar(b);
    const auto residual = kernel->add(kernel->mul(kernel->sub(rv, kernel->mkOne()), kernel->pow(uv, 2)),
                                      kernel->sub(bv, kernel->mkConst(2)));
    const std::vector<PartialLinearModelSearch::Constraint> constraints{
        {kernel->sub(rv, kernel->mkOne()), Relation::Eq}, {residual, Relation::Eq},
        {kernel->sub(kernel->pow(bv, 2), kernel->mkConst(4)), Relation::Eq}, {bv, Relation::Gt}
    };
    PartialLinearModelSearch::Statistics stats;
    const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel, false, &stats);
    REQUIRE(model.has_value());
    CHECK(model->at(r) == 1);
    CHECK(model->at(b) == 2);
    CHECK(stats.choices == 0);
    CHECK(stats.maxActiveAtoms == constraints.size());
    for (const auto& constraint : constraints) {
        const int sign = kernel->sgnVarId(constraint.poly, *model);
        CHECK((constraint.rel == Relation::Eq ? sign == 0 : sign > 0));
    }
    for (const auto allocation : {PartialLinearModelSearch::Allocation(std::chrono::milliseconds(0)),
                                  PartialLinearModelSearch::Allocation(std::chrono::milliseconds(1000), 1)}) {
        CHECK_FALSE(PartialLinearModelSearch::trySolve(constraints, *kernel, false, &stats, allocation));
        CHECK(stats.exhausted);
    }
    CHECK(PartialLinearModelSearch::trySolve(constraints, *kernel).has_value());
}

TEST_CASE("partial linear model: explained substitution and withdrawal preserve independent Boolean witnesses") {
    std::mt19937 random(3197);
    for (int trial = 0; trial < 70; ++trial) {
        auto kernel = createPolynomialKernel();
        constexpr int count = 4;
        std::vector<VarId> variables;
        std::vector<mpq_class> known;
        std::vector<PartialLinearModelSearch::Constraint> constraints;
        const auto one = kernel->mkOne();
        for (int i = 0; i < count; ++i) {
            const auto var = kernel->getOrCreateVar("v_" + std::to_string(i));
            variables.push_back(var);
            known.emplace_back(random() % 2);
            const auto poly = kernel->mkVar(var);
            constraints.push_back({poly, Relation::Geq});
            constraints.push_back({kernel->sub(poly, one), Relation::Leq});
            constraints.push_back({kernel->sub(kernel->pow(poly, 2), poly), Relation::Eq});
        }
        struct Term { int coefficient; std::vector<size_t> factors; };
        struct Source { std::vector<Term> terms; mpq_class rhs; Relation relation; };
        std::vector<Source> sources;
        auto evaluate = [](const Source& source, const std::vector<mpq_class>& point) {
            mpq_class value = 0;
            for (const auto& term : source.terms) {
                mpq_class product = term.coefficient;
                for (const auto factor : term.factors) product *= point[factor];
                value += product;
            }
            return mpq_class(value - source.rhs);
        };
        for (int i = 0; i < 7; ++i) {
            Source source{{}, 0, i % 3 == 0 ? Relation::Eq : Relation::Geq};
            auto polynomial = kernel->mkConst(0);
            for (int j = 0; j < 4; ++j) {
                Term term{static_cast<int>(random() % 7) - 3, {random() % count, random() % count}};
                auto product = kernel->mkConst(term.coefficient);
                for (const auto factor : term.factors) product = kernel->mul(product, kernel->mkVar(variables[factor]));
                polynomial = kernel->add(polynomial, product);
                source.terms.push_back(std::move(term));
            }
            source.rhs = evaluate(source, known);
            constraints.push_back({kernel->sub(polynomial, kernel->mkConst(source.rhs)), source.relation});
            sources.push_back(std::move(source));
        }
        const auto model = PartialLinearModelSearch::trySolve(constraints, *kernel);
        REQUIRE(model.has_value());
        std::vector<mpq_class> point;
        for (const auto var : variables) {
            point.push_back(model->at(var));
            CHECK((point.back() == 0 || point.back() == 1));
        }
        for (const auto& source : sources) {
            const auto value = evaluate(source, point);
            CHECK((source.relation == Relation::Eq ? value == 0 : value >= 0));
        }
    }
}
