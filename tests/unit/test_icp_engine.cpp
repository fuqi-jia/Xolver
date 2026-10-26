#include <doctest/doctest.h>
#include "search/icp/IcpEngine.h"
#include "search/icp/contractors/RelationContractor.h"
#include "search/icp/ContractorFactory.h"
#include "search/nia/search/NiaIcpAdapter.h"
#include "algebra/poly/PolynomialKernel.h"
#include <algorithm>
#include <memory>

using namespace xolver;

namespace {
SatLit lit(int n) { return SatLit::positive(n); }
bool contains(const std::vector<SatLit>& reasons, int n) {
    return std::find(reasons.begin(), reasons.end(), lit(n)) != reasons.end();
}

TEST_CASE("ICP integer: nonlinear definitions create missing bounds and wake dependent rows") {
    auto kernel = createPolynomialKernel();
    auto variable = [&](const char* name) { return kernel->mkVar(kernel->getOrCreateVar(name)); };
    const auto x = variable("x"), y = variable("y"), z = variable("z"), w = variable("w");
    const auto definition = kernel->sub(x, kernel->add(kernel->mul(y, y), kernel->mul(z, z)));
    const auto following = kernel->sub(w, x);
    auto built = ContractorFactory::build({
        {std::nullopt, definition, Relation::Eq, lit(5), TheoryId::NIA},
        {std::nullopt, following, Relation::Eq, lit(6), TheoryId::NIA}}, *kernel);
    ReasonedBox box;
    box.set("y", {{2, 3}, {lit(1), lit(2)}});
    box.set("z", {{-3, -2}, {lit(3), lit(4)}});
    auto result = IcpEngine{}.run(built.contractors, built.watchers, box, {});
    REQUIRE(result.status == IcpStatus::DomainUpdate);
    REQUIRE(box.get("w").has_value());
    CHECK(box.get("w")->interval.lo == 8);
    CHECK(box.get("w")->interval.hi == 18);
    for (int reason = 1; reason <= 6; ++reason) CHECK(contains(box.get("w")->reasons, reason));
    // A new context with incompatible w bounds must cite both the equation
    // chain and its new bound source, with no reused child explanations.
    box.clear();
    box.set("y", {{2, 3}, {lit(1), lit(2)}});
    box.set("z", {{-3, -2}, {lit(3), lit(4)}});
    box.set("w", {{-10, -1}, {lit(7)}});
    result = IcpEngine{}.run(built.contractors, built.watchers, box, {});
    REQUIRE(result.status == IcpStatus::Conflict);
    REQUIRE(result.conflict.has_value());
    for (int reason = 1; reason <= 7; ++reason) CHECK(contains(result.conflict->clause, reason));
}

TEST_CASE("ICP integer: signed nonlinear projections retain every independently feasible point") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    for (const int coefficient : {-3, -1, 1, 3}) {
        const auto poly = kernel->add(kernel->mkConst(1), kernel->add(
            kernel->mul(kernel->mkConst(coefficient), x),
            kernel->sub(kernel->mul(y, y), kernel->mul(kernel->mkConst(3), z))));
        for (const auto relation : {Relation::Eq, Relation::Neq, Relation::Leq,
                                    Relation::Lt, Relation::Geq, Relation::Gt}) {
            ReasonedBox box;
            box.set("x", {{-8, 8}, {lit(1)}});
            box.set("y", {{-2, 2}, {lit(2)}});
            box.set("z", {{-2, 2}, {lit(3)}});
            RelationContractor contractor({std::nullopt, poly, relation, lit(4), TheoryId::NIA}, *kernel);
            const auto result = contractor.contract(box);
            for (int a = -8; a <= 8; ++a) for (int b = -2; b <= 2; ++b) for (int c = -2; c <= 2; ++c) {
                const auto value = kernel->evalInteger(poly, {{"x", mpz_class(a)}, {"y", mpz_class(b)}, {"z", mpz_class(c)}});
                REQUIRE(value.has_value());
                const bool holds = relation == Relation::Eq ? *value == 0 : relation == Relation::Neq ? *value != 0 :
                    relation == Relation::Leq ? *value <= 0 : relation == Relation::Lt ? *value < 0 :
                    relation == Relation::Geq ? *value >= 0 : *value > 0;
                if (!holds) continue;
                CHECK(result.status != IcpStatus::Conflict);
                for (const auto& update : result.updates)
                    CHECK(update.newInterval.contains(update.var == "x" ? a : update.var == "y" ? b : c));
            }
        }
    }
}

TEST_CASE("ICP integer: backward rounding cannot discard real-valued models") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto poly = kernel->sub(kernel->add(kernel->mul(kernel->mkConst(2), x), y), kernel->mkOne());
    ReasonedBox box;
    box.set("x", {{0, 1}, {lit(1)}});
    box.set("y", {{0, 0}, {lit(2)}});
    RelationContractor real({std::nullopt, poly, Relation::Eq, lit(3), TheoryId::NRA}, *kernel);
    CHECK(real.contract(box).status == IcpStatus::NoChange); // x=1/2 is feasible
    RelationContractor integer({std::nullopt, poly, Relation::Eq, lit(3), TheoryId::NIA}, *kernel);
    CHECK(integer.contract(box).status == IcpStatus::Conflict);
}

// A contractor may repeat a sound bound proposal. The engine owns intersection
// and must schedule dependants only when the box actually changes.
class FixedBound final : public Contractor {
public:
    explicit FixedBound(int& calls) : calls_(calls) {}
    ContractorResultZ contract(ReasonedBox&) override {
        ++calls_;
        return {IcpStatus::DomainUpdate, std::nullopt,
                {{"x", IntervalZ{-4, 4}, {lit(2)}}}};
    }
    std::vector<std::string> vars() const override { return {"x"}; }
    SatLit reason() const override { return lit(2); }
private:
    int& calls_;
};

struct EngineFixture {
    int calls = 0;
    ReasonedBox box;
    WatcherMap watchers;
    IcpConfig config;
    std::vector<std::unique_ptr<Contractor>> contractors;
    EngineFixture() {
        contractors.push_back(std::make_unique<FixedBound>(calls));
        watchers.addWatcher("x", 0);
        config.maxIterations = 8;
        config.maxContractors = 8;
    }
    IcpResultZ run() { return IcpEngine{}.run(contractors, watchers, box, config); }
};

IcpConstraint square(PolynomialKernel& kernel, int coefficient, int constant,
                     Relation relation, int reason = 2) {
    auto x = kernel.mkVar(kernel.getOrCreateVar("x"));
    auto poly = kernel.add(kernel.mul(kernel.mkConst(mpq_class(coefficient)),
                                      kernel.mul(x, x)),
                           kernel.mkConst(mpq_class(constant)));
    return {std::nullopt, poly, relation, lit(reason), TheoryId::NIA};
}
}

TEST_CASE("ICP integer: applies proposals and reaches a fixpoint") {
    EngineFixture f;
    auto result = f.run();
    REQUIRE(result.status == IcpStatus::DomainUpdate);
    REQUIRE(result.updates.size() == 1);
    REQUIRE(f.box.get("x").has_value());
    CHECK(f.calls == 2);
    CHECK(f.box.get("x")->interval.lo == -4);
    CHECK(f.box.get("x")->interval.hi == 4);
    CHECK(result.updates.front().newInterval.lo == -4);
    CHECK(result.updates.front().newInterval.hi == 4);
    CHECK(contains(result.updates.front().reasons, 2));
}

TEST_CASE("ICP integer: intersects bounds and preserves both reasons") {
    EngineFixture f;
    f.box.set("x", {IntervalZ{3, 10}, {lit(1)}});
    auto result = f.run();
    REQUIRE(result.status == IcpStatus::DomainUpdate);
    REQUIRE(result.updates.size() == 1);
    CHECK(result.updates.front().newInterval.lo == 3);
    CHECK(result.updates.front().newInterval.hi == 4);
    CHECK(contains(result.updates.front().reasons, 1));
    CHECK(contains(result.updates.front().reasons, 2));
}

TEST_CASE("ICP integer: disjoint bounds yield an explained conflict") {
    EngineFixture f;
    f.box.set("x", {IntervalZ{5, 10}, {lit(1)}});
    auto result = f.run();
    REQUIRE(result.status == IcpStatus::Conflict);
    REQUIRE(result.conflict.has_value());
    CHECK(contains(result.conflict->clause, 1));
    CHECK(contains(result.conflict->clause, 2));
    CHECK(f.calls == 1);
}

TEST_CASE("ICP integer: an unchanged proposal does not requeue watchers") {
    EngineFixture f;
    f.box.set("x", {IntervalZ{-4, 4}, {lit(1)}});
    auto result = f.run();
    CHECK(result.status == IcpStatus::NoChange);
    CHECK(result.updates.empty());
    CHECK(f.calls == 1);
}

TEST_CASE("ICP integer: zero budgets execute no contractors") {
    EngineFixture f;
    SUBCASE("contractors") { f.config.maxContractors = 0; }
    SUBCASE("iterations") { f.config.maxIterations = 0; }
    auto result = f.run();
    CHECK(result.status == IcpStatus::UnknownBudget);
    CHECK(result.updates.empty());
    CHECK(f.calls == 0);
}

TEST_CASE("ICP integer: exhausted budgets retain sound progress") {
    EngineFixture f;
    SUBCASE("contractors") { f.config.maxContractors = 1; }
    SUBCASE("iterations") { f.config.maxIterations = 1; }
    auto result = f.run();
    REQUIRE(result.status == IcpStatus::UnknownBudget);
    REQUIRE(result.updates.size() == 1);
    CHECK(f.calls == 1);
    CHECK(result.updates.front().newInterval.lo == -4);
    CHECK(result.updates.front().newInterval.hi == 4);
    CHECK(contains(result.updates.front().reasons, 2));
}

TEST_CASE("ICP integer: initially empty boxes keep conflict reasons") {
    ReasonedBox box;
    box.set("x", {IntervalZ{5, 4}, {lit(1), lit(2)}});
    auto result = IcpEngine{}.run({}, {}, box, {});
    REQUIRE(result.status == IcpStatus::Conflict);
    REQUIRE(result.conflict.has_value());
    CHECK(contains(result.conflict->clause, 1));
    CHECK(contains(result.conflict->clause, 2));
}

TEST_CASE("ICP integer: adapter exports bounds and reaches a stable second call") {
    auto kernel = createPolynomialKernel();
    DomainStore store;
    NiaIcpAdapter adapter(*kernel, store);
    std::vector<IcpConstraint> constraints{square(*kernel, 1, -16, Relation::Eq)};
    IcpConfig config;
    config.maxIterations = 8;
    auto result = adapter.run(constraints, config);
    REQUIRE(result.status == IcpStatus::DomainUpdate);
    const auto* d = store.getDomain("x");
    REQUIRE(d != nullptr);
    REQUIRE(d->hasLower);
    REQUIRE(d->hasUpper);
    CHECK(d->lower.value == -4);
    CHECK(d->upper.value == 4);
    CHECK(contains(d->lower.reasons, 2));
    CHECK(contains(d->upper.reasons, 2));
    CHECK(adapter.run(constraints, config).status == IcpStatus::NoChange);
}

TEST_CASE("ICP integer: adapter keeps progress when the budget expires") {
    auto kernel = createPolynomialKernel();
    DomainStore store;
    NiaIcpAdapter adapter(*kernel, store);
    IcpConfig config;
    config.maxIterations = 1;
    auto result = adapter.run({square(*kernel, 1, -16, Relation::Eq)}, config);
    REQUIRE(result.status == IcpStatus::UnknownBudget);
    const auto* d = store.getDomain("x");
    REQUIRE(d != nullptr);
    CHECK(d->hasLower);
    CHECK(d->hasUpper);
    CHECK(d->lower.value == -4);
    CHECK(d->upper.value == 4);
}

TEST_CASE("ICP integer: relation fallback remains available for squares") {
    auto kernel = createPolynomialKernel();
    DomainStore store;
    int coefficient = 1, constant = -4;
    Relation relation = Relation::Neq;
    SUBCASE("disequality") {
        store.addLowerBound("x", 2, lit(1));
        store.addUpperBound("x", 2, lit(3));
    }
    SUBCASE("nonunit leading coefficient") {
        coefficient = 2;
        relation = Relation::Leq;
        store.addLowerBound("x", 3, lit(1));
        store.addUpperBound("x", 4, lit(3));
    }
    NiaIcpAdapter adapter(*kernel, store);
    auto result = adapter.run({square(*kernel, coefficient, constant, relation)}, {});
    REQUIRE(result.status == IcpStatus::Conflict);
    REQUIRE(result.conflict.has_value());
    CHECK(contains(result.conflict->clause, 1));
    CHECK(contains(result.conflict->clause, 2));
    CHECK(contains(result.conflict->clause, 3));
}

TEST_CASE("ICP integer: finite enumeration checks contraction soundness") {
    auto kernel = createPolynomialKernel();
    for (int coefficient : {-2, -1, 1, 2}) {
        for (int constant : {-16, -4, -2, 0, 1}) {
            for (auto relation : {Relation::Eq, Relation::Leq, Relation::Neq}) {
                for (auto bounds : {std::pair<int,int>{-5,5}, {2,3}, {5,6}, {-3,-2}}) {
                    CAPTURE(coefficient); CAPTURE(constant);
                    CAPTURE(static_cast<int>(relation));
                    CAPTURE(bounds.first); CAPTURE(bounds.second);
                    DomainStore store;
                    store.addLowerBound("x", bounds.first, lit(1));
                    store.addUpperBound("x", bounds.second, lit(3));
                    NiaIcpAdapter adapter(*kernel, store);
                    IcpConfig config;
                    config.maxIterations = 8;
                    auto result = adapter.run({square(*kernel, coefficient, constant, relation)}, config);
                    bool anyModel = false;
                    for (int x = bounds.first; x <= bounds.second; ++x) {
                        int p = coefficient*x*x + constant;
                        bool satisfies = relation == Relation::Eq ? p == 0
                            : relation == Relation::Leq ? p <= 0 : p != 0;
                        if (!satisfies) continue;
                        anyModel = true;
                        REQUIRE(result.status != IcpStatus::Conflict);
                        const auto* d = store.getDomain("x");
                        REQUIRE(d != nullptr);
                        CHECK(d->lower.value <= x);
                        CHECK(d->upper.value >= x);
                    }
                    if (result.status == IcpStatus::Conflict) CHECK_FALSE(anyModel);
                }
            }
        }
    }
}
