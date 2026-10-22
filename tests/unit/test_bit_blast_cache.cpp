#include <doctest/doctest.h>
#include "base/EnvParam.h"
#include "base/SolveClock.h"
#include "search/bitblast/BitBlastSolver.h"
#include "search/nia/NiaSolver.h"
#include "search/arith/Reasoner.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <algorithm>
#include <chrono>
#include <stdexcept>
#include <thread>

using namespace xolver;
using Status = bitblast::BitBlastResult::Status;

namespace {
struct CacheFixture {
    std::unique_ptr<PolynomialKernel> kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    IntegerModelValidator validator{*kernel};
    bitblast::BitBlastSolver solver{*kernel};
    std::vector<NormalizedNiaConstraint> cs{{x, Relation::Geq, SatLit::positive(1)}};
    DomainStore domains;

    CacheFixture() {
        domains.addLowerBound("x", 0, SatLit::positive(2));
        domains.addUpperBound("x", 2, SatLit::positive(3));
    }
    bitblast::BitBlastResult solve() { return solver.solve(cs, domains, validator); }
};

class BitBlastStageProbe : public NiaSolver {
public:
    using NiaSolver::NiaSolver;
    std::optional<TheoryCheckResult> runStage(const std::string& name,
                                             TheoryLemmaStorage& db) {
        for (auto& stage : reasoners_)
            if (stage->name() == name) return stage->run(db, TheoryEffort::Full);
        throw std::runtime_error("missing NIA stage: " + name);
    }
};
}

TEST_CASE("BitBlastSolver: cached model respects newly excluded values") {
    CacheFixture f;
    const auto first = f.solve();
    REQUIRE(first.status == Status::Sat);
    const auto excluded = first.model.at("x");
    f.domains.excludeValue("x", excluded, SatLit::positive(4));
    const auto second = f.solve();
    REQUIRE(second.status == Status::Sat);
    CHECK(second.model.at("x") != excluded);
    CHECK(second.model.at("x") >= 0);
    CHECK(second.model.at("x") <= 2);
    f.domains.restrictToFiniteSet("x", {excluded}, SatLit::positive(5));
    CHECK(f.solve().status == Status::UnsatComplete);
}

TEST_CASE("BitBlastSolver: finite sets with equal endpoints have different solutions") {
    CacheFixture f;
    f.cs = {{f.kernel->sub(f.x, f.kernel->mkConst(1)), Relation::Eq, SatLit::positive(1)}};
    DomainStore before = f.domains;
    before.restrictToFiniteSet("x", {mpz_class(0), mpz_class(2)}, SatLit::positive(4));
    REQUIRE(f.solver.solve(f.cs, before, f.validator).status == Status::UnsatComplete);
    f.domains.restrictToFiniteSet("x", {mpz_class(0), mpz_class(1), mpz_class(2)}, SatLit::positive(4));
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == 1);
    CHECK(f.solver.solve(f.cs, before, f.validator).status == Status::UnsatComplete);
}

TEST_CASE("BitBlastSolver: cached model includes current domain-only variables") {
    CacheFixture f;
    for (const std::string& name : std::vector<std::string>{"y", "y:0..0;|v", std::string("y\0z", 3)}) {
        CAPTURE(name);
        DomainStore before = f.domains;
        before.addLowerBound(name, 0, SatLit::positive(4));
        before.addUpperBound(name, 0, SatLit::positive(5));
        const auto first = f.solver.solve(f.cs, before, f.validator);
        REQUIRE(first.status == Status::Sat);
        CHECK(first.model.at(name) == 0);
        DomainStore after = f.domains;
        after.addLowerBound(name, 1, SatLit::positive(4));
        after.addUpperBound(name, 1, SatLit::positive(5));
        const auto second = f.solver.solve(f.cs, after, f.validator);
        REQUIRE(second.status == Status::Sat);
        CHECK(second.model.at(name) == 1);
    }
}

TEST_CASE("BitBlastSolver: cached conflict uses each current justification and polarity") {
    // Change one reason at a time while leaving every mathematical restriction
    // identical. Returning an old reason would learn a clause about another branch.
    for (int changed = 0; changed < 5; ++changed) {
        for (bool polarityOnly : {false, true}) {
            CAPTURE(changed); CAPTURE(polarityOnly);
            CacheFixture f;
            const auto eq1 = f.kernel->sub(f.x, f.kernel->mkConst(1));
            for (bool replacement : {false, true}) {
                std::vector<SatLit> reasons;
                for (int i = 0; i < 5; ++i) {
                    reasons.push_back(replacement && i == changed
                        ? (polarityOnly ? SatLit::negative(10 + i) : SatLit::positive(20 + i))
                        : SatLit::positive(10 + i));
                }
                DomainStore d;
                d.addLowerBound("x", 0, reasons[1]);
                d.addUpperBound("x", 2, reasons[2]);
                d.restrictToFiniteSet("x", {mpz_class(0), mpz_class(2)}, reasons[3]);
                d.excludeValue("x", 2, reasons[4]);
                const auto result = f.solver.solve({{eq1, Relation::Eq, reasons[0]}}, d, f.validator);
                REQUIRE(result.status == Status::UnsatComplete);
                REQUIRE(result.conflict.has_value());
                CHECK(result.conflict->clause.size() == reasons.size());
                for (SatLit reason : reasons)
                    CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(), reason)
                          != result.conflict->clause.end());
            }
        }
    }
}

TEST_CASE("BitBlastSolver: unknown can be retried after increasing resource budgets") {
    SUBCASE("encoding budget") {
        CacheFixture f;
        f.solver.setGateBudget(1);
        REQUIRE(f.solve().status == Status::Unknown);
        f.solver.setGateBudget(2000000);
        CHECK(f.solve().status == Status::Sat);
    }
    SUBCASE("iteration budget") {
        CacheFixture f;
        f.solver.setMaxIterations(0);
        REQUIRE(f.solve().status == Status::Unknown);
        f.solver.setMaxIterations(1);
        CHECK(f.solve().status == Status::Sat);
    }
    SUBCASE("bit width") {
        CacheFixture f;
        f.domains.reset();
        f.cs = {{f.kernel->sub(f.x, f.kernel->mkConst(256)), Relation::Eq, SatLit::positive(1)}};
        f.solver.setMaxBitWidth(8);
        REQUIRE(f.solve().status == Status::Unknown);
        f.solver.setMaxBitWidth(16);
        const auto result = f.solve();
        REQUIRE(result.status == Status::Sat);
        CHECK(result.model.at("x") == 256);
    }
}

TEST_CASE("BitBlastSolver: expired attempt does not poison the next solve deadline") {
    CacheFixture f;
    struct ClockReset { ~ClockReset() { wall::endSolve(); } } reset;
    wall::beginSolve(1);
    std::this_thread::sleep_for(std::chrono::milliseconds(3));
    REQUIRE(wall::remainingMs() == 0);
    REQUIRE(f.solve().status == Status::Unknown);
    wall::endSolve();
    CHECK(f.solve().status == Status::Sat);
}

TEST_CASE("NiaSolver: early bit-blast retries changed constraints after backtracking") {
    env::Scope scope(env::Snapshot::capture({{"XOLVER_NIA_BB_EARLY_MIN_ACTIVE", "0"},
        {"XOLVER_NIA_BITBLAST_MAX_ITERS", "1"}, {"XOLVER_NIA_BITBLAST_MAX_BITWIDTH", "8"}}));
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto first = kernel->sub(kernel->pow(x, 2), kernel->mkConst(2));
    const auto second = kernel->sub(y, kernel->mkConst(1));
    BitBlastStageProbe solver(std::move(kernel));
    TheoryLemmaDatabase db;
    TheoryAtomRecord atom{1, TheoryId::NIA, false, NullExpr,
        PolynomialAtomPayload{first, Relation::Eq, RealValue::fromInt(0)}};
    solver.assertLit(atom, true, 1, SatLit::positive(1));
    REQUIRE_FALSE(solver.runStage("nia.normalize", db).has_value());
    REQUIRE_FALSE(solver.runStage("nia.bit-blast-early", db).has_value());
    solver.backtrackToLevel(0);
    atom.satVar = 2;
    atom.payload = PolynomialAtomPayload{second, Relation::Eq, RealValue::fromInt(0)};
    solver.assertLit(atom, true, 1, SatLit::positive(2));
    REQUIRE_FALSE(solver.runStage("nia.normalize", db).has_value());
    const auto result = solver.runStage("nia.bit-blast-early", db);
    REQUIRE(result.has_value());
    CHECK(result->kind == TheoryCheckResult::Kind::Consistent);
}
