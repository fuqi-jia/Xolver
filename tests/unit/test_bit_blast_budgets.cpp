#include <doctest/doctest.h>
#include "base/EnvParam.h"
#include "search/bitblast/BitBlastSolver.h"
#include <algorithm>

using namespace xolver;
using Status = bitblast::BitBlastResult::Status;

namespace {
struct BudgetFixture {
    std::unique_ptr<PolynomialKernel> kernel = createPolynomialKernel();
    PolyId x = kernel->mkVar(kernel->getOrCreateVar("x"));
    IntegerModelValidator validator{*kernel};
    bitblast::BitBlastSolver solver{*kernel};
    DomainStore domains;
    std::vector<NormalizedNiaConstraint> cs;

    void equalTo(const mpz_class& value) {
        cs = {{kernel->sub(x, kernel->mkConst(mpq_class(value))), Relation::Eq, SatLit::positive(1)}};
    }
    bitblast::BitBlastResult solve() { return solver.solve(cs, domains, validator); }
};
}

TEST_CASE("BitBlastSolver: iteration budget limits unbounded search and permits retry") {
    env::Scope scope(env::Snapshot::capture({{"XOLVER_NIA_BITBLAST_MAX_ITERS", "1"}}));
    BudgetFixture f;
    f.equalTo(256); // Requires ten signed bits, beyond the first two-bit box.
    REQUIRE(f.solve().status == Status::Unknown);
    f.solver.setMaxIterations(4); // Widths 2, 4, 8, 16.
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == 256);
}

TEST_CASE("BitBlastSolver: zero attempt budget applies to complete and incomplete boxes") {
    for (bool bounded : {false, true}) {
        CAPTURE(bounded);
        BudgetFixture f;
        f.equalTo(0);
        if (bounded) {
            f.domains.addLowerBound("x", 0, SatLit::positive(2));
            f.domains.addUpperBound("x", 0, SatLit::positive(3));
        }
        f.solver.setMaxIterations(0);
        REQUIRE(f.solve().status == Status::Unknown);
        f.solver.setMaxIterations(1);
        CHECK(f.solve().status == Status::Sat);
    }
}

TEST_CASE("BitBlastSolver: width cap includes bounded variables in complete and mixed boxes") {
    for (bool mixed : {false, true}) {
        CAPTURE(mixed);
        env::Scope scope(env::Snapshot::capture({{"XOLVER_NIA_BITBLAST_MAX_BITWIDTH", "8"}}));
        BudgetFixture f;
        f.equalTo(256);
        f.domains.addLowerBound("x", 256, SatLit::positive(2));
        f.domains.addUpperBound("x", 256, SatLit::positive(3));
        if (mixed) {
            const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
            f.cs.push_back({y, Relation::Eq, SatLit::positive(4)});
        }
        const auto limited = f.solve();
        REQUIRE(limited.status == Status::Unknown);
        CHECK_FALSE(limited.conflict.has_value());
        f.solver.setMaxBitWidth(10);
        const auto result = f.solve();
        REQUIRE(result.status == Status::Sat);
        CHECK(result.model.at("x") == 256);
        if (mixed) CHECK(result.model.at("y") == 0);
    }
}

TEST_CASE("BitBlastSolver: complete conflict requires the entire hard domain to fit") {
    BudgetFixture f;
    f.equalTo(257);
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 256, SatLit::positive(3));
    f.solver.setMaxBitWidth(8);
    REQUIRE(f.solve().status == Status::Unknown);
    f.solver.setMaxBitWidth(10);
    const auto result = f.solve();
    REQUIRE(result.status == Status::UnsatComplete);
    REQUIRE(result.conflict.has_value());
    CHECK(result.conflict->clause.size() == 3);
}

TEST_CASE("BitBlastSolver: zero width budget refuses encoding and can be increased") {
    BudgetFixture f;
    f.equalTo(0);
    f.solver.setMaxBitWidth(0);
    REQUIRE(f.solve().status == Status::Unknown);
    f.solver.setMaxBitWidth(1);
    CHECK(f.solve().status == Status::Sat);
}

TEST_CASE("BitBlastSolver: non-power-of-two width ceiling is reached exactly") {
    BudgetFixture f;
    f.equalTo(128); // Needs nine signed bits.
    f.solver.setMaxBitWidth(9);
    f.solver.setMaxIterations(3);
    REQUIRE(f.solve().status == Status::Unknown);
    f.solver.setMaxIterations(4); // Widths 2, 4, 8, 9.
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == 128);
}

TEST_CASE("BitBlastSolver: default cascade retains models wider than 64 bits") {
    BudgetFixture f;
    const mpz_class value = mpz_class(1) << 64;
    f.equalTo(value);
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == value);
}

TEST_CASE("BitBlastSolver: invalid configuration falls back to the complete default cascade") {
    env::Scope scope(env::Snapshot::capture({{"XOLVER_NIA_BITBLAST_MAX_ITERS", "9999"},
        {"XOLVER_NIA_BITBLAST_MAX_BITWIDTH", "4"}}));
    BudgetFixture f;
    const mpz_class value = mpz_class(1) << 64;
    f.equalTo(value);
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == value);
}

TEST_CASE("BitBlastSolver: distinct constraints survive refinement from an insufficient box") {
    BudgetFixture f;
    std::vector<PolyId> vars;
    for (int i = 0; i < 5; ++i)
        vars.push_back(f.kernel->mkVar(f.kernel->getOrCreateVar("d" + std::to_string(i))));
    unsigned reason = 1;
    for (size_t i = 0; i < vars.size(); ++i)
        for (size_t j = i + 1; j < vars.size(); ++j)
            f.cs.push_back({f.kernel->sub(vars[i], vars[j]), Relation::Neq, SatLit::positive(reason++)});
    f.solver.setMaxIterations(1); // Four signed values cannot satisfy five-way distinct.
    REQUIRE(f.solve().status == Status::Unknown);
    f.solver.setMaxIterations(2);
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    for (int i = 0; i < 5; ++i)
        for (int j = i + 1; j < 5; ++j)
            CHECK(result.model.at("d" + std::to_string(i)) != result.model.at("d" + std::to_string(j)));
}

TEST_CASE("BitBlastSolver: established contradiction precedes unrelated encoding exhaustion") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    f.cs = {{f.kernel->mkConst(1), Relation::Eq, SatLit::positive(1)},
            {f.kernel->pow(y, 8), Relation::Eq, SatLit::positive(4)}};
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 1, SatLit::positive(3));
    f.domains.addLowerBound("y", 0, SatLit::positive(5));
    f.domains.addUpperBound("y", 255, SatLit::positive(6));
    f.solver.setGateBudget(32);
    const auto result = f.solve();
    REQUIRE(result.status == Status::UnsatComplete);
    REQUIRE(result.conflict.has_value());
    CHECK(result.conflict->clause == std::vector<SatLit>{SatLit::positive(1)});
}

TEST_CASE("BitBlastSolver: early contradiction retains completeness and reason requirements") {
    for (bool bounded : {false, true}) {
        CAPTURE(bounded);
        BudgetFixture f;
        f.cs = {{f.kernel->mkConst(1), Relation::Eq,
                 bounded ? SatLit{} : SatLit::positive(1)},
                {f.x, Relation::Geq, SatLit::positive(2)}};
        if (!bounded) {
            // This two-bit contradiction has a wider integer model. It must
            // not become a global conflict merely because another fact holds.
            f.cs[0].poly = f.kernel->sub(f.x, f.kernel->mkConst(2));
            f.solver.setMaxIterations(1);
        }
        if (bounded) {
            f.domains.addLowerBound("x", 0, SatLit::positive(3));
            f.domains.addUpperBound("x", 1, SatLit::positive(4));
        }
        const auto result = f.solve();
        CHECK(result.status == Status::Unknown);
        CHECK_FALSE(result.conflict.has_value());
    }
}

TEST_CASE("BitBlastSolver: overflow contradictions do not refute a satisfiable encoding") {
    BudgetFixture f;
    f.cs = {{f.kernel->pow(f.x, 8), Relation::Eq, SatLit::positive(1)}};
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 255, SatLit::positive(3));
    f.solver.setGateBudget(16);
    const auto limited = f.solve();
    CHECK(limited.status == Status::Unknown);
    CHECK_FALSE(limited.conflict.has_value());
    f.solver.setGateBudget(2000000);
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == 0);
}

TEST_CASE("SAT backend: permanent inconsistency excludes failed assumptions") {
    auto sat = createSatSolver();
    const auto x = SatLit::positive(sat->newVar());
    sat->addClause({x});
    CHECK_FALSE(sat->inconsistent());
    REQUIRE(sat->solve({x.negated()}) == SatSolver::SolveResult::Unsat);
    CHECK_FALSE(sat->inconsistent());
    REQUIRE(sat->solve() == SatSolver::SolveResult::Sat);
    sat->addClause({x.negated()});
    CHECK(sat->inconsistent());
    CHECK(sat->solve() == SatSolver::SolveResult::Unsat);
}

TEST_CASE("BitBlastSolver: finite refutation survives connected unbounded variables") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    const auto z = f.kernel->mkVar(f.kernel->getOrCreateVar("z"));
    f.cs = {{f.kernel->sub(f.kernel->pow(f.x, 2), f.kernel->mkConst(2)),
             Relation::Eq, SatLit::positive(1)},
            {f.kernel->sub(f.kernel->add(f.x, y), z), Relation::Eq, SatLit::positive(4)}};
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 2, SatLit::positive(3));
    f.solver.setMaxIterations(1);
    const auto result = f.solve();
    REQUIRE(result.status == Status::UnsatComplete);
    REQUIRE(result.conflict.has_value());
    for (unsigned reason : {1u, 2u, 3u})
        CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(),
                        SatLit::positive(reason)) != result.conflict->clause.end());
    CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(),
                    SatLit::positive(4)) == result.conflict->clause.end());
}

TEST_CASE("BitBlastSolver: scoped refutations retain bound reasons and source polarity") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    f.cs = {{f.kernel->add(f.x, y), Relation::Eq, SatLit{}},
            {f.kernel->sub(f.kernel->pow(f.x, 2), f.kernel->mkConst(2)),
             Relation::Eq, SatLit::negative(7)}};
    f.solver.setMaxIterations(1);
    f.domains.addLowerBound("x", 0, SatLit{});
    f.domains.addUpperBound("x", 2, SatLit::positive(3));
    CHECK(f.solve().status == Status::Unknown);
    f.domains.reset();
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 2, SatLit::positive(3));
    const auto result = f.solve();
    REQUIRE(result.status == Status::UnsatComplete);
    REQUIRE(result.conflict.has_value());
    CHECK(result.conflict->clause.size() == 3);
    CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(),
                    SatLit::negative(7)) != result.conflict->clause.end());
}

TEST_CASE("BitBlastSolver: a narrow failed core refines only a candidate box") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    f.cs = {{f.kernel->sub(f.kernel->pow(f.x, 2), f.kernel->mkConst(16)),
             Relation::Eq, SatLit::positive(1)},
            {y, Relation::Eq, SatLit::positive(4)}};
    f.domains.addLowerBound("y", 0, SatLit::positive(2));
    f.domains.addUpperBound("y", 0, SatLit::positive(3));
    f.solver.setMaxIterations(1);
    const auto limited = f.solve();
    CHECK(limited.status == Status::Unknown);
    CHECK_FALSE(limited.conflict.has_value());
    f.solver.setMaxIterations(2);
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK((result.model.at("x") == 4 || result.model.at("x") == -4));
    CHECK(result.model.at("y") == 0);
}

TEST_CASE("BitBlastSolver: completed refutations survive a later encoding overflow") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    f.cs = {{f.x, Relation::Eq, SatLit::positive(1)},
            {f.kernel->sub(f.x, f.kernel->mkConst(1)), Relation::Eq, SatLit::positive(4)},
            {f.kernel->pow(y, 32), Relation::Eq, SatLit::positive(7)}};
    f.domains.addLowerBound("x", 0, SatLit::positive(2));
    f.domains.addUpperBound("x", 1, SatLit::positive(3));
    f.domains.addLowerBound("y", 0, SatLit::positive(5));
    f.domains.addUpperBound("y", 255, SatLit::positive(6));
    f.solver.setGateBudget(128);
    const auto result = f.solve();
    REQUIRE(result.status == Status::UnsatComplete);
    REQUIRE(result.conflict.has_value());
    CHECK(std::find(result.conflict->clause.begin(), result.conflict->clause.end(),
                    SatLit::positive(7)) == result.conflict->clause.end());
}

TEST_CASE("BitBlastEncoder: overflow preserves the exact SAT prefix") {
    auto sat = createSatSolver();
    bitblast::BitBlastEncoder encoder(*sat);
    encoder.setVarBudget(3);
    const auto s = encoder.mkVar(1).bits[0];
    const auto t = encoder.mkVar(1).bits[0];
    const auto e = encoder.mkVar(1).bits[0];
    encoder.assertLit(s);
    encoder.assertLit(t);
    encoder.assertLit(e.negated());
    encoder.iteGate(s, t, e);
    REQUIRE(encoder.overflowed());
    encoder.assertLit(encoder.constFalse());
    CHECK(sat->solve() == SatSolver::SolveResult::Sat);
}

TEST_CASE("BitBlastSolver: independent wide variables retain the default search reach") {
    BudgetFixture f;
    const auto y = f.kernel->mkVar(f.kernel->getOrCreateVar("y"));
    const mpz_class value = mpz_class(1) << 64;
    f.equalTo(value);
    f.cs.push_back({f.kernel->sub(y, f.kernel->mkConst(mpq_class(value))),
                    Relation::Eq, SatLit::positive(4)});
    const auto result = f.solve();
    REQUIRE(result.status == Status::Sat);
    CHECK(result.model.at("x") == value);
    CHECK(result.model.at("y") == value);
}
