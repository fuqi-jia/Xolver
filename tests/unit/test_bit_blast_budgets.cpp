#include <doctest/doctest.h>
#include "base/EnvParam.h"
#include "search/bitblast/BitBlastSolver.h"

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
