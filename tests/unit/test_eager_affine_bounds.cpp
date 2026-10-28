#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>

using namespace xolver;

namespace {
struct EagerFixture {
    NativeTerms terms;
    EagerFixture() {
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        terms.setBoolSortId(0);
        terms.setIntSortId(1);
    }
    ExprId variable(const std::string& name) {
        return terms.add({Kind::Variable, 1, {}, Payload(name)});
    }
    ExprId integer(const mpz_class& value) {
        return terms.add({Kind::ConstInt, 1, {}, Payload(value.get_str())});
    }
    ExprId binary(Kind kind, ExprId a, ExprId b) {
        const bool predicate = kind == Kind::Eq || kind == Kind::Leq || kind == Kind::Geq ||
            kind == Kind::Or || kind == Kind::Implies;
        return terms.add({kind, predicate ? SortId(0) : SortId(1), {a, b}, {}});
    }
};
}

TEST_CASE("Eager affine bounds: derived wide integer models survive the cascade") {
    EagerFixture fixture;
    const auto x = fixture.variable("x");
    const auto y = fixture.variable("y");
    const mpz_class scale = mpz_class(1) << 70;
    const auto scaled = fixture.binary(Kind::Mul, fixture.integer(scale), y);
    const std::vector<ExprId> roots{
        fixture.binary(Kind::Eq, y, fixture.integer(1)),
        fixture.binary(Kind::Eq, x, scaled),
        fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(scale*scale))};
    bitblast::EagerBitBlastSolver solver;
    solver.setFarkasBudget(33, 500);
    const auto result = solver.solve(fixture.terms, roots);
    REQUIRE(result.status == bitblast::EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == scale);
    CHECK(result.model.at("y") == 1);
}

TEST_CASE("Eager affine bounds: signed offset inequalities refresh between queries") {
    EagerFixture fixture;
    const auto x = fixture.variable("x");
    const auto y = fixture.variable("y");
    const auto shifted = fixture.binary(Kind::Add, y, fixture.integer(3));
    bitblast::EagerBitBlastSolver solver;
    solver.setFarkasBudget(33, 500);
    for (int sign : {-1, 1}) {
        const mpz_class value = sign * (mpz_class(1) << 70);
        const mpz_class expected = value + 3;
        const std::vector<ExprId> roots{
            fixture.binary(Kind::Eq, y, fixture.integer(value)),
            fixture.binary(Kind::Leq, x, shifted),
            fixture.binary(Kind::Geq, x, shifted),
            fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(expected*expected))};
        const auto result = solver.solve(fixture.terms, roots);
        REQUIRE(result.status == bitblast::EagerBitBlastSolver::Status::Sat);
        CHECK(result.model.at("x") == expected);
        CHECK(result.model.at("y") == value);
    }
}

TEST_CASE("Eager affine bounds: branch predicates never become root premises") {
    for (auto context : {Kind::Not, Kind::Or, Kind::Implies, Kind::Ite}) {
        EagerFixture fixture;
        const auto x = fixture.variable("x");
        const auto y = fixture.variable("y");
        const auto c = fixture.terms.add({Kind::Variable, 0, {}, Payload(std::string("c"))});
        const auto badBranch = fixture.binary(Kind::Eq, x,
            fixture.binary(Kind::Mul, fixture.integer(mpz_class(1) << 70), y));
        const auto xZero = fixture.binary(Kind::Eq, x, fixture.integer(0));
        ExprId nested;
        if (context == Kind::Not)
            nested = fixture.terms.add({Kind::Not, 0, {badBranch}, {}});
        else if (context == Kind::Ite)
            nested = fixture.terms.add({Kind::Ite, 0, {c, badBranch, xZero}, {}});
        else nested = fixture.binary(context, context == Kind::Or ? badBranch : c,
                                     context == Kind::Or ? xZero : badBranch);
        const std::vector<ExprId> roots{nested, xZero,
            fixture.binary(Kind::Eq, y, fixture.integer(1)),
            fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(0)),
            fixture.terms.add({Kind::Not, 0, {c}, {}})};
        bitblast::EagerBitBlastSolver solver;
        solver.setFarkasBudget(33, 500);
        const auto result = solver.solve(fixture.terms, roots);
        REQUIRE(result.status == bitblast::EagerBitBlastSolver::Status::Sat);
        CHECK(result.model.at("x") == 0);
        CHECK(result.model.at("y") == 1);
    }
}
