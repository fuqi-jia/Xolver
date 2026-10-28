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
        const bool predicate = kind == Kind::Eq || kind == Kind::Leq || kind == Kind::Geq;
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
