#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>

using namespace xolver;

namespace {
struct EagerFixture {
    NativeTerms terms;
    SortId numericSort;
    explicit EagerFixture(bool real = false) : numericSort(real ? 2 : 1) {
        terms.registerSort(0, SortKind::Bool);
        terms.registerSort(1, SortKind::Int);
        terms.registerSort(2, SortKind::Real);
        terms.setBoolSortId(0);
        terms.setIntSortId(1);
        terms.setRealSortId(2);
    }
    ExprId variable(const std::string& name) {
        return terms.add({Kind::Variable, numericSort, {}, Payload(name)});
    }
    ExprId integer(const mpz_class& value) {
        return terms.add({numericSort == 1 ? Kind::ConstInt : Kind::ConstReal,
                          numericSort, {}, Payload(value.get_str())});
    }
    ExprId binary(Kind kind, ExprId a, ExprId b) {
        const bool predicate = kind == Kind::Eq || kind == Kind::Leq || kind == Kind::Geq ||
            kind == Kind::Or || kind == Kind::Implies;
        return terms.add({kind, predicate ? SortId(0) : numericSort, {a, b}, {}});
    }
};
}

TEST_CASE("Eager numeric candidates: integral points satisfy real Boolean formulas") {
    EagerFixture fixture(true);
    const auto x = fixture.variable("x"), y = fixture.variable("y");
    const std::vector<ExprId> roots{
        fixture.binary(Kind::Or,
            fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(4)),
            fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, y, y), fixture.integer(9))),
        fixture.binary(Kind::Eq, y, fixture.integer(0)),
        fixture.binary(Kind::Geq, x, fixture.integer(0))};
    bitblast::EagerBitBlastSolver solver;
    solver.setFarkasBudget(33, 500);
    const auto result = solver.solve(fixture.terms, roots);
    REQUIRE(result.status == bitblast::EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == 2);
    CHECK(result.model.at("y") == 0);
}

TEST_CASE("Eager numeric candidates: fractional and irrational real points remain open") {
    EagerFixture fixture(true);
    const auto x = fixture.variable("x");
    const auto half = fixture.terms.add({Kind::ConstReal, 2, {}, Payload(std::string("1/2"))});
    bitblast::EagerBitBlastSolver solver;
    solver.setFarkasBudget(33, 500);
    CHECK(solver.solve(fixture.terms, {fixture.binary(Kind::Eq, x, half)}).status ==
          bitblast::EagerBitBlastSolver::Status::Unknown);
    CHECK(solver.solve(fixture.terms, {
        fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(2))}).status ==
          bitblast::EagerBitBlastSolver::Status::Unknown);
    const auto result = solver.solve(fixture.terms, {
        fixture.binary(Kind::Eq, fixture.binary(Kind::Mul, x, x), fixture.integer(4)),
        fixture.binary(Kind::Geq, x, fixture.integer(0))});
    REQUIRE(result.status == bitblast::EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == 2);
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

TEST_CASE("Finite linear decisions: refutations retain the legacy candidate contracts") {
    EagerFixture f;
    const auto x = f.variable("x"), y = f.variable("y");
    const std::vector<ExprId> box{
        f.binary(Kind::Geq, x, f.integer(0)), f.binary(Kind::Leq, x, f.integer(1)),
        f.binary(Kind::Geq, y, f.integer(0)), f.binary(Kind::Leq, y, f.integer(1))};
    auto roots = box;
    roots.push_back(f.binary(Kind::Eq, f.binary(Kind::Eq, x, f.integer(0)),
                                         f.binary(Kind::Eq, y, f.integer(0))));
    roots.push_back(f.terms.add({Kind::Distinct, 0, {x, y}, {}}));
    bitblast::EagerBitBlastSolver solver;
    CHECK(solver.solve(f.terms, roots).status == bitblast::EagerBitBlastSolver::Status::Unknown);
    CHECK(solver.solveLinear(f.terms, roots).status == bitblast::EagerBitBlastSolver::Status::Unknown);
    CHECK(solver.decide(f.terms, roots).status == bitblast::EagerBitBlastSolver::Status::Unsat);
    roots = box;
    roots.push_back(f.binary(Kind::Eq, x, f.integer(0)));
    roots.push_back(f.binary(Kind::Eq, y, f.integer(1)));
    const auto next = solver.decide(f.terms, roots);
    REQUIRE(next.status == bitblast::EagerBitBlastSolver::Status::Sat);
    CHECK(next.model.at("x") == 0);
    CHECK(next.model.at("y") == 1);
}

TEST_CASE("Finite linear decisions: signed arithmetic and Boolean structure match exhaustive domains") {
    for (const auto& [a, b] : {std::pair{-2, 1}, std::pair{1, 3}, std::pair{0, -1}}) {
        for (int threshold = -4; threshold <= 4; ++threshold) {
            for (const auto kind : {Kind::And, Kind::Or, Kind::Implies, Kind::Xor, Kind::Eq, Kind::Ite}) {
                CAPTURE(a);
                CAPTURE(b);
                CAPTURE(threshold);
                CAPTURE(static_cast<int>(kind));
                EagerFixture f;
                const auto x = f.variable("x"), y = f.variable("y");
                const auto p = f.terms.add({Kind::Variable, 0, {}, Payload(std::string("p"))});
                const auto c = f.terms.add({Kind::Variable, 0, {}, Payload(std::string("c"))});
                const auto weighted = f.binary(Kind::Add,
                    f.binary(Kind::Mul, f.integer(a), x), f.binary(Kind::Mul, f.integer(b), y));
                const auto left = f.binary(Kind::Leq, weighted, f.integer(threshold));
                const auto right = f.binary(Kind::Geq, f.binary(Kind::Sub, x, y), f.integer(1));
                const auto formula = kind == Kind::Ite ?
                    f.terms.add({Kind::Ite, 0, {c, left, right}, {}}) :
                    f.terms.add({kind, 0, {left, right}, {}});
                const std::vector<ExprId> roots{
                    f.binary(Kind::Geq, x, f.integer(-2)), f.binary(Kind::Leq, x, f.integer(2)),
                    f.binary(Kind::Geq, y, f.integer(-1)), f.binary(Kind::Leq, y, f.integer(2)),
                    f.binary(Kind::Or, p, formula), f.terms.add({Kind::Not, 0, {p}, {}})};
                auto holds = [&](const mpz_class& xv, const mpz_class& yv, bool cv) {
                    const bool l = a * xv + b * yv <= threshold, r = xv - yv >= 1;
                    if (kind == Kind::And) return l && r;
                    if (kind == Kind::Or) return l || r;
                    if (kind == Kind::Implies) return !l || r;
                    if (kind == Kind::Xor) return l != r;
                    if (kind == Kind::Eq) return l == r;
                    return cv ? l : r;
                };
                bool feasible = false;
                for (int xv = -2; xv <= 2; ++xv)
                    for (int yv = -1; yv <= 2; ++yv)
                        for (int cv = 0; cv < 2; ++cv) feasible |= holds(xv, yv, cv);
                bitblast::EagerBitBlastSolver solver;
                const auto decision = solver.decide(f.terms, roots);
                if (!feasible) CHECK(decision.status == bitblast::EagerBitBlastSolver::Status::Unsat);
                else {
                    REQUIRE(decision.status == bitblast::EagerBitBlastSolver::Status::Sat);
                    const auto xv = decision.model.at("x"), yv = decision.model.at("y");
                    CHECK((xv >= -2 && xv <= 2 && yv >= -1 && yv <= 2));
                    const auto choice = decision.boolModel.find("c");
                    CHECK(holds(xv, yv, choice != decision.boolModel.end() && choice->second));
                }
            }
        }
    }
}

TEST_CASE("Finite linear decisions: real, nonlinear and unbounded integer searches stay open") {
    {
        EagerFixture f(true);
        const auto x = f.variable("x");
        bitblast::EagerBitBlastSolver solver;
        CHECK(solver.decide(f.terms, {
            f.binary(Kind::Geq, x, f.integer(0)), f.binary(Kind::Leq, x, f.integer(1)),
            f.binary(Kind::Eq, f.binary(Kind::Mul, f.integer(2), x), f.integer(1))}).status ==
            bitblast::EagerBitBlastSolver::Status::Unknown);
    }
    {
        EagerFixture f;
        const auto x = f.variable("x"), twice = f.binary(Kind::Mul, f.integer(2), x);
        bitblast::EagerBitBlastSolver solver;
        CHECK(solver.decide(f.terms, {f.binary(Kind::Or,
            f.binary(Kind::Eq, twice, f.integer(1)),
            f.binary(Kind::Eq, twice, f.integer(3)))}).status ==
            bitblast::EagerBitBlastSolver::Status::Unknown);
    }
    {
        EagerFixture f;
        const auto x = f.variable("x"), square = f.binary(Kind::Mul, x, x);
        bitblast::EagerBitBlastSolver solver;
        CHECK(solver.decide(f.terms, {
            f.binary(Kind::Geq, x, f.integer(0)), f.binary(Kind::Leq, x, f.integer(1)),
            f.binary(Kind::Eq, f.binary(Kind::Add, square, x), f.integer(1))}).status ==
            bitblast::EagerBitBlastSolver::Status::Unknown);
    }
}

TEST_CASE("Finite linear decisions: sparse signed domains retain arbitrary-size points") {
    EagerFixture f;
    const auto x = f.variable("x"), y = f.variable("y");
    const mpz_class scale = mpz_class(1) << 130;
    const std::vector<mpz_class> points{-scale, 0, scale};
    auto domain = [&](ExprId variable) {
        TermExpr choice{Kind::Or, 0, {}, {}};
        for (const auto& point : points)
            choice.children.push_back(f.binary(Kind::Eq, variable, f.integer(point)));
        return f.terms.add(std::move(choice));
    };
    const auto dx = domain(x), dy = domain(y);
    bitblast::EagerBitBlastSolver solver;
    for (const mpz_class target : std::vector<mpz_class>{-2 * scale, -scale, 0, 1, scale, 2 * scale}) {
        bool feasible = false;
        for (const auto& xv : points) for (const auto& yv : points) feasible |= xv + yv == target;
        const auto decision = solver.decide(f.terms,
            {dx, dy, f.binary(Kind::Eq, f.binary(Kind::Add, x, y), f.integer(target))});
        if (!feasible) CHECK(decision.status == bitblast::EagerBitBlastSolver::Status::Unsat);
        else {
            REQUIRE(decision.status == bitblast::EagerBitBlastSolver::Status::Sat);
            CHECK(decision.model.at("x") + decision.model.at("y") == target);
        }
    }
}
