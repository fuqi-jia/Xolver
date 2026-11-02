#include "search/bitblast/IntegerFiniteDomainEncoder.h"
#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>

using namespace xolver;
using namespace xolver::bitblast;

namespace {
struct Fixture {
    NativeTerms ir;
    Fixture() {
        ir.registerSort(0, SortKind::Bool); ir.setBoolSortId(0);
        ir.registerSort(1, SortKind::Int); ir.setIntSortId(1);
    }
    ExprId integer(const mpz_class& value) {
        return ir.add({Kind::ConstInt, 1, {}, Payload(value.get_str())});
    }
    ExprId variable(const char* name, SortId sort = 1) {
        return ir.add({Kind::Variable, sort, {}, Payload(std::string(name))});
    }
    ExprId term(Kind kind, std::vector<ExprId> children) {
        const bool arithmetic = kind == Kind::Add || kind == Kind::Mul || kind == Kind::Sub;
        TermExpr expression{kind, arithmetic ? SortId(1) : SortId(0), {}, {}};
        for (const auto child : children) expression.children.push_back(child);
        return ir.add(std::move(expression));
    }
    ExprId domain(ExprId variable, const std::vector<mpz_class>& points) {
        std::vector<ExprId> alternatives;
        for (const auto& point : points)
            alternatives.push_back(term(Kind::Eq, {variable, integer(point)}));
        return term(Kind::Or, std::move(alternatives));
    }
};
}

TEST_CASE("Finite integer domain: selectors and signed bits denote exactly one arbitrary-size point") {
    const mpz_class big = mpz_class(1) << 130;
    for (const auto& points : std::vector<std::vector<mpz_class>>{
            {-871, -30, 0, 1}, {-big - 3, 0, big + 7}, {17}, {4, 4, -9}}) {
        auto sat = createSatSolver();
        BitBlastEncoder encoder(*sat);
        WorkBudget budget;
        const auto domain = encodeIntegerFiniteDomain(encoder, points, budget);
        REQUIRE(domain);
        const auto& choices = domain->choices;
        REQUIRE_FALSE(choices.empty());
        for (size_t selected = 0; selected < choices.size(); ++selected) {
            REQUIRE(sat->solve({choices[selected].second}) == SatSolver::SolveResult::Sat);
            CHECK(readBitVec(*sat, domain->value) == choices[selected].first);
            for (size_t other = 0; other < choices.size(); ++other)
                CHECK(litValue(*sat, choices[other].second) == (selected == other));
        }
        std::vector<SatLit> none;
        for (const auto& choice : choices) none.push_back(choice.second.negated());
        CHECK(sat->solve(none) == SatSolver::SolveResult::Unsat);
        if (choices.size() > 1)
            CHECK(sat->solve({choices[0].second, choices[1].second}) == SatSolver::SolveResult::Unsat);
    }
}

TEST_CASE("Finite integer domain: resource exhaustion exposes no partial result") {
    auto sat = createSatSolver();
    BitBlastEncoder encoder(*sat);
    WorkBudget budget(2);
    CHECK_FALSE(encodeIntegerFiniteDomain(encoder, {0, 30, 871}, budget));
    WorkBudget available;
    CHECK_FALSE(encodeIntegerFiniteDomain(encoder, {}, available));
    CHECK_FALSE(encodeIntegerFiniteDomain(encoder, {0, 1}, available,
        std::chrono::steady_clock::time_point::min()));
    encoder.setVarBudget(encoder.varCount());
    CHECK_FALSE(encodeIntegerFiniteDomain(encoder, {-1, 30, 871}, available));
    CHECK(encoder.overflowed());
}

TEST_CASE("Eager finite domains: disjoint integer choices qualify exact linear search") {
    Fixture f;
    const auto x = f.variable("x"), y = f.variable("y");
    const std::vector<mpz_class> points{-871, -30, 0, 1};
    const auto dx = f.domain(x, points), dy = f.domain(y, points);
    const auto sum = f.term(Kind::Add, {x, y});
    const auto formula = f.term(Kind::And, {dx, dy,
        f.term(Kind::Eq, {sum, f.integer(-901)}),
        f.term(Kind::Not, {f.term(Kind::Eq, {x, f.integer(-30)})})});
    EagerBitBlastSolver solver;
    const auto result = solver.solveLinear(f.ir, {formula});
    REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == -871);
    CHECK(result.model.at("y") == -30);
}

TEST_CASE("Eager finite domains: affine alternatives intersect and reset between queries") {
    Fixture f;
    const auto x = f.variable("x");
    const auto affine = f.term(Kind::Add, {f.term(Kind::Mul, {f.integer(-3), x}), f.integer(2)});
    const auto d = f.term(Kind::Or, {
        f.term(Kind::Eq, {affine, f.integer(2603)}),
        f.term(Kind::Or, {f.term(Kind::Eq, {affine, f.integer(92)}),
                         f.term(Kind::Eq, {affine, f.integer(2)})})});
    EagerBitBlastSolver solver;
    const auto first = solver.solveLinear(f.ir, {d, f.domain(x, {-30, 871})});
    REQUIRE(first.status == EagerBitBlastSolver::Status::Sat);
    CHECK(first.model.at("x") == -30);
    CHECK(solver.solveLinear(f.ir, {d, f.domain(x, {871})}).status == EagerBitBlastSolver::Status::Unknown);
    const auto next = solver.solveLinear(f.ir, {f.term(Kind::Eq, {x, f.integer(871)})});
    REQUIRE(next.status == EagerBitBlastSolver::Status::Sat);
    CHECK(next.model.at("x") == 871);
}

TEST_CASE("Eager finite domains: conditional and mixed-variable disjunctions supply no root domain") {
    Fixture f;
    const auto x = f.variable("x"), y = f.variable("y"), p = f.variable("p", 0);
    const auto d = f.domain(x, {0, 30, 871});
    EagerBitBlastSolver solver;
    for (const auto expression : {f.term(Kind::Or, {p, d}), f.term(Kind::Implies, {p, d}),
                                 f.term(Kind::Not, {d}),
                                 f.term(Kind::Or, {d, f.term(Kind::Eq, {y, f.integer(0)})})})
        CHECK(solver.solveLinear(f.ir, {expression}).status == EagerBitBlastSolver::Status::Unknown);
    const auto guarded = f.term(Kind::Or, {d, p});
    const auto result = solver.solveLinear(f.ir, {guarded, f.term(Kind::Eq, {x, f.integer(999)})});
    REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == 999);
    CHECK(result.boolModel.at("p"));
}

TEST_CASE("Eager finite domains: point representations retain coupled radix equations") {
    Fixture f;
    const auto x = f.variable("x"), q = f.variable("q"), r = f.variable("r");
    const auto radix = f.term(Kind::Eq, {x, f.term(Kind::Add, {
        f.term(Kind::Mul, {f.integer(1024), q}), r})});
    EagerBitBlastSolver solver;
    const auto result = solver.solveLinear(f.ir, {f.domain(x, {0, 1025, 3074}), radix,
        f.term(Kind::Geq, {q, f.integer(0)}), f.term(Kind::Leq, {q, f.integer(3)}),
        f.term(Kind::Geq, {r, f.integer(0)}), f.term(Kind::Leq, {r, f.integer(1023)}),
        f.term(Kind::Not, {f.term(Kind::Eq, {x, f.integer(0)})}),
        f.term(Kind::Not, {f.term(Kind::Eq, {x, f.integer(1025)})})});
    REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("x") == 3074);
    CHECK(result.model.at("q") == 3);
    CHECK(result.model.at("r") == 2);
}
