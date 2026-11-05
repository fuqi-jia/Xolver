#include "search/bitblast/IntegerEncodingContext.h"
#include "search/bitblast/EagerBitBlastSolver.h"
#include <doctest/doctest.h>
#include <stdexcept>

using namespace xolver;
using namespace xolver::bitblast;

namespace {

struct Fixture {
    NativeTerms terms;
    Fixture() {
        terms.registerSort(0, SortKind::Bool); terms.setBoolSortId(0);
        terms.registerSort(1, SortKind::Int); terms.setIntSortId(1);
    }
    ExprId integer(long value) {
        return terms.add({Kind::ConstInt, 1, {}, Payload(std::to_string(value))});
    }
    ExprId variable(const char* name, SortId sort = 1) {
        return terms.add({Kind::Variable, sort, {}, Payload(std::string(name))});
    }
    ExprId term(Kind kind, std::initializer_list<ExprId> children) {
        const bool arithmetic = kind == Kind::Add || kind == Kind::Mul || kind == Kind::Sub;
        TermExpr expression{kind, arithmetic ? SortId(1) : SortId(0), {}, {}};
        for (auto child : children) expression.children.push_back(child);
        return terms.add(std::move(expression));
    }
};

} // namespace

TEST_CASE("Integer encoding context: widening changes signed interpretation without retaining predicates") {
    IntegerEncodingContext context(createSatSolver(), 0);
    auto& encoder = context.encoder();
    const auto narrow = context.widen("x", 4);
    const auto impossible = encoder.eq(narrow, encoder.mkConst(13));
    REQUIRE(context.solver().solve({impossible}) == SatSolver::SolveResult::Unsat);
    const auto wide = context.widen("x", 8);
    for (long value : {13, -13, 127, -128}) {
        const auto predicate = encoder.eq(wide, encoder.mkConst(value));
        REQUIRE(context.solver().solve({predicate}) == SatSolver::SolveResult::Sat);
        CHECK(readBitVec(context.solver(), wide) == value);
        for (unsigned bit = 0; bit < narrow.width(); ++bit)
            CHECK(wide.bits[bit] == narrow.bits[bit]);
    }
    CHECK(context.solver().solve({impossible}) == SatSolver::SolveResult::Unsat);
}

TEST_CASE("Integer encoding context: constant extension preserves exact arbitrary-size values") {
    for (const mpz_class& value : std::vector<mpz_class>{(mpz_class(1) << 130) + 7,
                                                        -(mpz_class(1) << 130) - 7}) {
        IntegerEncodingContext context(createSatSolver(), 0);
        context.variables()["constant"] = context.encoder().mkConst(value);
        const auto widened = context.widen("constant", 256);
        REQUIRE(context.solver().solve() == SatSolver::SolveResult::Sat);
        CHECK(readBitVec(context.solver(), widened) == value);
        CHECK(widened.isConst);
        CHECK(widened.constValue == value);
    }
    CHECK_THROWS_AS(IntegerEncodingContext(nullptr, 0), std::invalid_argument);
}

TEST_CASE("Integer encoding context: retained leaves share the existing variable limit") {
    IntegerEncodingContext context(createSatSolver(), 8);
    const auto small = context.widen("x", 4);
    context.widen("x", 8);
    CHECK_FALSE(context.encoder().overflowed());
    CHECK(context.encoder().varCount() == 8);
    const auto unchanged = context.widen("x", 4);
    CHECK(unchanged.width() == 8);
    CHECK(unchanged.bits.front() == small.bits.front());
    context.widen("y", 1);
    CHECK(context.encoder().overflowed());
    CHECK(context.encoder().varCount() == 8);
    CHECK_THROWS_AS(context.widen("empty", 0), std::invalid_argument);
}

TEST_CASE("Eager shared widths: radix fitting and Boolean leaves follow the current signed interpretation") {
    for (bool negative : {false, true}) {
        Fixture f;
        const auto x = f.variable("x"), q = f.variable("q"), r = f.variable("r");
        const auto p = f.variable("negative", 0);
        const auto radix = f.term(Kind::Eq, {x,
            f.term(Kind::Add, {f.term(Kind::Mul, {f.integer(8), q}), r})});
        const auto square = f.term(Kind::Eq, {f.term(Kind::Mul, {q, q}), f.integer(169)});
        const auto sign = f.term(Kind::Lt, {q, f.integer(0)});
        const auto formula = f.term(Kind::And, {radix, square,
            f.term(Kind::Eq, {p, sign}), negative ? p : f.term(Kind::Not, {p}),
            f.term(Kind::Geq, {x, f.integer(negative ? -200 : 0)}),
            f.term(Kind::Leq, {x, f.integer(negative ? 0 : 200)}),
            f.term(Kind::Eq, {r, f.integer(0)})});
        EagerBitBlastSolver solver;
        const auto result = solver.solve(f.terms, {formula});
        REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
        CHECK(result.model.at("q") == (negative ? -13 : 13));
        CHECK(result.model.at("x") == 8 * result.model.at("q"));
        CHECK(result.model.at("r") == 0);
        CHECK(result.boolModel.at("negative") == negative);
    }
}

TEST_CASE("Eager shared widths: finite point selectors survive unrelated integer widening") {
    Fixture f;
    const auto x = f.variable("point"), q = f.variable("q");
    const auto points = f.term(Kind::Or, {
        f.term(Kind::Eq, {x, f.integer(-871)}),
        f.term(Kind::Eq, {x, f.integer(-30)}),
        f.term(Kind::Eq, {x, f.integer(1)})});
    const auto formula = f.term(Kind::And, {points,
        f.term(Kind::Not, {f.term(Kind::Eq, {x, f.integer(-871)})}),
        f.term(Kind::Not, {f.term(Kind::Eq, {x, f.integer(1)})}),
        f.term(Kind::Eq, {f.term(Kind::Mul, {q, q}), f.integer(169)}),
        f.term(Kind::Geq, {q, f.integer(0)})});
    EagerBitBlastSolver solver;
    const auto result = solver.solve(f.terms, {formula});
    REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
    CHECK(result.model.at("point") == -30);
    CHECK(result.model.at("q") == 13);
}

TEST_CASE("Eager shared widths: a new query releases the old SAT interpretation") {
    EagerBitBlastSolver solver;
    for (long target : {13, -13, 17}) {
        Fixture f;
        const auto x = f.variable("x");
        const auto sign = f.term(target > 0 ? Kind::Gt : Kind::Lt, {x, f.integer(0)});
        const auto square = f.term(Kind::Eq, {
            f.term(Kind::Mul, {x, x}), f.integer(target * target)});
        const auto result = solver.solve(f.terms, {sign, square});
        REQUIRE(result.status == EagerBitBlastSolver::Status::Sat);
        CHECK(result.model.at("x") == target);
    }
}
