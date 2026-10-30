#include <doctest/doctest.h>
#include "search/boolean/TheoryRefutation.h"
#include "search/refute/PolynomialBooleanRefutation.h"
#include "algebra/poly/PolynomialConverter.h"
#include "base/WorkBudget.h"

using namespace xolver;

TEST_CASE("Boolean refutation: explained alternatives close the abstraction") {
    auto sat = createSatSolver();
    const auto a = sat->newVar(), b = sat->newVar();
    sat->addClause({SatLit::positive(a), SatLit::positive(b)});
    BooleanRefutationLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
    auto result = refuteBooleanTheory(*sat, [=](const SatSolver& model) {
        return std::vector<SatLit>{{a, model.value(a)}, {b, model.value(b)}};
    }, [](std::span<const SatLit> assignment) -> std::optional<std::vector<SatLit>> {
        for (auto literal : assignment)
            if (literal.sign) return std::vector<SatLit>{literal};
        return std::nullopt;
    }, limits);
    CHECK(result.refuted);
    CHECK(result.conflicts == 2);
}

TEST_CASE("Boolean refutation: open and invalid explanations cannot prove UNSAT") {
    for (bool invalid : {false, true}) {
        auto sat = createSatSolver();
        const auto a = sat->newVar();
        sat->addClause({SatLit::positive(a)});
        BooleanRefutationLimits limits;
        auto result = refuteBooleanTheory(*sat, [=](const SatSolver&) {
            return std::vector<SatLit>{SatLit::positive(a)};
        }, [=](std::span<const SatLit>) -> std::optional<std::vector<SatLit>> {
            if (invalid) return std::vector<SatLit>{SatLit::negative(a)};
            return std::nullopt;
        }, limits);
        CHECK_FALSE(result.refuted);
        CHECK(result.conflicts == 0);
    }
}

TEST_CASE("Polynomial refutation: Boolean alternatives share real and integer explanations") {
    for (auto sort : {SortKind::Int, SortKind::Real}) {
        NativeTerms terms;
        terms.registerSort(0, sort);
        terms.registerSort(1, SortKind::Bool);
        terms.setBoolSortId(1);
        auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
        auto y = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
        auto zero = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
        auto product = terms.add(TermExpr{Kind::Mul, 0, {x, y}, {}});
        auto positiveX = terms.add(TermExpr{Kind::Gt, 1, {x, zero}, {}});
        auto positiveY = terms.add(TermExpr{Kind::Gt, 1, {y, zero}, {}});
        auto equal = terms.add(TermExpr{Kind::Eq, 1, {product, zero}, {}});
        auto negative = terms.add(TermExpr{Kind::Lt, 1, {product, zero}, {}});
        auto positive = terms.add(TermExpr{Kind::Gt, 1, {product, zero}, {}});
        auto impossible = terms.add(TermExpr{Kind::Or, 1, {equal, negative}, {}});
        auto feasible = terms.add(TermExpr{Kind::Or, 1, {equal, positive}, {}});
        BooleanRefutationLimits limits;
        limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
        PolynomialBooleanStatistics stats;
        CHECK(refutePolynomialBoolean(terms, {positiveX, positiveY, impossible}, limits, &stats));
        CHECK(stats.boolean.conflicts == 2);
        CHECK_FALSE(refutePolynomialBoolean(terms, {positiveX, positiveY, feasible}, limits));
        limits.deadline = std::chrono::steady_clock::now();
        CHECK_FALSE(refutePolynomialBoolean(terms, {positiveX, positiveY, impossible}, limits));
    }
}

TEST_CASE("Polynomial refutation: unsupported products remain open and Boolean equality is exact") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    terms.registerSort(1, SortKind::Bool);
    terms.setBoolSortId(1);
    auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    auto zero = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    auto one = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(1))});
    auto divzero = terms.add(TermExpr{Kind::Div, 0, {one, zero}, {}});
    auto product = terms.add(TermExpr{Kind::Mul, 0, {x, divzero}, {}});
    auto fixed = terms.add(TermExpr{Kind::Eq, 1, {x, one}, {}});
    auto partial = terms.add(TermExpr{Kind::Eq, 1, {product, zero}, {}});
    BooleanRefutationLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
    CHECK_FALSE(refutePolynomialBoolean(terms, {fixed, partial}, limits));
    auto positive = terms.add(TermExpr{Kind::Gt, 1, {x, zero}, {}});
    auto negative = terms.add(TermExpr{Kind::Lt, 1, {x, zero}, {}});
    auto truth = terms.add(TermExpr{Kind::ConstBool, 1, {}, Payload(true)});
    auto equivalence = terms.add(TermExpr{Kind::Eq, 1, {positive, truth}, {}});
    CHECK(refutePolynomialBoolean(terms, {negative, equivalence}, limits));
}

TEST_CASE("Polynomial conversion: bounded expansion and unrepresentable powers stay open") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    auto y = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    auto sum = terms.add(TermExpr{Kind::Add, 0, {x, y}, {}});
    auto twenty = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(20))});
    auto power = terms.add(TermExpr{Kind::Pow, 0, {sum, twenty}, {}});
    auto kernel = createPolynomialKernel();
    WorkBudget budget(64);
    PolynomialConverter bounded(*kernel, &budget);
    CHECK_THROWS_AS(bounded.convert(power, terms), ResourceExhausted);
    PolynomialConverter ordinary(*kernel);
    for (int64_t exponent : {int64_t(4294967296LL), int64_t(4294967297LL)}) {
        auto count = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(exponent)});
        auto huge = terms.add(TermExpr{Kind::Pow, 0, {x, count}, {}});
        CHECK_FALSE(ordinary.convert(huge, terms).ok());
    }
}
