#include "algebra/interval/IntervalOperations.h"
#include "algebra/interval/IntervalQOps.h"
#include "applications/satisfiability/smt/Solver.h"
#include "applications/verification/model_checking/Range.h"
#include "frontend/parser/NativeTheoryPolicy.h"
#include "ir/NativeBuilder.h"
#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

using namespace xolver;
namespace v = applications::verification::model_checking;
TEST_CASE("SV ranges: interval power means the requested exponent") {
    for (int lo = -3; lo <= 3; ++lo)
        for (int hi = lo; hi <= 3; ++hi)
            for (uint32_t exponent = 0; exponent <= 8; ++exponent) {
                auto integers = intervalPow({lo, hi}, exponent);
                auto rationals = intervalQPow({mpq_class(lo, 2), mpq_class(hi, 2)}, exponent);
                for (int x = lo; x <= hi; ++x) {
                    mpz_class exact = 1;
                    mpq_class fraction = 1;
                    for (uint32_t i = 0; i < exponent; ++i) {
                        exact *= x;
                        fraction *= mpq_class(x, 2);
                    }
                    CHECK(integers.contains(exact));
                    CHECK(rationals.contains(fraction));
                }
            }
    CHECK(intervalPow({2, 3}, 4).hi == 81);
    CHECK(intervalPow({-3, -2}, 6).lo == 64);
    CHECK(intervalQPow({mpq_class(1, 2), mpq_class(3, 2)}, 4).hi == mpq_class(81, 16));
}
TEST_CASE("SV ranges: prove machine product bounds and replay original premises") {
    native::Nodes b({});
    auto sort = SOMTParser::SortManager::getInt();
    auto x = b.make(sort, native::K::NT_VAR, {}, "x"), y = b.make(sort, native::K::NT_VAR, {}, "y");
    auto value = [&](const char *s) { return b.make(sort, native::K::NT_CONST, {}, s); };
    auto product = b.make(sort, native::K::NT_MUL, {x, y});
    v::Obligation o{"product",
                    {b.logical(native::K::NT_GE, {x, value("-2147483648")}),
                     b.logical(native::K::NT_LE, {x, value("2147483647")}),
                     b.logical(native::K::NT_GT, {y, value("-2147483648")}),
                     b.logical(native::K::NT_LE, {y, value("2147483647")})},
                    b.all({b.logical(native::K::NT_LE, {product, value("9223372036854775807")}),
                           b.logical(native::K::NT_GE, {product, value("-9223372036854775808")})})};
    auto answer = v::RangeSolver().solve(o);
    INFO(answer.reason);
    REQUIRE(answer.status == v::Status::Valid);
    REQUIRE(answer.certificate);
    CHECK(v::RangeCertificateSolver().solve({o, *answer.certificate}).status == v::Status::Valid);
    auto forged = *answer.certificate;
    REQUIRE(!forged.bounds.empty());
    forged.bounds[0].lower = 0;
    CHECK(v::RangeCertificateSolver().solve({o, forged}).status == v::Status::Invalid);
    auto changed = o;
    changed.assumptions.erase(changed.assumptions.begin());
    CHECK(v::RangeCertificateSolver().solve({changed, *answer.certificate}).status ==
          v::Status::Invalid);
    CHECK(v::RangeCertificateSolver(1).solve({o, *answer.certificate}).status ==
          v::Status::Unknown);
}
TEST_CASE("SV ranges: an open quartic condition is not a proof or a countermodel") {
    native::Nodes b({});
    auto x = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    auto power = b.make(x->getSort(), native::K::NT_POW, {x, b.numeral(4)});
    v::Obligation o{"quartic",
                    {b.logical(native::K::NT_GE, {x, b.numeral(2)}),
                     b.logical(native::K::NT_LE, {x, b.numeral(3)})},
                    b.logical(native::K::NT_LE, {power, b.numeral(10)})};
    CHECK(v::RangeSolver().solve(o).status == v::Status::Unknown);
    o.conclusion = b.logical(native::K::NT_LE, {power, b.numeral(81)});
    CHECK(v::RangeSolver().solve(o).status == v::Status::Valid);
    CHECK(v::RangeSolver(1).solve(o).status == v::Status::Unknown);
    o.conclusion = x;
    CHECK(v::RangeSolver().solve(o).status == v::Status::InvalidInput);
}
TEST_CASE("SV ranges: Euclidean division and remainder retain both divisor signs") {
    for (int a = -9; a <= 9; ++a)
        for (int divisor = -4; divisor <= 4; ++divisor) {
            native::Nodes b({});
            auto sort = SOMTParser::SortManager::getInt();
            auto literal = [&](int x) {
                return b.make(sort, native::K::NT_CONST, {}, std::to_string(x));
            };
            auto x = b.make(sort, native::K::NT_VAR, {}, "x");
            auto div = b.make(sort, native::K::NT_DIV_INT, {x, literal(divisor)});
            auto mod = b.make(sort, native::K::NT_MOD, {x, literal(divisor)});
            v::Obligation o{"division", {b.equal(x, literal(a))}, b.equal(div, literal(0))};
            if (!divisor) {
                CHECK(v::RangeSolver().solve(o).status == v::Status::Unknown);
                continue;
            }
            int remainder = a % divisor;
            if (remainder < 0)
                remainder += std::abs(divisor);
            int quotient = (a - remainder) / divisor;
            o.conclusion = b.all({b.equal(div, literal(quotient)),
                                  b.logical(native::K::NT_GE, {mod, literal(0)}),
                                  b.logical(native::K::NT_LT, {mod, literal(std::abs(divisor))})});
            auto answer = v::RangeSolver().solve(o);
            INFO(a, divisor, answer.reason);
            REQUIRE(answer.status == v::Status::Valid);
            CHECK(v::RangeCertificateSolver().solve({o, *answer.certificate}).status ==
                  v::Status::Valid);
        }
}
TEST_CASE("SV ranges: disjunctive bounds cannot justify a certificate") {
    native::Nodes b({});
    auto x = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    auto low = b.logical(native::K::NT_GE, {x, b.numeral(0)});
    auto high = b.logical(native::K::NT_LE, {x, b.numeral(2)});
    v::Obligation o{"disjunction",
                    {b.any({low, high})},
                    b.logical(native::K::NT_LE,
                              {b.make(x->getSort(), native::K::NT_MUL, {x, x}), b.numeral(4)})};
    CHECK(v::RangeSolver().solve(o).status == v::Status::Unknown);
    v::RangeCertificate forged{{{x, mpz_class(0), mpz_class(2), low, high}}};
    CHECK(v::RangeCertificateSolver().solve({o, forged}).status == v::Status::Invalid);
    o.assumptions = {b.all({low, high})};
    CHECK(v::RangeSolver().solve(o).status == v::Status::Valid);
}
TEST_CASE("SV ranges: nonzero guards justify sign-preserving remainder bounds") {
    native::Nodes b({});
    auto sort = SOMTParser::SortManager::getInt();
    auto x = b.make(sort, native::K::NT_VAR, {}, "x"), y = b.make(sort, native::K::NT_VAR, {}, "y");
    auto lit = [&](int v) { return b.make(sort, native::K::NT_CONST, {}, std::to_string(v)); };
    auto negative = b.logical(native::K::NT_LT, {x, lit(0)});
    auto absolute = b.choose(negative, b.make(sort, native::K::NT_NEG, {x}), x);
    auto remainder = b.make(sort, native::K::NT_MOD, {absolute, y});
    auto signedRem =
        b.choose(b.equal(y, lit(0)), x,
                 b.choose(negative, b.make(sort, native::K::NT_NEG, {remainder}), remainder));
    auto nonzero = b.negate(b.equal(y, lit(0)));
    v::Obligation o{"signed remainder",
                    {b.logical(native::K::NT_GE, {x, lit(-9)}),
                     b.logical(native::K::NT_LE, {x, lit(9)}),
                     b.logical(native::K::NT_GE, {y, lit(-5)}),
                     b.logical(native::K::NT_LE, {y, lit(5)}), nonzero},
                    b.all({b.logical(native::K::NT_GE, {signedRem, lit(-4)}),
                           b.logical(native::K::NT_LE, {signedRem, lit(4)})})};
    auto answer = v::RangeSolver().solve(o);
    REQUIRE(answer.status == v::Status::Valid);
    REQUIRE(answer.certificate);
    CHECK(v::RangeCertificateSolver().solve({o, *answer.certificate}).status == v::Status::Valid);
    o.assumptions.pop_back();
    CHECK(v::RangeSolver().solve(o).status == v::Status::Unknown);
    CHECK(v::RangeCertificateSolver().solve({o, *answer.certificate}).status == v::Status::Invalid);
    o.assumptions.push_back(b.any({nonzero, b.boolean(true)}));
    CHECK(v::RangeSolver().solve(o).status == v::Status::Unknown);
}
TEST_CASE("SV ranges: application composition preserves oracle results") {
    native::Nodes b({});
    auto x = b.make(SOMTParser::SortManager::getInt(), native::K::NT_VAR, {}, "x");
    int calls = 0;
    DecisionOracle oracle = [&](const NativeAssertions &query) {
        ++calls;
        return applications::satisfiability::smt::Solver().solve({query, {}, {}, {}});
    };
    v::Obligation o{"composition", {}, b.boolean(true)};
    auto answer = v::RangeAssistedSolver(oracle).solve(o);
    REQUIRE(answer.status == v::Status::Valid);
    CHECK(answer.method == v::VerificationMethod::Interval);
    CHECK(answer.certificate.has_value());
    CHECK(calls == 0);
    o.conclusion = b.equal(x, b.numeral(0));
    answer = v::RangeAssistedSolver(oracle).solve(o);
    CHECK(answer.status == v::Status::Invalid);
    CHECK(answer.method == v::VerificationMethod::DecisionOracle);
    CHECK(calls == 1);
    DecisionOracle unknown = [](const NativeAssertions &) { return SolverAnswer{}; };
    CHECK(v::RangeAssistedSolver(unknown).solve(o).status == v::Status::Unknown);
}
TEST_CASE("SV ranges: parsed integer disequalities preserve nonzero evidence") {
    SOMTParser::Parser parser;
    preserveNativeTheories(*parser.getOptions());
    REQUIRE(
        parser.parseStr("(set-logic ALL)(declare-const x Int)(declare-const y Int)"
                        "(assert (>= x (- 9)))(assert (<= x 9))(assert (>= y (- 5)))"
                        "(assert (<= y 5))(assert (not (= y 0)))"
                        "(assert (not (<= (ite (= y 0) x (ite (< x 0)"
                        "(- (mod (ite (< x 0) (- x) x) y)) (mod (ite (< x 0) (- x) x) y))) 4)))"));
    native::Nodes b(parser.getAssertions());
    auto assertions = parser.getAssertions();
    v::Obligation o{"parsed remainder", assertions, b.negate(assertions.back())};
    o.assumptions.pop_back();
    auto answer = v::RangeSolver().solve(o);
    INFO(answer.reason);
    REQUIRE(answer.status == v::Status::Valid);
    CHECK(v::RangeCertificateSolver().solve({o, *answer.certificate}).status == v::Status::Valid);
}
