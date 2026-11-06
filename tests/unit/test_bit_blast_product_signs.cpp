#include <doctest/doctest.h>
#include "search/bitblast/PolyBitBlaster.h"
#include <array>
#include <functional>

using namespace xolver;
using namespace xolver::bitblast;

namespace {
bool comparison(const mpz_class& value, Relation relation) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Lt: return value < 0;
        case Relation::Leq: return value <= 0;
        case Relation::Gt: return value > 0;
        case Relation::Geq: return value >= 0;
    }
    return false;
}

void pin(std::vector<SatLit>& assumptions, const BitVec& bits, int value) {
    const mpz_class integer(value);
    for (unsigned i = 0; i < bits.width(); ++i)
        assumptions.push_back(mpz_tstbit(integer.get_mpz_t(), i) ? bits.bits[i] : bits.bits[i].negated());
}
}

TEST_CASE("Signed comparison encoding: unequal widths and both predicate polarities") {
    const std::array relations{Relation::Eq, Relation::Neq, Relation::Lt,
                               Relation::Leq, Relation::Gt, Relation::Geq};
    auto sat = createSatSolver();
    BitBlastEncoder encoder(*sat);
    const auto left = encoder.mkVar(2), right = encoder.mkVar(3);
    std::vector<SatLit> predicates;
    for (auto relation : relations) predicates.push_back(encoder.compare(left, right, relation));
    for (int a = -2; a <= 1; ++a) for (int b = -4; b <= 3; ++b) {
        std::vector<SatLit> assumptions;
        pin(assumptions, left, a);
        pin(assumptions, right, b);
        REQUIRE(sat->solve(assumptions) == SatSolver::SolveResult::Sat);
        std::vector<bool> observed;
        for (auto predicate : predicates) observed.push_back(litValue(*sat, predicate));
        for (size_t i = 0; i < relations.size(); ++i) {
            const bool expected = comparison(mpz_class(a-b), relations[i]);
            CHECK(observed[i] == expected);
            assumptions.push_back(expected ? predicates[i].negated() : predicates[i]);
            CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
            assumptions.pop_back();
        }
    }
    const mpz_class large = mpz_class(1) << 120;
    const std::vector<mpz_class> values{-large, -large + 1, -1, 0, 1, large - 1, large};
    for (const auto& a : values) for (const auto& b : values)
        for (auto relation : relations) {
            const auto predicate = encoder.compare(encoder.mkConst(a), encoder.mkConst(b), relation);
            CHECK(predicate == (comparison(mpz_class(a-b), relation) ? encoder.constTrue() : encoder.constFalse()));
        }
}

TEST_CASE("Integer difference encoding: exact scales rounding and general fallback") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->getOrCreateVar("x"), y = kernel->getOrCreateVar("y");
    const auto z = kernel->getOrCreateVar("z");
    const std::array relations{Relation::Eq, Relation::Neq, Relation::Lt,
                               Relation::Leq, Relation::Gt, Relation::Geq};
    size_t directCount = 0, fallbackCount = 0;
    for (const mpz_class& scale : std::vector<mpz_class>{2, 2*((mpz_class(1) << 100) + 3)})
        for (int shape = 0; shape < 3; ++shape) for (int offset = -3; offset <= 3; ++offset) {
            const bool useX = shape != 2, useY = shape != 1;
            const mpz_class constant = (scale / 2) * offset;
            std::vector<PolynomialKernel::MonomialTerm> terms{{constant, {}}};
            if (useX) terms.push_back({scale, {{x, 1}}});
            if (useY) terms.push_back({-scale, {{y, 1}}});
            const auto polynomial = kernel->mkFromMonomials(terms);
            auto sat = createSatSolver();
            BitBlastEncoder encoder(*sat);
            std::unordered_map<std::string, BitVec> variables{
                {"x", encoder.mkVar(3)}, {"y", encoder.mkVar(3)}};
            PolyBitBlaster blaster(encoder, *kernel, variables);
            std::vector<SatLit> predicates;
            for (auto relation : relations) {
                const auto direct = blaster.encodeDifferenceConstraint(polynomial, relation);
                if (direct) { ++directCount; predicates.push_back(*direct); }
                else {
                    ++fallbackCount;
                    predicates.push_back(blaster.encodeConstraint({polynomial, relation, {}}));
                }
            }
            for (int a = -4; a <= 3; ++a) for (int b = -4; b <= 3; ++b) {
                std::vector<SatLit> assumptions;
                pin(assumptions, variables.at("x"), a);
                pin(assumptions, variables.at("y"), b);
                REQUIRE(sat->solve(assumptions) == SatSolver::SolveResult::Sat);
                const mpz_class exact = scale * ((useX ? a : 0) - (useY ? b : 0)) + constant;
                for (size_t i = 0; i < relations.size(); ++i) {
                    const bool expected = comparison(exact, relations[i]);
                    assumptions.push_back(expected ? predicates[i].negated() : predicates[i]);
                    CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
                    assumptions.pop_back();
                }
            }
        }
    CHECK(directCount > 0);
    CHECK(fallbackCount > 0);
    auto sat = createSatSolver();
    BitBlastEncoder encoder(*sat);
    const std::unordered_map<std::string, BitVec> variables{
        {"x", encoder.mkVar(3)}, {"y", encoder.mkVar(3)}, {"z", encoder.mkVar(3)}};
    PolyBitBlaster blaster(encoder, *kernel, variables);
    for (const auto& terms : std::vector<std::vector<PolynomialKernel::MonomialTerm>>{
        {{1, {{x, 1}}}, {-1, {{y, 1}}}, {1, {{z, 1}}}},
        {{1, {{x, 1}}}, {-2, {{y, 1}}}},
        {{1, {{x, 1}, {y, 1}}}},
        {{1, {{z, 2}}}}})
        for (auto relation : relations)
            CHECK_FALSE(blaster.encodeDifferenceConstraint(kernel->mkFromMonomials(terms), relation));
}

TEST_CASE("polynomial product comparisons preserve zero factors and signed odd/even powers") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const auto xy = kernel->mul(x, y);
    using Value = std::function<mpz_class(mpz_class, mpz_class, mpz_class)>;
    const std::vector<std::pair<PolyId, Value>> polynomials{
        {xy, [](mpz_class a, mpz_class b, mpz_class) -> mpz_class { return a*b; }},
        {kernel->mul(kernel->mkConst(-7), kernel->mul(kernel->pow(x, 2), kernel->pow(y, 3))),
            [](mpz_class a, mpz_class b, mpz_class) -> mpz_class { return -7*a*a*b*b*b; }},
        {kernel->mul(xy, kernel->sub(y, z)),
            [](mpz_class a, mpz_class b, mpz_class c) -> mpz_class { return a*b*(b-c); }},
        {kernel->mul(kernel->mul(kernel->pow(x, 2), kernel->pow(y, 2)), kernel->sub(y, z)),
            [](mpz_class a, mpz_class b, mpz_class c) -> mpz_class { return a*a*b*b*(b-c); }},
        {kernel->add(xy, kernel->mkConst(1)),
            [](mpz_class a, mpz_class b, mpz_class) -> mpz_class { return a*b+1; }}
    };
    const std::array relations{Relation::Eq, Relation::Neq, Relation::Lt,
                               Relation::Leq, Relation::Gt, Relation::Geq};
    for (const auto& [polynomial, value] : polynomials) {
        auto sat = createSatSolver();
        BitBlastEncoder encoder(*sat);
        std::unordered_map<std::string, BitVec> variables{
            {"x", encoder.mkVar(3)}, {"y", encoder.mkVar(3)}, {"z", encoder.mkVar(3)}};
        PolyBitBlaster blaster(encoder, *kernel, variables);
        std::vector<SatLit> predicates;
        for (auto relation : relations) predicates.push_back(blaster.encodeConstraint({polynomial, relation, {}}));
        REQUIRE_FALSE(encoder.overflowed());
        for (int a = -4; a <= 3; ++a) for (int b = -4; b <= 3; ++b) for (int c = -4; c <= 3; ++c) {
            std::vector<SatLit> assumptions;
            pin(assumptions, variables.at("x"), a);
            pin(assumptions, variables.at("y"), b);
            pin(assumptions, variables.at("z"), c);
            REQUIRE(sat->solve(assumptions) == SatSolver::SolveResult::Sat);
            const auto exact = value(a, b, c);
            for (size_t i = 0; i < relations.size(); ++i) {
                const bool expected = comparison(exact, relations[i]);
                assumptions.push_back(expected ? predicates[i].negated() : predicates[i]);
                CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
                assumptions.pop_back();
            }
        }
    }
}

TEST_CASE("high degree product zero comparison fits a linear gate allocation") {
    auto kernel = createPolynomialKernel();
    auto sat = createSatSolver();
    BitBlastEncoder encoder(*sat);
    encoder.setVarBudget(1500);
    std::unordered_map<std::string, BitVec> variables;
    auto polynomial = kernel->mkConst(-3);
    for (int i = 0; i < 8; ++i) {
        const auto name = "x" + std::to_string(i);
        const auto variable = kernel->getOrCreateVar(name);
        variables.emplace(name, encoder.mkVar(64));
        polynomial = kernel->mul(polynomial, kernel->pow(kernel->mkVar(variable), i % 2 + 2));
    }
    PolyBitBlaster blaster(encoder, *kernel, variables);
    const auto zero = blaster.encodeConstraint({polynomial, Relation::Eq, {}});
    REQUIRE_FALSE(encoder.overflowed());
    CHECK(encoder.varCount() < 1200);
    std::vector<SatLit> assumptions;
    for (const auto& [name, bits] : variables) pin(assumptions, bits, name == "x0" ? 0 : -1);
    assumptions.push_back(zero.negated());
    CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
    assumptions.clear();
    for (const auto& [name, bits] : variables) { (void)name; pin(assumptions, bits, -1); }
    assumptions.push_back(zero);
    CHECK(sat->solve(assumptions) == SatSolver::SolveResult::Unsat);
}
