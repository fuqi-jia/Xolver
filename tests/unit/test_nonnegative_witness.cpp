#include <doctest/doctest.h>
#include "search/linear/NonnegativeWitness.h"

using namespace xolver;
namespace {
auto deadline() { return std::chrono::steady_clock::now() + std::chrono::seconds(1); }
}

TEST_CASE("Nonnegative witness: dense signed systems recover their unique exact point") {
    for (const size_t size : {4U, 8U, 16U}) {
        for (int pattern = 0; pattern < 4; ++pattern) {
            CAPTURE(size);
            CAPTURE(pattern);
            std::vector<mpq_class> expected(size);
            for (size_t j = 0; j < size; ++j) {
                expected[j] = (j + pattern) % 4 == 0 ? mpq_class(0) :
                    mpq_class(j + 1, size + 1);
                expected[j].canonicalize();
            }
            std::vector<NonnegativeEquation> equations;
            for (size_t i = 0; i < size; ++i) {
                NonnegativeEquation equation;
                for (size_t j = 0; j < size; ++j) {
                    // Strict diagonal dominance makes this system invertible;
                    // row signs, ordering and rational scale change its basis.
                    mpq_class coefficient = i == j ? mpq_class(size + 1) :
                        mpq_class((i + j + pattern) % 2 == 0 ? -1 : 1);
                    coefficient *= mpq_class((i + pattern) % 2 == 0 ? -1 : 1,
                                              (i + pattern) % 5 + 1);
                    coefficient.canonicalize();
                    equation.coefficients.emplace_back(j, coefficient);
                    equation.rhs += coefficient * expected[j];
                }
                equations.insert(equations.begin(), std::move(equation));
            }
            const auto witness = findNonnegativeWitness(size, equations, deadline());
            REQUIRE(witness);
            CHECK(*witness == expected);
        }
    }
}

TEST_CASE("Nonnegative witness: scaled redundant systems recover exact boundary parameters") {
    for (int pattern = 0; pattern < 8; ++pattern) {
        CAPTURE(pattern);
        const std::vector<NonnegativeEquation> original{
            {{{0, 1}, {1, -1}, {2, -1}}, -1},
            {{{0, 2}, {1, -1}, {3, 1}}, 1},
            {{{0, 3}, {1, -2}, {2, -1}, {3, 1}}, 0}};
        std::vector<NonnegativeEquation> equations;
        for (size_t i = 0; i < original.size(); ++i) {
            auto equation = original[(i + pattern) % original.size()];
            mpq_class scale((i + pattern) % 2 == 0 ? -1 : 1, i + pattern + 1);
            scale.canonicalize();
            equation.rhs *= scale;
            for (auto& [column, coefficient] : equation.coefficients) {
                // Column permutation must not change the feasible cone.
                column = (column + pattern) % 4;
                coefficient *= scale;
            }
            equations.push_back(std::move(equation));
        }
        const auto witness = findNonnegativeWitness(4, equations, deadline());
        REQUIRE(witness);
        for (const auto& value : *witness) CHECK(value >= 0);
        for (const auto& equation : equations) {
            mpq_class value = 0;
            for (const auto& [column, coefficient] : equation.coefficients)
                value += coefficient * (*witness)[column];
            CHECK(value == equation.rhs);
        }
    }
}

TEST_CASE("Nonnegative witness: rational recovery respects signs and inconsistent equations") {
    const std::vector<NonnegativeEquation> equations{
        {{{0, 2}, {1, -1}}, 0}, {{{0, 1}, {1, 1}}, 1}};
    const auto witness = findNonnegativeWitness(2, equations, deadline());
    REQUIRE(witness);
    CHECK((*witness == std::vector<mpq_class>{mpq_class(1, 3), mpq_class(2, 3)}));
    const std::vector<NonnegativeEquation> impossible{{{{0, -1}}, 1}};
    CHECK_FALSE(findNonnegativeWitness(1, impossible, deadline()));
    CHECK_FALSE(findNonnegativeWitness(2, equations, std::chrono::steady_clock::now()));
    const std::vector<NonnegativeEquation> malformed{{{{2, 1}}, 0}};
    CHECK_FALSE(findNonnegativeWitness(2, malformed, deadline()));
}

TEST_CASE("Nonnegative witness: floating coincidence cannot hide a rational contradiction") {
    const mpq_class gap(1, mpz_class(1) << 200);
    const std::vector<NonnegativeEquation> equations{
        {{{0, 1}, {1, 1}}, 1}, {{{0, 1}, {1, mpq_class(1) + gap}}, mpq_class(1) - gap}};
    // Rounding makes both rows look like x+y=1. Exactly they force y=-1.
    CHECK_FALSE(findNonnegativeWitness(2, equations, deadline()));
}

TEST_CASE("Nonnegative witness: nearly equal ratios retain a feasible small coordinate") {
    const mpq_class gap(1, mpz_class("20000000000"));
    const std::vector<NonnegativeEquation> equations{
        {{{0, 1}}, mpq_class(1) + gap}, {{{0, 1000}, {1, -1}}, 1000}};
    const auto witness = findNonnegativeWitness(2, equations, deadline());
    REQUIRE(witness);
    CHECK((*witness)[0] == mpq_class(1) + gap);
    CHECK((*witness)[1] == 1000 * gap);
}

TEST_CASE("Nonnegative witness: row scaling retains arbitrarily small positive coordinates") {
    const mpq_class scale(mpz_class(1) << 60);
    const std::vector<NonnegativeEquation> equations{
        {{{0, 1}, {1, -scale}}, 0}, {{{0, 1}}, 1}};
    const auto witness = findNonnegativeWitness(2, equations, deadline());
    REQUIRE(witness);
    CHECK((*witness)[0] == 1);
    CHECK((*witness)[1] == 1 / scale);
}

TEST_CASE("Nonnegative witness: row scaling and redundant equations retain exact solutions") {
    const mpq_class huge(mpz_class(1) << 2000);
    const std::vector<NonnegativeEquation> large{
        {{{0, huge}}, huge}, {{{1, -huge}}, -huge}};
    const auto scaled = findNonnegativeWitness(2, large, deadline());
    REQUIRE(scaled);
    CHECK((*scaled == std::vector<mpq_class>{1, 1}));
    const std::vector<NonnegativeEquation> redundant{
        {{{0, 1}, {1, -1}}, 0}, {{{0, 2}, {1, -2}}, 0}, {{{2, 1}}, 1}};
    const auto witness = findNonnegativeWitness(3, redundant, deadline());
    REQUIRE(witness);
    CHECK((*witness)[0] == (*witness)[1]);
    CHECK((*witness)[0] >= 0);
    CHECK((*witness)[2] == 1);
}

TEST_CASE("Nonnegative witness: dependent equations preserve nonnegative parameter freedom") {
    const std::vector<std::vector<NonnegativeEquation>> systems{
        {{{{0, 1}, {1, -1}}, -1}, {{{0, 1}, {2, 1}}, 1},
         {{{0, 2}, {1, -1}, {2, 1}}, 0}},
        {{{{0, 1}, {1, -1}, {2, -1}}, -1}, {{{0, 2}, {1, -1}, {3, 1}}, 1},
         {{{0, 3}, {1, -2}, {2, -1}, {3, 1}}, 0}}};
    for (const auto& equations : systems) {
        const auto witness = findNonnegativeWitness(4, equations, deadline());
        REQUIRE(witness);
        for (const auto& value : *witness) CHECK(value >= 0);
        for (const auto& equation : equations) {
            mpq_class value = 0;
            for (const auto& [column, coefficient] : equation.coefficients)
                value += coefficient * (*witness)[column];
            CHECK(value == equation.rhs);
        }
    }
}
