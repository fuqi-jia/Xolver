#include <doctest/doctest.h>

#include "search/linear/IntegerLinearSystem.h"
#include "search/presolve/IntegerLinearAlgebra.h"

#include <algorithm>
#include <random>
#include <stdexcept>

using namespace xolver;

namespace {
std::vector<IntegerLinearEquation> equationsFor(
    const IntMatrix& matrix, const std::vector<mpz_class>& rhs) {
    std::vector<IntegerLinearEquation> equations(matrix.size());
    for (size_t i = 0; i < matrix.size(); ++i) {
        equations[i].rhs = rhs[i];
        for (size_t j = 0; j < matrix[i].size(); ++j)
            if (matrix[i][j] != 0) equations[i].coefficients.emplace_back(j, matrix[i][j]);
    }
    return equations;
}

bool wholeSystemConsistent(const IntMatrix& matrix, const std::vector<mpz_class>& rhs) {
    const auto form = smithNormalForm(matrix);
    const auto transformed = matVec(form->U, rhs);
    for (size_t i = 0; i < matrix.size(); ++i) {
        if (i < static_cast<size_t>(form->rank)) {
            if (transformed[i] % form->D[i][i] != 0) return false;
        } else if (transformed[i] != 0) return false;
    }
    return true;
}

void checkSystem(const IntMatrix& matrix, const std::vector<mpz_class>& rhs) {
    const size_t columns = matrix.empty() ? 0 : matrix.front().size();
    const auto result = solveIntegerLinearSystem(columns, equationsFor(matrix, rhs));
    REQUIRE(result.consistent == wholeSystemConsistent(matrix, rhs));
    if (!result.consistent) {
        REQUIRE_FALSE(result.conflictRows.empty());
        IntMatrix subsystem;
        std::vector<mpz_class> subRhs;
        for (const size_t row : result.conflictRows) {
            REQUIRE(row < matrix.size());
            subsystem.push_back(matrix[row]); subRhs.push_back(rhs[row]);
        }
        CHECK_FALSE(wholeSystemConsistent(subsystem, subRhs));
        return;
    }
    const auto form = smithNormalForm(matrix);
    REQUIRE(result.particular.size() == columns);
    REQUIRE(result.coordinatePeriods.size() == columns);
    CHECK(result.rank == static_cast<size_t>(form->rank));
    CHECK(matVec(matrix, result.particular) == rhs);
    const auto transformed = matVec(form->U, rhs);
    std::vector<mpz_class> coordinates(columns);
    for (int i = 0; i < form->rank; ++i)
        coordinates[i] = transformed[i] / form->D[i][i];
    const auto reference = matVec(form->V, coordinates);
    for (size_t i = 0; i < columns; ++i) {
        mpz_class period = 0;
        for (size_t j = form->rank; j < columns; ++j)
            mpz_gcd(period.get_mpz_t(), period.get_mpz_t(), form->V[i][j].get_mpz_t());
        CHECK(result.coordinatePeriods[i] == period);
        if (period == 0) CHECK(result.particular[i] == reference[i]);
        else CHECK((result.particular[i] - reference[i]) % period == 0);
    }
    const bool line = columns - result.rank == 1;
    REQUIRE(result.lineDirection.has_value() == line);
    if (line) {
        const auto& direction = *result.lineDirection;
        REQUIRE(direction.size() == columns);
        CHECK(matVec(matrix, direction) == std::vector<mpz_class>(matrix.size()));
        bool same = true, opposite = true;
        for (size_t i = 0; i < columns; ++i) {
            same &= direction[i] == form->V[i][form->rank];
            opposite &= direction[i] == -form->V[i][form->rank];
        }
        CHECK((same || opposite));
        for (int parameter : {-7, -1, 0, 1, 5}) {
            auto point = result.particular;
            for (size_t i = 0; i < columns; ++i) point[i] += parameter * direction[i];
            CHECK(matVec(matrix, point) == rhs);
        }
    }
}
}

TEST_CASE("integer equality systems: independent blocks preserve exact coordinate lattices") {
    constexpr size_t blocks = 48;
    IntMatrix matrix(blocks, std::vector<mpz_class>(2 * blocks));
    std::vector<mpz_class> rhs(blocks);
    for (size_t i = 0; i < blocks; ++i) {
        matrix[i][i] = 2;
        matrix[i][i + blocks] = 4;
        rhs[i] = 6;
    }
    checkSystem(matrix, rhs);
    const auto result = solveIntegerLinearSystem(2 * blocks, equationsFor(matrix, rhs));
    CHECK(result.rank == blocks);
    for (size_t i = 0; i < blocks; ++i) {
        CHECK(result.coordinatePeriods[i] == 2);
        CHECK(result.coordinatePeriods[i + blocks] == 1);
    }
    // Reconnect two former components, then withdraw that equality again.
    matrix.push_back(std::vector<mpz_class>(2 * blocks));
    matrix.back()[0] = 1; matrix.back()[1] = -1; rhs.push_back(0);
    checkSystem(matrix, rhs);
    matrix.pop_back(); rhs.pop_back(); checkSystem(matrix, rhs);
}

TEST_CASE("integer equality systems: inconsistent block retains only supporting original rows") {
    const IntMatrix matrix{{2, 1, 0, 0}, {0, 0, 3, 6}, {0, 1, 0, 0}};
    const std::vector<mpz_class> rhs{0, 9, 1};
    checkSystem(matrix, rhs);
    const auto result = solveIntegerLinearSystem(4, equationsFor(matrix, rhs));
    REQUIRE_FALSE(result.consistent);
    auto rows = result.conflictRows;
    std::sort(rows.begin(), rows.end());
    CHECK(rows == std::vector<size_t>{0, 2});
}

TEST_CASE("integer equality systems: empty zero and free coordinates remain exact") {
    checkSystem({}, {});
    checkSystem({{}}, {0});
    checkSystem({{}, {}}, {0, 1});
    checkSystem({{0, 0, 0}}, {0});
    checkSystem({{0, 0, 0}}, {1});
    checkSystem({{0, 3, 0}}, {6});
    checkSystem({{0, 3, 0}, {0, 0, 0}}, {6, 0});
    checkSystem({{0, 3}, {0, 0}}, {6, 0});
}

TEST_CASE("integer equality systems: one-dimensional reconstruction and large coefficients") {
    checkSystem({{2, 4, 0}, {0, 0, -3}}, {6, -9});
    const mpz_class huge = mpz_class(1) << 140;
    checkSystem({{huge, 2 * huge, 0}, {0, 0, -3}}, {3 * huge, -9});
    checkSystem({{huge, 2 * huge, 0}, {0, 0, -3}}, {3 * huge + 1, -9});
}

TEST_CASE("integer equality systems: sparse rectangular systems match whole exact forms") {
    std::minstd_rand random(810371);
    for (int sample = 0; sample < 48; ++sample) {
        const size_t rows = 1 + random() % 5, columns = 1 + random() % 6;
        IntMatrix matrix(rows, std::vector<mpz_class>(columns));
        std::vector<mpz_class> point(columns);
        for (auto& value : point) value = static_cast<int>(random() % 7) - 3;
        for (auto& row : matrix)
            for (auto& value : row)
                if (random() % 3 == 0) value = static_cast<int>(random() % 11) - 5;
        auto rhs = matVec(matrix, point);
        checkSystem(matrix, rhs);
        rhs[random() % rows] += 1;
        checkSystem(matrix, rhs);
    }
}

TEST_CASE("integer equality systems: sparse repeated coefficients retain cancellation") {
    const std::vector<IntegerLinearEquation> rows{{{{1, 2}, {0, 1}, {1, 2}, {0, 1}}, 6}};
    const auto result = solveIntegerLinearSystem(2, rows);
    REQUIRE(result.consistent);
    REQUIRE(result.coordinatePeriods == std::vector<mpz_class>{2, 1});
    CHECK(matVec(IntMatrix{{2, 4}}, result.particular) == std::vector<mpz_class>{6});
    const auto canceled = solveIntegerLinearSystem(1, {{{{0, 7}, {0, -7}}, 1}});
    CHECK_FALSE(canceled.consistent);
    CHECK(canceled.conflictRows == std::vector<size_t>{0});
    const auto free = solveIntegerLinearSystem(1, {});
    REQUIRE(free.lineDirection.has_value());
    CHECK(*free.lineDirection == std::vector<mpz_class>{1});
}

TEST_CASE("integer equality systems: invalid sparse columns fail explicitly") {
    CHECK_THROWS_AS(solveIntegerLinearSystem(1, {{{{1, 2}}, 0}}), std::invalid_argument);
    CHECK_THROWS_AS(solveIntegerLinearSystem(0, {{{{0, 0}}, 0}}), std::invalid_argument);
}
