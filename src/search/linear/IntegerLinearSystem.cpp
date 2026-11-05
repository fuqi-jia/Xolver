#include "search/linear/IntegerLinearSystem.h"
#include "search/presolve/IntegerLinearAlgebra.h"

#include <algorithm>
#include <numeric>
#include <stdexcept>
#include <utility>

namespace xolver {

IntegerLinearSystemSolution solveIntegerLinearSystem(
    size_t columns, const std::vector<IntegerLinearEquation>& equations) {
    const size_t rows = equations.size();

    IntegerLinearSystemSolution solution;
    solution.particular.resize(columns);
    solution.coordinatePeriods.resize(columns);
    std::vector<size_t> parent(columns);
    std::iota(parent.begin(), parent.end(), 0);
    auto root = [&](size_t column) {
        while (parent[column] != column) {
            parent[column] = parent[parent[column]];
            column = parent[column];
        }
        return column;
    };
    // Retain only nonzero entries while finding the variable components. The
    // caller's equations remain alive throughout construction of the small blocks.
    using Entry = std::pair<size_t, const mpz_class*>;
    std::vector<std::vector<Entry>> entries(rows);
    for (size_t i = 0; i < rows; ++i) {
        for (const auto& [j, coefficient] : equations[i].coefficients) {
            if (j >= columns) throw std::invalid_argument("integer system column out of range");
            if (coefficient == 0) continue;
            entries[i].emplace_back(j, &coefficient);
            const size_t a = root(entries[i].front().first), b = root(j);
            if (a != b) parent[std::max(a, b)] = std::min(a, b);
        }
        if (entries[i].empty() && equations[i].rhs != 0) {
            solution.consistent = false;
            solution.conflictRows.push_back(i);
            return solution;
        }
    }

    std::vector<std::vector<size_t>> componentColumns(columns), componentRows(columns);
    for (size_t j = 0; j < columns; ++j) componentColumns[root(j)].push_back(j);
    for (size_t i = 0; i < rows; ++i)
        if (!entries[i].empty()) componentRows[root(entries[i].front().first)].push_back(i);
    std::vector<size_t> positions(columns);
    size_t freeDimensions = 0;
    for (size_t component = 0; component < columns; ++component) {
        const auto& localColumns = componentColumns[component];
        if (localColumns.empty()) continue;
        const auto& localRows = componentRows[component];
        if (localRows.empty()) {
            // A zero column is a completely free coordinate.
            for (const size_t column : localColumns) {
                solution.coordinatePeriods[column] = 1;
                if (++freeDimensions == 1) {
                    solution.lineDirection.emplace(columns);
                    (*solution.lineDirection)[column] = 1;
                } else solution.lineDirection.reset();
            }
            continue;
        }

        for (size_t j = 0; j < localColumns.size(); ++j) positions[localColumns[j]] = j;
        IntMatrix block(localRows.size(), std::vector<mpz_class>(localColumns.size()));
        std::vector<mpz_class> blockRhs(localRows.size());
        for (size_t i = 0; i < localRows.size(); ++i) {
            blockRhs[i] = equations[localRows[i]].rhs;
            for (const auto& [column, coefficient] : entries[localRows[i]])
                block[i][positions[column]] += *coefficient;
        }
        const auto form = smithNormalForm(block);
        const auto transformed = matVec(form->U, blockRhs);
        const size_t rank = static_cast<size_t>(form->rank);
        for (size_t i = 0; i < localRows.size(); ++i) {
            const bool bad = i < rank ? transformed[i] % form->D[i][i] != 0
                                      : transformed[i] != 0;
            if (!bad) continue;
            solution.consistent = false;
            for (size_t j = 0; j < localRows.size(); ++j)
                if (form->U[i][j] != 0) solution.conflictRows.push_back(localRows[j]);
            return solution;
        }
        solution.rank += rank;
        std::vector<mpz_class> coordinates(localColumns.size());
        for (size_t i = 0; i < rank; ++i)
            coordinates[i] = transformed[i] / form->D[i][i];
        const auto origin = matVec(form->V, coordinates);
        for (size_t i = 0; i < localColumns.size(); ++i) {
            const size_t column = localColumns[i];
            solution.particular[column] = origin[i];
            auto& period = solution.coordinatePeriods[column];
            for (size_t j = rank; j < localColumns.size(); ++j)
                mpz_gcd(period.get_mpz_t(), period.get_mpz_t(), form->V[i][j].get_mpz_t());
        }
        const size_t blockFree = localColumns.size() - rank;
        if (blockFree) {
            freeDimensions += blockFree;
            if (freeDimensions == 1) {
                solution.lineDirection.emplace(columns);
                for (size_t i = 0; i < localColumns.size(); ++i)
                    (*solution.lineDirection)[localColumns[i]] = form->V[i][rank];
            } else solution.lineDirection.reset();
        }
    }
    return solution;
}

} // namespace xolver
