#include "search/linear/NonnegativeWitness.h"
#include "base/WorkBudget.h"
#include "search/lra/GeneralSimplex.h"
#include <algorithm>
#include <cmath>
#include <limits>

namespace xolver {
std::optional<std::vector<mpq_class>> findNonnegativeWitness(
    size_t variables, std::span<const NonnegativeEquation> equations,
    std::chrono::steady_clock::time_point deadline) {
    if (!variables || variables > 512 || equations.empty() || equations.size() > 128)
        return std::nullopt;
    try {
        // Cheap tableau updates must not consume the rational reconstruction
        // quota before reaching the common deadline.
        WorkBudget numericalWork(2000000), reconstructionWork(200000);
        auto* work = &numericalWork;
        auto tick = [&](size_t amount = 1) {
            work->tick(amount);
            if (std::chrono::steady_clock::now() >= deadline)
                throw ResourceExhausted("nonnegative witness proposal exhausted");
        };
        auto bounded = [&](const mpq_class& value) {
            tick();
            if (value.get_den() <= 0 ||
                mpz_sizeinbase(value.get_num_mpz_t(), 2) > 4096 ||
                mpz_sizeinbase(value.get_den_mpz_t(), 2) > 4096)
                throw ResourceExhausted("nonnegative witness coefficient limit");
        };
        const size_t count = equations.size(), columns = variables, rhs = columns;
        std::vector<std::vector<double>> tableau(count + 1, std::vector<double>(columns + 1));
        std::vector<size_t> basis(count);
        std::vector<bool> basic(variables, false);
        for (size_t i = 0; i < count; ++i) {
            tick();
            const auto& equation = equations[i];
            bounded(equation.rhs);
            mpq_class scale = abs(equation.rhs);
            for (const auto& [column, coefficient] : equation.coefficients) {
                if (column >= variables) return std::nullopt;
                bounded(coefficient);
                const mpq_class magnitude = abs(coefficient);
                if (magnitude > scale) scale = magnitude;
            }
            if (scale == 0) scale = 1;
            const bool reversed = equation.rhs < 0;
            for (const auto& [column, coefficient] : equation.coefficients) {
                tick();
                const mpq_class normalized = coefficient / scale;
                tableau[i][column] += reversed ? -normalized.get_d() : normalized.get_d();
                if (!std::isfinite(tableau[i][column])) return std::nullopt;
            }
            const mpq_class normalized = abs(equation.rhs) / scale;
            tableau[i][rhs] = normalized.get_d();
            basis[i] = variables + i;
            for (size_t j = 0; j < variables; ++j) tableau[count][j] += tableau[i][j];
            tableau[count][rhs] += tableau[i][rhs];
        }
        constexpr double tolerance = 1e-10;
        // Artificial columns stay implicit. Once one leaves the basis it is
        // fixed to zero; every solution of the original system lies on that
        // face. The remaining artificial basic columns are unit columns.
        auto pivot = [&](size_t leaving, size_t entering) {
            const auto coefficient = tableau[leaving][entering];
            tick(columns + 1);
            for (auto& value : tableau[leaving]) {
                value /= coefficient;
                if (!std::isfinite(value)) return false;
            }
            tableau[leaving][entering] = 1;
            for (size_t i = 0; i <= count; ++i) {
                if (i == leaving) continue;
                const auto factor = tableau[i][entering];
                if (factor == 0) continue;
                tick(columns + 1);
                for (size_t j = 0; j <= columns; ++j) {
                    tableau[i][j] -= factor * tableau[leaving][j];
                    if (!std::isfinite(tableau[i][j])) return false;
                }
                tableau[i][entering] = 0;
            }
            if (basis[leaving] < variables) basic[basis[leaving]] = false;
            basis[leaving] = entering;
            basic[entering] = true;
            return true;
        };
        // Zero-right-hand-side rows can start with original variables at
        // their nonnegative boundary. Eliminate them before Phase I instead
        // of repeatedly pivoting degenerate zero-valued artificial variables.
        for (size_t i = 0; i < count; ++i) {
            tick(columns + 1);
            if (tableau[i][rhs] != 0) continue;
            size_t entering = columns;
            double largest = tolerance;
            for (size_t j = 0; j < columns; ++j) {
                const auto magnitude = std::abs(tableau[i][j]);
                if (!basic[j] && magnitude > largest) { largest = magnitude; entering = j; }
            }
            if (entering != columns && !pivot(i, entering)) return std::nullopt;
        }
        for (size_t iteration = 0; iteration < 128; ++iteration) {
            tick(columns);
            bool positiveArtificial = false;
            for (size_t i = 0; i < count; ++i)
                if (basis[i] >= variables && tableau[i][rhs] > 0) { positiveArtificial = true; break; }
            if (!positiveArtificial) break;
            size_t entering = columns;
            double best = tolerance;
            for (size_t j = 0; j < columns; ++j) {
                if (basic[j]) continue;
                const auto value = tableau[count][j];
                if (!std::isfinite(value)) return std::nullopt;
                if (value > best) { best = value; entering = j; }
            }
            if (entering == columns) break;
            size_t leaving = count;
            double ratio = std::numeric_limits<double>::infinity();
            for (size_t i = 0; i < count; ++i) {
                const auto coefficient = tableau[i][entering];
                if (coefficient <= tolerance) continue;
                const auto value = tableau[i][rhs];
                if (value < -tolerance || !std::isfinite(value)) return std::nullopt;
                const auto candidate = std::max(0.0, value) / coefficient;
                if (!std::isfinite(candidate)) return std::nullopt;
                // A tolerance tie can choose a larger step and make another
                // basic value negative. Tie only equal ratios; tiny negative
                // residuals are handled before division by a small pivot.
                if (candidate < ratio ||
                    (candidate == ratio && (leaving == count || basis[i] < basis[leaving]))) {
                    ratio = candidate; leaving = i;
                }
            }
            if (leaving == count) return std::nullopt;
            if (!pivot(leaving, entering)) return std::nullopt;
        }
        std::vector<size_t> support;
        for (size_t i = 0; i < count; ++i)
            if (basis[i] < variables) support.push_back(basis[i]);
        std::sort(support.begin(), support.end());
        support.erase(std::unique(support.begin(), support.end()), support.end());

        // Recover the entire original-variable basis, including numerically
        // zero coordinates. Dropping small values can discard necessary exact
        // weights after row scaling. Numerical weights never leave this function.
        work = &reconstructionWork;
        std::vector<std::vector<mpq_class>> exact(count, std::vector<mpq_class>(support.size() + 1));
        for (size_t i = 0; i < count; ++i) {
            tick();
            exact[i].back() = equations[i].rhs;
            for (const auto& [column, coefficient] : equations[i].coefficients) {
                tick();
                const auto found = std::lower_bound(support.begin(), support.end(), column);
                if (found != support.end() && *found == column)
                    exact[i][static_cast<size_t>(found - support.begin())] += coefficient;
            }
        }
        std::vector<size_t> pivots;
        size_t rank = 0;
        for (size_t j = 0; j < support.size() && rank < count; ++j) {
            tick();
            size_t pivot = rank;
            while (pivot < count && exact[pivot][j] == 0) { tick(); ++pivot; }
            if (pivot == count) continue;
            std::swap(exact[pivot], exact[rank]);
            const mpq_class leading = exact[rank][j];
            for (size_t k = j; k <= support.size(); ++k) {
                tick(); exact[rank][k] /= leading; bounded(exact[rank][k]);
            }
            // Keep an echelon system. Updating all preceding pivot rows here
            // computes many coefficients that recovery never reads.
            for (size_t i = rank + 1; i < count; ++i) {
                if (exact[i][j] == 0) continue;
                const mpq_class factor = exact[i][j];
                for (size_t k = j; k <= support.size(); ++k) {
                    tick(); exact[i][k] -= factor * exact[rank][k]; bounded(exact[i][k]);
                }
            }
            pivots.push_back(j);
            ++rank;
        }
        for (size_t i = rank; i < count; ++i)
            if (exact[i].back() != 0) return std::nullopt;
        std::vector<size_t> freeColumns;
        for (size_t j = 0; j < support.size(); ++j)
            if (!std::binary_search(pivots.begin(), pivots.end(), j)) freeColumns.push_back(j);
        // Recover each pivot as an affine function of the free coordinates.
        // Only the right-hand side and free coefficients need back substitution;
        // with a full-rank support this is ordinary triangular solution recovery.
        for (size_t i = rank; i-- > 0;) {
            for (size_t next = i + 1; next < rank; ++next) {
                tick();
                const size_t column = pivots[next];
                const mpq_class factor = exact[i][column];
                if (factor == 0) continue;
                exact[i].back() -= factor * exact[next].back();
                bounded(exact[i].back());
                for (const auto free : freeColumns) {
                    tick();
                    exact[i][free] -= factor * exact[next][free];
                    bounded(exact[i][free]);
                }
                exact[i][column] = 0;
            }
        }
        std::vector<mpq_class> parameters(freeColumns.size(), 0);
        const bool needsRepair = std::any_of(exact.begin(), exact.begin() + rank,
            [](const auto& row) { return row.back() < 0; });
        if (needsRepair) {
            if (freeColumns.empty()) return std::nullopt;
            // A numerical basis can be rank deficient over the rationals.
            // Its nullspace parameters must satisfy the nonnegative bounds;
            // setting all of them to zero need not produce a feasible point.
            if (freeColumns.size() == 1) {
                mpq_class lower = 0;
                std::optional<mpq_class> upper;
                for (size_t i = 0; i < rank; ++i) {
                    tick();
                    const auto& coefficient = exact[i][freeColumns[0]];
                    const auto& value = exact[i].back();
                    if (coefficient == 0) {
                        if (value < 0) return std::nullopt;
                        continue;
                    }
                    const mpq_class boundary = value / coefficient;
                    bounded(boundary);
                    if (coefficient < 0) lower = std::max(lower, boundary);
                    else if (!upper || boundary < *upper) upper = boundary;
                }
                if (upper && lower > *upper) return std::nullopt;
                parameters[0] = lower;
            } else {
                // Solve only in the exact nullspace, rather than rebuilding
                // the full coefficient LP with every proposed generator.
                GeneralSimplex simplex;
                std::vector<int> columns;
                std::vector<GeneralSimplex::ActiveBound> bounds;
                SatVar label = 0;
                for (size_t j = 0; j < freeColumns.size(); ++j) {
                    tick();
                    columns.push_back(simplex.addVar("t" + std::to_string(j)));
                    bounds.push_back({columns.back(), true,
                        BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(++label))});
                }
                for (size_t i = 0; i < rank; ++i) {
                    std::vector<std::pair<int, mpq_class>> terms;
                    for (size_t j = 0; j < columns.size(); ++j) {
                        tick();
                        if (exact[i][freeColumns[j]] != 0)
                            terms.emplace_back(columns[j], exact[i][freeColumns[j]]);
                    }
                    const auto row = simplex.addConstraint(terms, exact[i].back());
                    if (row < 0) return std::nullopt;
                    bounds.push_back({row, false,
                        BoundInfo(BoundValue(DeltaRational(0)), SatLit::positive(++label))});
                }
                if (!simplex.replaceActiveBounds(bounds, GeneralSimplex::AssignmentPolicy::Preserve) ||
                    simplex.checkUntil(deadline) != GeneralSimplex::Result::Sat) return std::nullopt;
                const auto delta = simplex.computeSafeDelta();
                for (size_t j = 0; j < columns.size(); ++j) {
                    tick();
                    const auto value = simplex.value(columns[j]);
                    parameters[j] = value.a + value.b * delta;
                    bounded(parameters[j]);
                    if (parameters[j] < 0) return std::nullopt;
                }
            }
        }
        std::vector<mpq_class> witness(variables, 0);
        for (size_t j = 0; j < freeColumns.size(); ++j)
            witness[support[freeColumns[j]]] = parameters[j];
        for (size_t i = 0; i < pivots.size(); ++i) {
            mpq_class value = exact[i].back();
            for (size_t j = 0; j < freeColumns.size(); ++j) {
                tick();
                value -= exact[i][freeColumns[j]] * parameters[j];
                bounded(value);
            }
            if (value < 0) return std::nullopt;
            witness[support[pivots[i]]] = value;
        }
        for (const auto& equation : equations) {
            mpq_class value = 0;
            for (const auto& [column, coefficient] : equation.coefficients) {
                tick(); value += coefficient * witness[column]; bounded(value);
            }
            if (value != equation.rhs) return std::nullopt;
        }
        tick();
        return witness;
    } catch (const ResourceExhausted&) {
        return std::nullopt;
    }
}
} // namespace xolver
