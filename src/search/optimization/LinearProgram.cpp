#include "search/optimization/LinearProgram.h"
#include <algorithm>
#include <cstdint>
#include <limits>
#include <stdexcept>

namespace xolver::optimization {
namespace {
mpq_class rational(mpq_class q) {
    if (q.get_den() == 0)
        throw std::invalid_argument("zero rational denominator");
    q.canonicalize();
    return q;
}
class Tableau {
    WorkBudget &budget;
    std::size_t columns;
    std::vector<std::vector<mpq_class>> rows;
    std::vector<mpq_class> rhs, costs;
    std::vector<std::size_t> basis;
    mpq_class value = 0;

    void pivot(std::size_t row, std::size_t entering) {
        const auto leaving = basis[row];
        const mpq_class divisor = rows[row][entering];
        if (divisor == 0)
            throw std::logic_error("zero simplex pivot");
        rows[row][entering] = 0;
        rows[row][leaving] = 1;
        for (auto &a : rows[row]) {
            budget.tick();
            a /= divisor;
        }
        rhs[row] /= divisor;
        for (std::size_t i = 0; i < rows.size(); ++i) {
            if (i == row || rows[i][entering] == 0)
                continue;
            const mpq_class factor = rows[i][entering];
            rows[i][entering] = 0;
            for (std::size_t j = 0; j < columns; ++j) {
                budget.tick();
                rows[i][j] -= factor * rows[row][j];
            }
            rhs[i] -= factor * rhs[row];
        }
        const mpq_class factor = costs[entering];
        costs[entering] = 0;
        for (std::size_t j = 0; j < columns; ++j) {
            budget.tick();
            costs[j] -= factor * rows[row][j];
        }
        value += factor * rhs[row];
        basis[row] = entering;
    }
    void objective(std::vector<mpq_class> coefficients) {
        costs = std::move(coefficients);
        value = 0;
        for (std::size_t i = 0; i < rows.size(); ++i) {
            const mpq_class factor = costs[basis[i]];
            costs[basis[i]] = 0;
            value += factor * rhs[i];
            for (std::size_t j = 0; j < columns; ++j) {
                budget.tick();
                costs[j] -= factor * rows[i][j];
            }
        }
    }
    std::optional<std::size_t> maximize(std::size_t allowedColumns) {
        for (;;) {
            budget.tick();
            std::size_t entering = 0;
            while (entering < allowedColumns && costs[entering] <= 0)
                ++entering;
            if (entering == allowedColumns)
                return std::nullopt;
            std::optional<std::size_t> leaving;
            mpq_class ratio;
            for (std::size_t i = 0; i < rows.size(); ++i) {
                budget.tick();
                if (rows[i][entering] <= 0)
                    continue;
                const mpq_class candidate = rhs[i] / rows[i][entering];
                if (!leaving || candidate < ratio ||
                    (candidate == ratio && basis[i] < basis[*leaving])) {
                    leaving = i;
                    ratio = candidate;
                }
            }
            if (!leaving)
                return entering;
            pivot(*leaving, entering);
        }
    }

  public:
    Tableau(const LinearProgram &p, WorkBudget &work) : budget(work) {
        const auto n = p.variables, m = p.constraints.size();
        if (n > (SIZE_MAX - m) / 2 || 2 * n + m > SIZE_MAX - m)
            throw ResourceExhausted("simplex dimensions exhausted");
        columns = 2 * n + 2 * m;
        budget.tick(columns);
        if (m && columns > SIZE_MAX / m)
            throw ResourceExhausted("simplex storage exhausted");
        budget.tick(m * columns);
        rows.assign(m, std::vector<mpq_class>(columns));
        rhs.resize(m);
        basis.resize(m);
        std::vector<mpq_class> phaseOne(columns);
        for (std::size_t i = 0; i < m; ++i) {
            if (p.constraints[i].coefficients.size() != n)
                throw std::invalid_argument("linear constraint dimension mismatch");
            rhs[i] = rational(p.constraints[i].rhs);
            const bool negative = rhs[i] < 0;
            for (std::size_t j = 0; j < n; ++j) {
                mpq_class a = rational(p.constraints[i].coefficients[j]);
                rows[i][2 * j] = negative ? -a : a;
                rows[i][2 * j + 1] = -rows[i][2 * j];
            }
            if (negative) {
                rhs[i] = -rhs[i];
                rows[i][2 * n + i] = -1;
                basis[i] = 2 * n + m + i;
                phaseOne[basis[i]] = -1;
            } else
                basis[i] = 2 * n + i;
        }
        objective(std::move(phaseOne));
    }
    Solution solve(const LinearProgram &p) {
        Solution result;
        const auto n = p.variables, nonArtificial = 2 * n + p.constraints.size();
        if (maximize(columns))
            throw std::logic_error("unbounded simplex feasibility objective");
        if (value != 0) {
            result.status = Status::Infeasible;
            return result;
        }
        for (std::size_t i = rows.size(); i-- > 0;) {
            if (basis[i] < nonArtificial)
                continue;
            std::size_t j = 0;
            while (j < nonArtificial && rows[i][j] == 0)
                ++j;
            if (j < nonArtificial)
                pivot(i, j);
            else {
                rows.erase(rows.begin() + i);
                rhs.erase(rhs.begin() + i);
                basis.erase(basis.begin() + i);
            }
        }
        std::vector<mpq_class> c(columns);
        for (std::size_t j = 0; j < n; ++j) {
            c[2 * j] = p.objective.empty() ? mpq_class(0) : rational(p.objective[j]);
            if (!p.maximize)
                c[2 * j] = -c[2 * j];
            c[2 * j + 1] = -c[2 * j];
        }
        objective(std::move(c));
        const auto unbounded = maximize(nonArtificial);
        std::vector<mpq_class> point(columns), direction(columns);
        if (unbounded)
            direction[*unbounded] = 1;
        for (std::size_t i = 0; i < rows.size(); ++i) {
            point[basis[i]] = rhs[i];
            if (unbounded)
                direction[basis[i]] = -rows[i][*unbounded];
        }
        for (std::size_t j = 0; j < n; ++j) {
            result.point.push_back(point[2 * j] - point[2 * j + 1]);
            if (unbounded)
                result.ray.push_back(direction[2 * j] - direction[2 * j + 1]);
        }
        result.status = unbounded ? Status::Unbounded : Status::Optimal;
        result.value = rational(p.offset);
        for (std::size_t j = 0; j < n && !p.objective.empty(); ++j)
            *result.value += rational(p.objective[j]) * result.point[j];
        return result;
    }
};
} // namespace
Solution solveLinear(const LinearProgram &p, WorkBudget &budget) {
    if (!p.objective.empty() && p.objective.size() != p.variables)
        throw std::invalid_argument("linear objective dimension mismatch");
    auto result = Tableau(p, budget).solve(p);
    if (result.status == Status::Infeasible)
        return result;
    // Check primal witnesses independently of tableau transformations.
    for (const auto &row : p.constraints) {
        mpq_class value = 0, slope = 0;
        for (std::size_t j = 0; j < p.variables; ++j) {
            budget.tick();
            value += rational(row.coefficients[j]) * result.point[j];
            if (!result.ray.empty())
                slope += rational(row.coefficients[j]) * result.ray[j];
        }
        if (value > rational(row.rhs) || slope > 0)
            throw std::logic_error("invalid simplex primal witness");
    }
    if (result.status == Status::Unbounded) {
        mpq_class slope = 0;
        for (std::size_t j = 0; j < p.variables; ++j)
            slope += rational(p.objective[j]) * result.ray[j];
        if (p.maximize ? slope <= 0 : slope >= 0)
            throw std::logic_error("invalid simplex recession witness");
    }
    return result;
}
Solution solveMixedInteger(const LinearProgram &p, const std::vector<bool> &integer,
                           WorkBudget &budget) {
    if (integer.size() != p.variables)
        throw std::invalid_argument("integer signature dimension mismatch");
    Solution best;
    std::vector<std::vector<Row>> pending(1);
    try {
        while (!pending.empty()) {
            budget.tick();
            auto restrictions = std::move(pending.back());
            pending.pop_back();
            auto current = p;
            current.constraints.insert(current.constraints.end(), restrictions.begin(),
                                       restrictions.end());
            auto relaxed = solveLinear(current, budget);
            if (relaxed.status == Status::Infeasible)
                continue;
            if (relaxed.status == Status::Optimal && best.value &&
                (p.maximize ? *relaxed.value <= *best.value : *relaxed.value >= *best.value))
                continue;
            std::size_t branch = 0;
            while (branch < p.variables &&
                   (!integer[branch] || relaxed.point[branch].get_den() == 1))
                ++branch;
            if (branch == p.variables) {
                if (relaxed.status == Status::Unbounded)
                    return relaxed; // Scale the rational ray to preserve all integer coordinates.
                best = std::move(relaxed);
                continue;
            }
            mpz_class floor;
            const auto &q = relaxed.point[branch];
            mpz_fdiv_q(floor.get_mpz_t(), q.get_num_mpz_t(), q.get_den_mpz_t());
            Row left{std::vector<mpq_class>(p.variables), mpq_class(floor)};
            left.coefficients[branch] = 1;
            Row right{std::vector<mpq_class>(p.variables), mpq_class(-floor - 1)};
            right.coefficients[branch] = -1;
            auto sibling = restrictions;
            sibling.push_back(std::move(right));
            restrictions.push_back(std::move(left));
            pending.push_back(std::move(sibling));
            pending.push_back(std::move(restrictions));
        }
        best.status = best.value ? Status::Optimal : Status::Infeasible;
    } catch (const ResourceExhausted &) {
        best.status = Status::Unknown;
    }
    return best;
}
Solution feasible(const LinearProgram &p, const std::vector<bool> &strict,
                  const std::vector<bool> &integer, WorkBudget &budget) {
    if (strict.size() != p.constraints.size())
        throw std::invalid_argument("strict constraint signature mismatch");
    auto query = p;
    query.objective.assign(p.variables, 0);
    query.offset = 0;
    if (std::find(strict.begin(), strict.end(), true) == strict.end())
        return solveMixedInteger(query, integer, budget);
    ++query.variables;
    for (std::size_t i = 0; i < query.constraints.size(); ++i)
        query.constraints[i].coefficients.push_back(strict[i] ? 1 : 0);
    Row upper{std::vector<mpq_class>(query.variables), 1}, lower = upper;
    upper.coefficients.back() = 1;
    lower.coefficients.back() = -1;
    lower.rhs = 0;
    query.constraints.push_back(std::move(upper));
    query.constraints.push_back(std::move(lower));
    query.objective.push_back(1);
    query.maximize = true;
    auto signature = integer;
    signature.push_back(false);
    auto result = solveMixedInteger(query, signature, budget);
    if (result.status == Status::Optimal && *result.value <= 0) {
        result = {};
        result.status = Status::Infeasible;
    } else if (!result.point.empty()) {
        result.point.pop_back();
        result.value = 0;
    }
    return result;
}
} // namespace xolver::optimization
