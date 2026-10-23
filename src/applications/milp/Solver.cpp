#include "applications/milp/Solver.h"
#include "algebra/linear/RationalSystem.h"
#include <algorithm>
#include <functional>
#include <set>
namespace xolver::applications::milp {
namespace {
mpq_class canonical(mpq_class q) {
    if (q.get_den() == 0)
        throw std::invalid_argument("zero rational denominator");
    q.canonicalize();
    return q;
}
mpz_class floor(const mpq_class &q) {
    mpz_class n;
    mpz_fdiv_q(n.get_mpz_t(), q.get_num_mpz_t(), q.get_den_mpz_t());
    return n;
}
mpz_class ceil(const mpq_class &q) {
    mpz_class n;
    mpz_cdiv_q(n.get_mpz_t(), q.get_num_mpz_t(), q.get_den_mpz_t());
    return n;
}
} // namespace
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    WorkBudget budget(problem.workLimit);
    try {
        const auto n = problem.variables.size();
        std::set<std::string> names;
        std::vector<std::optional<mpq_class>> lo(n), hi(n);
        for (std::size_t i = 0; i < n; ++i) {
            const auto &v = problem.variables[i];
            if (v.name.empty() || !names.insert(v.name).second)
                throw std::invalid_argument("MILP variable names must be unique");
            if (v.lower)
                lo[i] = canonical(*v.lower);
            if (v.upper)
                hi[i] = canonical(*v.upper);
            if (v.kind == VariableKind::Binary) {
                lo[i] = lo[i] ? std::max(*lo[i], mpq_class(0)) : mpq_class(0);
                hi[i] = hi[i] ? std::min(*hi[i], mpq_class(1)) : mpq_class(1);
            }
        }
        std::vector<std::vector<mpq_class>> a;
        std::vector<mpq_class> rhs;
        auto add = [&](std::vector<mpq_class> row, mpq_class bound) {
            if (row.size() != n)
                throw std::invalid_argument("MILP constraint dimension mismatch");
            for (auto &q : row)
                q = canonical(q);
            bound = canonical(bound);
            std::size_t count = 0, index = 0;
            for (std::size_t i = 0; i < n; ++i)
                if (row[i] != 0) {
                    ++count;
                    index = i;
                }
            if (count == 1) {
                mpq_class value = bound / row[index];
                if (row[index] > 0) {
                    if (!hi[index] || value < *hi[index])
                        hi[index] = value;
                } else if (!lo[index] || value > *lo[index])
                    lo[index] = value;
            }
            a.push_back(std::move(row));
            rhs.push_back(bound);
        };
        for (const auto &c : problem.constraints) {
            if (c.relation != Relation::GreaterEqual)
                add(c.coefficients, c.rhs);
            if (c.relation != Relation::LessEqual) {
                auto row = c.coefficients;
                for (auto &q : row)
                    q = -q;
                add(std::move(row), -c.rhs);
            }
        }
        std::vector<mpq_class> objective = problem.objective;
        if (objective.empty())
            objective.resize(n);
        if (objective.size() != n)
            throw std::invalid_argument("MILP objective dimension mismatch");
        for (auto &q : objective)
            q = canonical(q);
        const auto offset = canonical(problem.objectiveOffset);
        std::vector<std::size_t> integers, continuous;
        for (std::size_t i = 0; i < n; ++i) {
            if (lo[i] && hi[i] && *lo[i] > *hi[i]) {
                answer.status = Status::Infeasible;
                return answer;
            }
            if (!lo[i] || !hi[i]) {
                answer.reason = "finite-box optimization backend requires finite bounds; general "
                                "MILP backend unavailable";
                return answer;
            }
            if (problem.variables[i].kind == VariableKind::Continuous)
                continuous.push_back(i);
            else {
                lo[i] = mpq_class(ceil(*lo[i]));
                hi[i] = mpq_class(floor(*hi[i]));
                if (*lo[i] > *hi[i]) {
                    answer.status = Status::Infeasible;
                    return answer;
                }
                integers.push_back(i);
            }
            std::vector<mpq_class> row(n);
            row[i] = 1;
            add(row, *hi[i]);
            row[i] = -1;
            add(row, -*lo[i]);
        }
        if (n > 512)
            throw ResourceExhausted("MILP enumeration depth exhausted");
        std::vector<mpq_class> point(n);
        auto accept = [&]() {
            for (std::size_t r = 0; r < a.size(); ++r) {
                mpq_class sum = 0;
                for (std::size_t i = 0; i < n; ++i) {
                    budget.tick();
                    sum += a[r][i] * point[i];
                }
                if (sum > rhs[r])
                    return;
            }
            mpq_class value = offset;
            for (std::size_t i = 0; i < n; ++i)
                value += objective[i] * point[i];
            if (!answer.objectiveValue || (problem.maximize ? value > *answer.objectiveValue
                                                            : value < *answer.objectiveValue)) {
                answer.objectiveValue = value;
                answer.assignment = point;
            }
        };
        std::function<void(std::size_t)> enumerate = [&](std::size_t next) {
            budget.tick();
            if (next < integers.size()) {
                auto i = integers[next];
                for (mpz_class v = lo[i]->get_num(); v <= hi[i]->get_num(); ++v) {
                    point[i] = v;
                    enumerate(next + 1);
                }
                return;
            }
            const auto m = continuous.size();
            if (!m) {
                accept();
                return;
            }
            std::vector<std::size_t> selected;
            std::function<void(std::size_t)> vertices = [&](std::size_t start) {
                budget.tick();
                if (selected.size() == m) {
                    std::vector<std::vector<mpq_class>> matrix;
                    std::vector<mpq_class> b;
                    for (auto r : selected) {
                        std::vector<mpq_class> row;
                        for (auto i : continuous)
                            row.push_back(a[r][i]);
                        mpq_class value = rhs[r];
                        for (auto i : integers)
                            value -= a[r][i] * point[i];
                        matrix.push_back(std::move(row));
                        b.push_back(value);
                    }
                    auto solution = linear::solve(std::move(matrix), std::move(b), m, budget);
                    if (solution.consistent && solution.rank == m) {
                        for (std::size_t j = 0; j < m; ++j)
                            point[continuous[j]] = solution.values[j];
                        accept();
                    }
                    return;
                }
                for (std::size_t r = start; r < a.size() && a.size() - r >= m - selected.size();
                     ++r) {
                    selected.push_back(r);
                    vertices(r + 1);
                    selected.pop_back();
                }
            };
            vertices(0);
        };
        enumerate(0);
        answer.status = answer.objectiveValue ? Status::Optimal : Status::Infeasible;
    } catch (const ResourceExhausted &e) {
        answer.status = Status::Unknown;
        answer.reason = e.what();
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
        answer.objectiveValue.reset();
        answer.assignment.clear();
    } catch (const std::bad_alloc &) {
        answer.status = Status::Unknown;
        answer.reason = "MILP memory exhausted";
    }
    return answer;
}
} // namespace xolver::applications::milp
