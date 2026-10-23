#include "quantifiers/real/Identities.h"
#include "algebra/linear/RationalSystem.h"
#include <map>
#include <set>

namespace xolver::quantifiers::real {
std::optional<SolverAnswer> solveIdentities(const Problem &p, Resources &resources) {
    std::map<VarId, std::size_t> coefficients;
    for (const auto &v : p.free) {
        if (v.boolean)
            return std::nullopt;
        coefficients.emplace(v.variable, coefficients.size());
    }
    std::set<VarId> universal;
    bool all = false;
    for (const auto &binder : p.prefix) {
        resources.tick();
        if (binder.universal) {
            if (coefficients.contains(binder.variable))
                return std::nullopt;
            universal.insert(binder.variable);
            all = true;
        } else if (all || !coefficients.contains(binder.variable))
            return std::nullopt;
    }
    std::vector<std::size_t> pending{p.root}, atoms;
    std::set<std::size_t> seen;
    SolverAnswer answer;
    while (!pending.empty()) {
        resources.tick();
        auto id = pending.back();
        pending.pop_back();
        if (!seen.insert(id).second)
            continue;
        const auto &c = p.matrix.at(id);
        if (c.kind == Connective::Kind::True)
            continue;
        if (c.kind == Connective::Kind::False) {
            answer.result = Result::Unsat;
            return answer;
        }
        if (c.kind == Connective::Kind::And) {
            pending.insert(pending.end(), c.children.begin(), c.children.end());
            continue;
        }
        if (c.kind != Connective::Kind::Atom || p.atoms.at(c.atom).relation != Relation::Eq)
            return std::nullopt;
        atoms.push_back(c.atom);
    }
    std::vector<std::vector<mpq_class>> matrix;
    std::vector<mpq_class> rhs;
    for (auto atom : atoms) {
        struct Equation {
            std::vector<mpq_class> row;
            mpq_class constant = 0;
        };
        std::map<MonomialKey, Equation> equations;
        for (const auto &[powers, value] : p.atoms[atom].polynomial.terms()) {
            resources.tick(powers.size() + 1);
            MonomialKey key;
            std::optional<std::size_t> coefficient;
            for (const auto &[v, degree] : powers) {
                if (universal.contains(v))
                    key.emplace_back(v, degree);
                else if (auto it = coefficients.find(v);
                         it != coefficients.end() && degree == 1 && !coefficient)
                    coefficient = it->second;
                else
                    return std::nullopt;
            }
            auto &equation = equations[key];
            if (equation.row.empty())
                equation.row.resize(coefficients.size());
            if (coefficient)
                equation.row[*coefficient] += value;
            else
                equation.constant += value;
        }
        for (auto &[key, equation] : equations) {
            matrix.push_back(std::move(equation.row));
            rhs.push_back(-equation.constant);
        }
    }
    if (resources.limits.work && resources.work >= resources.limits.work)
        throw Exhausted("identity coefficient budget exhausted");
    WorkBudget budget(resources.limits.work ? resources.limits.work - resources.work : 0);
    linear::Solution solution;
    try {
        solution = linear::solve(std::move(matrix), std::move(rhs), coefficients.size(), budget);
    } catch (const ResourceExhausted &e) {
        throw Exhausted(e.what());
    }
    resources.tick(budget.used());
    if (!solution.consistent) {
        answer.result = Result::Unsat;
        return answer;
    }
    // Substitute the result into the original polynomials, independently of
    // coefficient grouping. Every remaining universal polynomial must be zero.
    for (auto atom : atoms) {
        auto polynomial = p.atoms[atom].polynomial;
        for (const auto &[v, column] : coefficients) {
            resources.tick(polynomial.terms().size() + 1);
            polynomial = polynomial.substituteRational(v, solution.values[column]);
        }
        if (!polynomial.isZero())
            throw Unsupported("identity model failed polynomial substitution");
    }
    answer.result = Result::Sat;
    answer.model.emplace();
    for (const auto &v : p.free) {
        const auto &q = solution.values[coefficients.at(v.variable)];
        answer.model->numericAssignments[v.name] = RealValue::fromMpq(q);
        answer.model->assignments[v.name] = q.get_str();
    }
    return answer;
}
} // namespace xolver::quantifiers::real
