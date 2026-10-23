#include "applications/de/Solver.h"
#include "ir/NativeBuilder.h"
#include "quantifiers/real/Solver.h"
#include <functional>
#include <map>

namespace xolver::applications::de {
namespace {
using namespace xolver::native;
using Monomial = std::vector<unsigned>;
class PolynomialSearch {
    const Problem &p;
    Options options;
    Nodes b;
    std::vector<Monomial> monomials;
    std::vector<NativeAssertions> coefficients;
    static NativeAssertions roots(const Problem &p) {
        auto out = p.coordinates;
        out.insert(out.end(), p.parameters.begin(), p.parameters.end());
        for (const auto &e : p.equations) {
            out.push_back(e.formula);
            out.insert(out.end(), e.assumptions.begin(), e.assumptions.end());
        }
        for (const auto &j : p.jets) {
            out.push_back(j.symbol);
            out.insert(out.end(), j.arguments.begin(), j.arguments.end());
        }
        return out;
    }
    Node real(const mpq_class &q) {
        return b.make(SOMTParser::SortManager::getReal(), K::NT_CONST, {}, q.get_str());
    }
    Node substitute(Node n, const std::map<Node, Node> &replacements, std::map<Node, Node> &memo) {
        Nodes::Frame frame(b);
        if (auto it = replacements.find(n); it != replacements.end())
            return it->second;
        if (auto it = memo.find(n); it != memo.end())
            return it->second;
        if (!n || !n->getSort())
            throw std::invalid_argument("null differential expression");
        if (!n->getChildrenSize())
            return n;
        std::vector<Node> args;
        for (auto c : SOMTParser::children(n))
            args.push_back(substitute(c, replacements, memo));
        auto out = b.make(n->getSort(), n->getKind(), args, n->getName());
        memo[n] = out;
        return out;
    }
    Node polynomial(std::size_t field, const Monomial &derivative,
                    const NativeAssertions &arguments) {
        std::vector<Node> terms;
        for (std::size_t i = 0; i < monomials.size(); ++i) {
            b.budget.tick();
            mpz_class factor = 1;
            auto powers = monomials[i];
            for (std::size_t j = 0; j < powers.size(); ++j) {
                if (powers[j] < derivative[j]) {
                    factor = 0;
                    break;
                }
                for (unsigned k = 0; k < derivative[j]; ++k) {
                    b.budget.tick();
                    factor *= powers[j] - k;
                }
                powers[j] -= derivative[j];
            }
            if (factor == 0)
                continue;
            std::vector<Node> product{coefficients[field][i]};
            if (factor != 1)
                product.push_back(real(mpq_class(factor)));
            for (std::size_t j = 0; j < powers.size(); ++j)
                for (unsigned k = 0; k < powers[j]; ++k) {
                    b.budget.tick();
                    product.push_back(arguments[j]);
                }
            terms.push_back(product.size() == 1
                                ? product[0]
                                : b.make(SOMTParser::SortManager::getReal(), K::NT_MUL, product));
        }
        if (terms.empty())
            return real(0);
        return terms.size() == 1 ? terms[0]
                                 : b.make(SOMTParser::SortManager::getReal(), K::NT_ADD, terms);
    }
    NativeAssertions obligations() {
        std::map<Node, Node> jets;
        for (const auto &jet : p.jets)
            jets[jet.symbol] = polynomial(jet.field, jet.order,
                                          jet.arguments.empty() ? p.coordinates : jet.arguments);
        std::map<Node, Node> cache;
        NativeAssertions formulas;
        for (const auto &equation : p.equations) {
            NativeAssertions assumptions;
            for (auto a : equation.assumptions)
                assumptions.push_back(substitute(a, jets, cache));
            auto body = substitute(equation.formula, jets, cache);
            formulas.push_back(
                assumptions.empty() ? body : b.logical(K::NT_IMPLIES, {b.all(assumptions), body}));
        }
        auto universal = p.coordinates;
        universal.insert(universal.end(), p.parameters.begin(), p.parameters.end());
        std::map<Node, Node> bind;
        NativeAssertions declarations;
        for (auto var : universal) {
            auto fresh = b.fresh(var->getSort());
            auto bound = b.make(var->getSort(), K::NT_QUANT_VAR, {}, fresh->getName());
            bind[var] = bound;
            declarations.push_back(bound);
        }
        cache.clear();
        auto body = substitute(b.all(formulas), bind, cache);
        if (declarations.empty())
            return {body};
        declarations.insert(declarations.begin(), body);
        return {b.logical(K::NT_FORALL, declarations)};
    }
    void basis(unsigned degree) {
        monomials.clear();
        Monomial powers(p.coordinates.size(), 0);
        std::function<void(std::size_t, unsigned)> visit = [&](std::size_t position,
                                                               unsigned remaining) {
            Nodes::Frame frame(b);
            if (position == powers.size()) {
                if (options.monomialLimit && monomials.size() >= options.monomialLimit)
                    throw ResourceExhausted("differential monomial budget exhausted");
                monomials.push_back(powers);
                return;
            }
            for (unsigned i = 0;; ++i) {
                powers[position] = i;
                visit(position + 1, remaining - i);
                if (i == remaining)
                    break;
            }
        };
        visit(0, degree);
        coefficients.assign(p.fields.size(), {});
        for (auto &field : coefficients)
            for (std::size_t i = 0; i < monomials.size(); ++i)
                field.push_back(b.fresh(SOMTParser::SortManager::getReal()));
    }

  public:
    PolynomialSearch(const Problem &input, Options o)
        : p(input), options(o), b(roots(input), o.limits.work) {}
    Answer solve() {
        Answer answer;
        for (unsigned degree = 0;; ++degree) {
            basis(degree);
            auto query = obligations();
            auto result = quantifiers::real::solve(query, options.limits);
            if (result.result == Result::Unknown) {
                answer.reason = result.reason;
                return answer;
            }
            if (result.result == Result::Sat) {
                if (!result.model) {
                    answer.reason = "differential coefficient model unavailable";
                    return answer;
                }
                for (auto &field : coefficients)
                    for (auto &coefficient : field) {
                        mpq_class value = 0;
                        if (auto it = result.model->numericAssignments.find(coefficient->getName());
                            it != result.model->numericAssignments.end()) {
                            auto q = it->second.tryAsRational();
                            if (!q) {
                                answer.reason =
                                    "algebraic differential coefficient serialization unavailable";
                                return answer;
                            }
                            value = *q;
                        }
                        coefficient = real(value);
                    }
                auto checked = quantifiers::real::solve(obligations(), options.limits);
                if (checked.result != Result::Sat) {
                    answer.reason =
                        "candidate differential solution did not pass exact substitution: " +
                        checked.reason;
                    return answer;
                }
                for (std::size_t field = 0; field < p.fields.size(); ++field)
                    answer.functions.push_back(
                        polynomial(field, Monomial(p.coordinates.size(), 0), p.coordinates));
                answer.status = Status::Solved;
                return answer;
            }
            if (degree == options.polynomialDegree)
                break;
        }
        answer.reason = "polynomial ansatz degree budget exhausted; no claim about existence of "
                        "other solutions";
        return answer;
    }
};
} // namespace
Answer Solver::solve(const Problem &problem) {
    Answer answer;
    try {
        if (problem.coordinates.empty() || (kind_ == Kind::Ode && problem.coordinates.size() != 1))
            throw std::invalid_argument(
                "ODE requires one coordinate; PDE requires at least one coordinate");
        if (problem.fields.empty())
            throw std::invalid_argument("differential problem requires an unknown function");
        std::set<std::string> names;
        for (const auto &name : problem.fields)
            if (name.empty() || !names.insert(name).second)
                throw std::invalid_argument("duplicate differential field name");
        std::set<Node> allowed;
        auto variable = [&](Node n, bool real) {
            if (!n || n->getKind() != K::NT_VAR || !n->getSort() ||
                (real && !n->getSort()->isReal()) || !allowed.insert(n).second)
                throw std::invalid_argument("invalid differential variable declaration");
        };
        for (auto n : problem.coordinates)
            variable(n, true);
        for (auto n : problem.parameters)
            variable(n, false);
        for (const auto &j : problem.jets) {
            variable(j.symbol, true);
            if (j.field >= problem.fields.size() || j.order.size() != problem.coordinates.size() ||
                (!j.arguments.empty() && j.arguments.size() != problem.coordinates.size()))
                throw std::invalid_argument("invalid derivative signature");
        }
        std::set<Node> jetSymbols;
        for (const auto &j : problem.jets)
            jetSymbols.insert(j.symbol);
        for (const auto &j : problem.jets) {
            auto pending = j.arguments;
            std::set<Node> seen;
            while (!pending.empty()) {
                auto n = pending.back();
                pending.pop_back();
                if (!n)
                    throw std::invalid_argument("null jet argument");
                if (!seen.insert(n).second)
                    continue;
                if (jetSymbols.contains(n)) {
                    answer.reason =
                        "jet evaluation points depending on unknown fields require another backend";
                    return answer;
                }
                for (auto c : SOMTParser::children(n))
                    pending.push_back(c);
            }
        }
        NativeAssertions pending;
        for (const auto &e : problem.equations) {
            if (!e.formula || !e.formula->getSort() || !e.formula->getSort()->isBool())
                throw std::invalid_argument("differential obligation must be Boolean");
            pending.push_back(e.formula);
            pending.insert(pending.end(), e.assumptions.begin(), e.assumptions.end());
        }
        for (const auto &j : problem.jets)
            pending.insert(pending.end(), j.arguments.begin(), j.arguments.end());
        std::set<Node> seen;
        WorkBudget budget(options_.limits.work);
        while (!pending.empty()) {
            auto n = pending.back();
            pending.pop_back();
            budget.tick();
            if (!n)
                throw std::invalid_argument("null differential input");
            if (!seen.insert(n).second)
                continue;
            if (n->getKind() == K::NT_VAR && !allowed.contains(n))
                throw std::invalid_argument("undeclared free differential parameter");
            for (auto c : SOMTParser::children(n))
                pending.push_back(c);
        }
        return PolynomialSearch(problem, options_).solve();
    } catch (const std::invalid_argument &e) {
        answer.status = Status::InvalidInput;
        answer.reason = e.what();
    } catch (const ResourceExhausted &e) {
        answer.reason = e.what();
    } catch (const std::bad_alloc &) {
        answer.reason = "differential solver memory exhausted";
    }
    return answer;
}
} // namespace xolver::applications::de
