#include "algebra/linear/Formula.h"
#include <set>

namespace xolver::linear {
Formula::Formula(const NativeTerms &terms, const std::vector<ExprId> &roots, WorkBudget &budget)
    : terms_(terms), budget_(budget) {
    std::vector<ExprId> pending = roots;
    std::set<ExprId> seen;
    std::map<std::string, ExprId> identities;
    while (!pending.empty()) {
        budget_.tick();
        auto id = pending.back();
        pending.pop_back();
        if (!seen.insert(id).second)
            continue;
        auto e = terms_.get(id);
        if (e.kind == Kind::Variable) {
            auto name = std::get_if<std::string>(&e.payload.value);
            auto sort = terms_.sortKind(e.sort);
            if (!name || !sort ||
                (*sort != SortKind::Int && *sort != SortKind::Real && *sort != SortKind::Bool))
                throw UnsupportedFormula("linear formula variable sort unavailable");
            if (auto it = identities.find(*name); it != identities.end() && it->second != id)
                throw UnsupportedFormula("ambiguous linear variable identity");
            if (!indices_.contains(*name)) {
                identities[*name] = id;
                indices_[*name] = variables.size();
                variables.push_back({*name, *sort != SortKind::Real, *sort == SortKind::Bool});
            }
        }
        for (auto c : e.children)
            pending.push_back(c);
    }
}
Affine Formula::affine(ExprId id) const {
    Affine result{std::vector<mpq_class>(variables.size()), 0};
    std::unordered_map<std::string, mpq_class> coefficients;
    budget_.tick();
    if (!extractLinearExpr(id, terms_, coefficients, result.constant, 1, &budget_))
        throw UnsupportedFormula("non-affine arithmetic expression");
    for (const auto &[name, coefficient] : coefficients) {
        auto it = indices_.find(name);
        if (it == indices_.end() || variables[it->second].boolean)
            throw UnsupportedFormula("non-arithmetic variable in affine term");
        result.coefficients[it->second] += coefficient;
    }
    return result;
}
Disjunction Formula::combine(Disjunction a, const Disjunction &b, bool conjunction) {
    if (!conjunction) {
        budget_.tick(b.size());
        a.insert(a.end(), b.begin(), b.end());
        return a;
    }
    Disjunction result;
    for (const auto &x : a)
        for (const auto &y : b) {
            budget_.tick(x.size() + y.size() + 1);
            auto joined = x;
            joined.insert(joined.end(), y.begin(), y.end());
            result.push_back(std::move(joined));
        }
    return result;
}
Disjunction Formula::atom(Affine a, Kind kind, bool negative) {
    auto minus = [](Affine a) {
        a.constant = -a.constant;
        for (auto &c : a.coefficients)
            c = -c;
        return a;
    };
    if (kind == Kind::Eq || kind == Kind::Distinct) {
        const bool equal = (kind == Kind::Eq) != negative;
        return combine(atom(a, equal ? Kind::Leq : Kind::Lt, false),
                       atom(minus(a), equal ? Kind::Leq : Kind::Lt, false), equal);
    }
    bool strict = kind == Kind::Lt || kind == Kind::Gt;
    if (kind == Kind::Gt || kind == Kind::Geq)
        a = minus(a);
    if (negative) {
        a = minus(a);
        strict = !strict;
    }
    bool integral = true;
    mpz_class scale = 1;
    for (std::size_t i = 0; i < variables.size(); ++i) {
        if (a.coefficients[i] != 0 && !variables[i].integer)
            integral = false;
        mpz_lcm(scale.get_mpz_t(), scale.get_mpz_t(), a.coefficients[i].get_den_mpz_t());
    }
    if (integral) {
        for (auto &c : a.coefficients)
            c *= scale;
        const mpq_class rhs = -a.constant * scale;
        mpz_class bound;
        if (strict) {
            mpz_cdiv_q(bound.get_mpz_t(), rhs.get_num_mpz_t(), rhs.get_den_mpz_t());
            --bound;
        } else
            mpz_fdiv_q(bound.get_mpz_t(), rhs.get_num_mpz_t(), rhs.get_den_mpz_t());
        a.constant = -bound;
        strict = false;
    }
    return {{{std::move(a), strict}}};
}
Disjunction Formula::boolean(ExprId id, bool negative) {
    budget_.tick();
    if (++depth_ > 512) {
        --depth_;
        throw ResourceExhausted("linear formula depth exhausted");
    }
    struct Pop {
        std::size_t &n;
        ~Pop() { --n; }
    } pop{depth_};
    const auto e = terms_.get(id);
    const auto count = e.children.size();
    auto require = [&](std::size_t n) {
        if (count != n)
            throw UnsupportedFormula("Boolean arity mismatch");
    };
    if (e.kind == Kind::ConstBool) {
        const auto value = std::get_if<bool>(&e.payload.value);
        if (!value)
            throw UnsupportedFormula("invalid Boolean constant");
        return (*value != negative) ? Disjunction(1) : Disjunction{};
    }
    if (e.kind == Kind::Variable && terms_.sortKind(e.sort) == SortKind::Bool) {
        const auto index = indices_.at(std::get<std::string>(e.payload.value));
        Affine a{std::vector<mpq_class>(variables.size()), negative ? 0 : 1};
        a.coefficients[index] = negative ? 1 : -1;
        return atom(std::move(a), Kind::Leq, false);
    }
    if (e.kind == Kind::Not) {
        require(1);
        return boolean(e.children[0], !negative);
    }
    if (e.kind == Kind::And || e.kind == Kind::Or) {
        const bool conjunction = (e.kind == Kind::And) != negative;
        Disjunction result = conjunction ? Disjunction(1) : Disjunction{};
        for (auto c : e.children)
            result = combine(std::move(result), boolean(c, negative), conjunction);
        return result;
    }
    if (e.kind == Kind::Implies) {
        require(2);
        return combine(boolean(e.children[0], !negative), boolean(e.children[1], negative),
                       negative);
    }
    if (e.kind == Kind::Ite) {
        require(3);
        return combine(
            combine(boolean(e.children[0], false), boolean(e.children[1], negative), true),
            combine(boolean(e.children[0], true), boolean(e.children[2], negative), true), false);
    }
    if (e.kind == Kind::Xor ||
        ((e.kind == Kind::Eq || e.kind == Kind::Distinct) && count == 2 &&
         terms_.sortKind(terms_.get(e.children[0]).sort) == SortKind::Bool)) {
        require(2);
        const bool same = (e.kind == Kind::Eq) != negative;
        return combine(combine(boolean(e.children[0], false), boolean(e.children[1], !same), true),
                       combine(boolean(e.children[0], true), boolean(e.children[1], same), true),
                       false);
    }
    if (e.kind == Kind::Eq || e.kind == Kind::Distinct || e.kind == Kind::Lt ||
        e.kind == Kind::Leq || e.kind == Kind::Gt || e.kind == Kind::Geq) {
        if (count < 2)
            throw UnsupportedFormula("comparison needs at least two operands");
        Disjunction result = negative ? Disjunction{} : Disjunction(1);
        for (std::size_t i = 0; i + 1 < count; ++i) {
            const auto end = e.kind == Kind::Distinct ? count : i + 2;
            for (std::size_t j = i + 1; j < end; ++j) {
                auto a = affine(e.children[i]), b = affine(e.children[j]);
                a.constant -= b.constant;
                for (std::size_t k = 0; k < variables.size(); ++k)
                    a.coefficients[k] -= b.coefficients[k];
                result =
                    combine(std::move(result), atom(std::move(a), e.kind, negative), !negative);
            }
        }
        return result;
    }
    throw UnsupportedFormula("linear Boolean connective or binder unavailable");
}
Disjunction Formula::compile(const std::vector<ExprId> &roots) {
    Disjunction result(1);
    for (auto root : roots)
        result = combine(std::move(result), boolean(root, false), true);
    for (auto &branch : result)
        for (std::size_t i = 0; i < variables.size(); ++i)
            if (variables[i].boolean) {
                Affine lower{std::vector<mpq_class>(variables.size()), 0}, upper = lower;
                lower.coefficients[i] = -1;
                upper.coefficients[i] = 1;
                upper.constant = -1;
                branch.push_back({std::move(lower), false});
                branch.push_back({std::move(upper), false});
            }
    return result;
}
} // namespace xolver::linear
