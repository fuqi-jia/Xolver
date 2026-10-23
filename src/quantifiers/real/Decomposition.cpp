#include "quantifiers/real/Problem.h"
#include "search/nra/backend/LibpolyBackend.h"
#include "search/nra/lazard/SubresultantChain.h"
#include "search/nra/lazard/RationalRootIsolation.h"
#include <algorithm>
#include <map>
#include <optional>
#include <unordered_map>

namespace xolver::quantifiers::real {
namespace {
using Poly = RationalPolynomial;
std::string key(const Poly& polynomial) {
    std::string result;
    for (const auto& [powers, coefficient] : polynomial.terms()) {
        result += coefficient.get_str() + ':';
        for (const auto& [v, degree] : powers) result += std::to_string(v) + '^' + std::to_string(degree) + ';';
        result += '|';
    }
    return result;
}
class Decomposition {
    const Problem& problem_;
    PolynomialKernel& kernel_;
    Resources& resources_;
    LibpolyBackend algebra_;
    std::vector<VarId> order_;
    std::unordered_map<VarId, std::size_t> levels_;
    std::vector<Poly> polynomials_;
    std::vector<std::vector<std::size_t>> byLevel_;
    std::map<std::string, std::size_t> unique_;
    std::map<std::string, PolyId> kernelPolynomials_;
    std::vector<PolyId> atoms_;
    std::vector<int> atomLevels_;
    SamplePoint sample_, witness_;
    std::size_t intern(Poly p) {
        resources_.tick(p.terms().size() + 1);
        p.normalize();
        if (p.isConstant()) return std::numeric_limits<std::size_t>::max();
        const mpq_class lead = p.terms().rbegin()->second;
        p *= mpq_class(1) / lead;
        auto identity = key(p);
        if (auto found = unique_.find(identity); found != unique_.end()) return found->second;
        if (resources_.limits.polynomials && polynomials_.size() >= resources_.limits.polynomials)
            throw Exhausted("real projection polynomial budget exhausted");
        const auto id = polynomials_.size();
        const int level = p.highestVariableLevel(order_);
        if (level < 0) throw std::logic_error("real projection contains an unbound variable");
        unique_.emplace(std::move(identity), id);
        byLevel_.at(level).push_back(id);
        polynomials_.push_back(std::move(p));
        return id;
    }
    PolyId kernelPolynomial(const Poly& polynomial) {
        const auto identity = key(polynomial);
        if (auto found = kernelPolynomials_.find(identity); found != kernelPolynomials_.end()) return found->second;
        const auto normalized = polynomial.toPrimitiveInteger(kernel_);
        if (!normalized.ok()) throw Unsupported("real polynomial conversion did not complete");
        kernelPolynomials_.emplace(identity, normalized.poly);
        return normalized.poly;
    }
    void chain(const Poly& a, const Poly& b, VarId variable) {
        const auto dimension = std::int64_t(a.degree(variable)) + b.degree(variable);
        if (resources_.limits.projectionMatrix && dimension > resources_.limits.projectionMatrix)
            throw Exhausted("real projection matrix budget exhausted");
        resources_.tick(a.terms().size() + b.terms().size() + 1);
        auto result = principalSubresultantCoefficients(a, b, variable,
            resources_.limits.projectionMatrix ? resources_.limits.projectionMatrix : std::numeric_limits<int>::max(), &kernel_);
        if (result.budgetExceeded) throw Exhausted("real subresultant budget exhausted");
        for (auto& polynomial : result.psc) intern(std::move(polynomial));
    }
    void project() {
        clearPscChainCache();
        for (const auto& atom : problem_.atoms) intern(atom.polynomial);
        // Collins projection uses every iterated reductum. A sample-dependent
        // leading-degree drop must still have its coefficient/PSC conditions in
        // the lower-dimensional decomposition, including on section cells.
        for (std::size_t level = order_.size(); level-- > 1;) {
            const auto variable = order_[level];
            const auto initial = byLevel_[level];
            for (auto id : initial) {
                auto reductum = polynomials_.at(id);
                while (reductum.degree(variable) > 0) {
                    resources_.tick();
                    const auto degree = reductum.degree(variable);
                    const auto leading = reductum.leadingCoefficient(variable);
                    intern(leading);
                    reductum -= leading * Poly::fromVar(variable, degree, 1);
                    intern(reductum);
                }
            }
            const auto basis = byLevel_[level];
            for (auto id : basis) {
                const auto p = polynomials_.at(id);
                for (auto coefficient : p.coefficients(variable)) intern(std::move(coefficient));
                const auto derivative = p.derivative(variable);
                if (!derivative.isZero()) chain(p, derivative, variable);
            }
            for (std::size_t i = 0; i < basis.size(); ++i)
                for (std::size_t j = i + 1; j < basis.size(); ++j) {
                    const auto a = polynomials_.at(basis[i]), b = polynomials_.at(basis[j]);
                    chain(a, b, variable);
                }
        }
    }
    Sign sign(const Poly& polynomial) {
        resources_.tick();
        if (polynomial.isConstant()) {
            const auto s = sgn(polynomial.constantValue());
            return s < 0 ? Sign::Neg : s > 0 ? Sign::Pos : Sign::Zero;
        }
        const auto result = algebra_.signAt(kernelPolynomial(polynomial), sample_);
        if (result == Sign::Unknown) throw Unsupported("exact real sign evaluation did not complete");
        return result;
    }
    std::optional<bool> evaluate(std::size_t id) {
        Resources::Frame frame(resources_);
        const auto& node = problem_.matrix.at(id);
        if (node.kind == Connective::Kind::False) return false;
        if (node.kind == Connective::Kind::True) return true;
        if (node.kind == Connective::Kind::Atom) {
            if (atomLevels_.at(node.atom) >= static_cast<int>(sample_.numVars())) return std::nullopt;
            const auto s = algebra_.signAt(atoms_.at(node.atom), sample_);
            if (s == Sign::Unknown) throw Unsupported("exact real atom evaluation did not complete");
            return relationHolds(s, problem_.atoms.at(node.atom).relation);
        }
        const bool conjunction = node.kind == Connective::Kind::And;
        bool decided = true;
        for (auto child : node.children) {
            const auto result = evaluate(child);
            if (!result) decided = false;
            else if (*result != conjunction) return *result;
        }
        return decided ? std::optional<bool>(conjunction) : std::nullopt;
    }
    int compare(const RealAlg& a, const RealAlg& b) {
        resources_.tick();
        const auto result = algebra_.compareRealAlg(a, b);
        if (result == CompareResult::Unknown) throw Unsupported("exact real root comparison did not complete");
        return static_cast<int>(result);
    }
    std::vector<RealAlg> roots(std::size_t level) {
        std::vector<RealAlg> result;
        const auto variable = order_.at(level);
        const bool rationalPrefix = std::all_of(sample_.values.begin(), sample_.values.end(),
            [](const auto& value) { return value.isRational(); });
        for (auto id : byLevel_.at(level)) {
            resources_.tick();
            const auto& polynomial = polynomials_.at(id);
            bool nullified = true;
            for (const auto& coefficient : polynomial.coefficients(variable))
                if (sign(coefficient) != Sign::Zero) nullified = false;
            // Full Collins coefficient projection makes nullification uniform
            // over the base cell. A zero polynomial has no boundary in its fiber.
            if (nullified) continue;
            RootSet isolated;
            const auto pid = kernelPolynomial(polynomial);
            if (rationalPrefix) {
                const auto univariate = algebra_.specializeToUnivariate(pid, sample_, variable);
                if (univariate == NullUniPolyId) throw Unsupported("real specialization did not complete");
                isolated = algebra_.isolateRealRoots(univariate);
                if (isolated.crashOccurred || !isolated.complete || !algebra_.validateRootIsolation(univariate, isolated))
                    throw Unsupported("real root isolation did not validate");
                // Independently count every distinct real root using a Sturm
                // chain over a Cauchy bound. An ordered list alone does not
                // establish that isolation returned all roots.
                const auto& coefficients = algebra_.getUni(univariate);
                Poly rational;
                mpq_class bound = 2;
                for (std::size_t i = 0; i < coefficients.size(); ++i) {
                    resources_.tick();
                    const auto degree = coefficients.size() - 1 - i;
                    if (degree) rational.addVar(variable, degree, coefficients[i]);
                    else rational.addConstant(coefficients[i]);
                    const mpq_class ratio = abs(mpq_class(coefficients[i]) / mpq_class(coefficients.front()));
                    if (ratio + 2 > bound) bound = ratio + 2;
                }
                rational.normalize();
                const auto count = countRealRootsIn(rational, variable, -bound, bound);
                if (count < 0 || static_cast<std::size_t>(count) != isolated.roots.size())
                    throw Unsupported("real root isolation disagrees with exact Sturm count");
            } else {
                isolated = algebra_.isolateRealRootsAlgebraic(pid, sample_, variable);
                if (isolated.crashOccurred) throw Unsupported("real algebraic isolation did not complete");
                if (!isolated.complete) {
                    bool complete = false;
                    isolated = algebra_.isolateRealRootsViaNorm(pid, sample_, variable, complete);
                    if (!complete) isolated = algebra_.isolateRealRootsViaTower(pid, sample_, variable, complete);
                    if (!complete) throw Unsupported("real algebraic tower isolation did not complete");
                }
            }
            for (auto& root : isolated.roots) result.push_back(std::move(root));
            resources_.nodes(result.size());
        }
        std::sort(result.begin(), result.end(), [&](const auto& a, const auto& b) { return compare(a, b) < 0; });
        result.erase(std::unique(result.begin(), result.end(),
            [&](const auto& a, const auto& b) { return compare(a, b) == 0; }), result.end());
        return result;
    }
    static mpq_class lower(const RealAlg& value) { return value.isRational() ? value.rational : value.root.lower; }
    static mpq_class upper(const RealAlg& value) { return value.isRational() ? value.rational : value.root.upper; }
    mpq_class between(RealAlg& left, RealAlg& right) {
        while (upper(left) >= lower(right)) {
            resources_.tick();
            bool progress = false;
            if (left.isAlgebraic()) progress |= algebra_.refineRootInterval(left.root);
            if (right.isAlgebraic()) progress |= algebra_.refineRootInterval(right.root);
            if (!progress) throw Unsupported("real section intervals could not be separated");
        }
        return (upper(left) + lower(right)) / 2;
    }
    void capture() {
        witness_ = sample_;
        while (witness_.numVars() < problem_.free.size())
            witness_.push(order_.at(witness_.numVars()), RealAlg::fromRational(0));
    }
    bool visit(std::size_t level) {
        Resources::Frame frame(resources_);
        if (const auto value = evaluate(problem_.root)) {
            if (*value && level <= problem_.free.size()) capture();
            return *value;
        }
        if (level == order_.size()) throw std::logic_error("real matrix is not ground at a CAD leaf");
        auto sections = roots(level);
        const bool universal = problem_.prefix.at(level).universal;
        auto child = [&](RealAlg value) {
            sample_.push(order_[level], std::move(value));
            const bool result = visit(level + 1);
            sample_.pop();
            return result;
        };
        auto finish = [&](bool value) {
            if (value && level == problem_.free.size()) capture();
            return value;
        };
        if (sections.empty()) return finish(child(RealAlg::fromRational(0)));
        if (const bool result = child(RealAlg::fromRational(lower(sections.front()) - 1)); result != universal)
            return finish(result);
        for (std::size_t i = 0; i < sections.size(); ++i) {
            if (const bool result = child(sections[i]); result != universal) return finish(result);
            if (i + 1 < sections.size()) {
                if (const bool result = child(RealAlg::fromRational(between(sections[i], sections[i + 1]))); result != universal)
                    return finish(result);
            }
        }
        if (const bool result = child(RealAlg::fromRational(upper(sections.back()) + 1)); result != universal)
            return finish(result);
        return finish(universal);
    }
    RealValue value(const RealAlg& real) {
        if (real.isRational()) return RealValue::fromMpq(real.rational);
        if (real.root.lower == real.root.upper) return RealValue::fromMpq(real.root.lower);
        const auto& coefficients = algebra_.getUni(real.root.definingPoly);
        AlgebraicNumber result;
        result.coefficients.assign(coefficients.rbegin(), coefficients.rend());
        result.lower = real.root.lower;
        result.upper = real.root.upper;
        return RealValue::fromAlgebraic(std::move(result));
    }
public:
    Decomposition(const Problem& p, PolynomialKernel& kernel, Resources& resources)
        : problem_(p), kernel_(kernel), resources_(resources), algebra_(&kernel) {
        for (const auto& binder : p.prefix) {
            levels_.emplace(binder.variable, order_.size());
            order_.push_back(binder.variable);
        }
        byLevel_.resize(order_.size());
        for (const auto& atom : p.atoms) {
            atoms_.push_back(kernelPolynomial(atom.polynomial));
            atomLevels_.push_back(atom.polynomial.highestVariableLevel(order_));
        }
    }
    SolverAnswer run() {
        if (!evaluate(problem_.root)) project();
        const bool satisfiable = visit(0);
        SolverAnswer answer;
        answer.result = satisfiable ? Result::Sat : Result::Unsat;
        if (satisfiable) {
            answer.model.emplace();
            for (std::size_t i = 0; i < problem_.free.size(); ++i) {
                const auto& variable = problem_.free[i];
                const auto v = value(witness_.values.at(i));
                if (variable.boolean) {
                    if (v != RealValue::fromInt(0) && v != RealValue::fromInt(1))
                        throw std::logic_error("CAD Boolean witness is outside its domain");
                    answer.model->assignments.emplace(variable.name, v.isZero() ? "false" : "true");
                } else {
                    answer.model->numericAssignments.emplace(variable.name, v);
                    answer.model->assignments.emplace(variable.name, v.isRational() ? v.asRational().get_str() : v.toSmtLib2());
                }
            }
        }
        return answer;
    }
};
}
SolverAnswer decompose(const Problem& problem, PolynomialKernel& kernel, Resources& resources) {
    return Decomposition(problem, kernel, resources).run();
}
}
