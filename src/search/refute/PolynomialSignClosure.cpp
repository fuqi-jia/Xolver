#include "search/refute/PolynomialSignClosure.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <iterator>
#include <map>
#include <string>
#include <unordered_map>

namespace xolver {
namespace {
constexpr unsigned Neg = 1, Zero = 2, Pos = 4, Any = 7;
using Reasons = std::vector<SatLit>;

unsigned negate(unsigned signs) {
    return (signs & Zero) | ((signs & Neg) ? Pos : 0) | ((signs & Pos) ? Neg : 0);
}
unsigned signsOf(Relation relation) {
    switch (relation) {
        case Relation::Lt: return Neg;
        case Relation::Leq: return Neg | Zero;
        case Relation::Eq: return Zero;
        case Relation::Neq: return Neg | Pos;
        case Relation::Geq: return Zero | Pos;
        case Relation::Gt: return Pos;
    }
    return Any;
}
unsigned combine(unsigned lhs, unsigned rhs, bool product) {
    unsigned result = 0;
    for (unsigned a : {Neg, Zero, Pos}) for (unsigned b : {Neg, Zero, Pos}) {
        if (!(lhs & a) || !(rhs & b)) continue;
        if (product) result |= a == Zero || b == Zero ? Zero : a == b ? Pos : Neg;
        else result |= a == Zero ? b : b == Zero ? a : a == b ? a : Any;
    }
    return result;
}
void include(Reasons& target, const Reasons& source) {
    for (auto literal : source)
        if (std::find(target.begin(), target.end(), literal) == target.end()) target.push_back(literal);
}
struct Conflict { Reasons reasons; };
struct Proof { unsigned signs = Any; Reasons reasons; };
struct Fact { RationalPolynomial poly; unsigned signs; Reasons reasons; };
struct Bound { mpq_class value; bool strict; Reasons reasons; };
struct Range { std::optional<Bound> lower, upper; };
struct Fixed { mpq_class value; Reasons reasons; };
struct Affine { VarId variable; mpq_class coefficient, constant; };

std::optional<Affine> affine(const RationalPolynomial& polynomial) {
    std::optional<Affine> result;
    mpq_class constant = 0;
    for (const auto& [monomial, coefficient] : polynomial.terms()) {
        if (monomial.empty()) { constant = coefficient; continue; }
        if (result || monomial.size() != 1 || monomial[0].second != 1) return std::nullopt;
        result = Affine{monomial[0].first, coefficient, 0};
    }
    if (result) result->constant = constant;
    return result;
}

class SignClosure {
    PolynomialSignStatistics& stats_;
    WorkBudget budget_{100000};
    const std::chrono::steady_clock::time_point deadline_ =
        std::chrono::steady_clock::now() + std::chrono::milliseconds(10);
    std::vector<Fact> facts_;
    std::unordered_map<std::string, size_t> index_;
    std::map<VarId, Range> ranges_;
    std::map<VarId, Fixed> fixed_;
    bool changed_ = false;

    void tick(size_t work = 1) {
        budget_.tick(work);
        if (std::chrono::steady_clock::now() >= deadline_)
            throw ResourceExhausted("polynomial sign closure allocation exhausted");
    }
    void checkSize(const RationalPolynomial& polynomial) {
        if (polynomial.terms().size() > 256) throw ResourceExhausted("sign closure term allocation exhausted");
        for (const auto& [monomial, coefficient] : polynomial.terms()) {
            tick(1 + monomial.size());
            if (mpz_sizeinbase(coefficient.get_num().get_mpz_t(), 2) > 4096 ||
                mpz_sizeinbase(coefficient.get_den().get_mpz_t(), 2) > 4096)
                throw ResourceExhausted("sign closure coefficient allocation exhausted");
            for (const auto& [variable, exponent] : monomial) {
                (void)variable;
                if (exponent > 32) throw ResourceExhausted("sign closure degree allocation exhausted");
            }
        }
    }
    std::string canonical(RationalPolynomial& polynomial, unsigned& signs) {
        polynomial.normalize();
        checkSize(polynomial);
        if (polynomial.isZero()) return {};
        const mpq_class leading = polynomial.terms().begin()->second;
        polynomial *= mpq_class(1) / leading;
        if (leading < 0) signs = negate(signs);
        std::string key;
        for (const auto& [monomial, coefficient] : polynomial.terms()) {
            for (const auto& [variable, exponent] : monomial)
                key += std::to_string(variable) + "^" + std::to_string(exponent) + ",";
            key += ":" + coefficient.get_str() + ";";
        }
        return key;
    }
    bool add(RationalPolynomial polynomial, unsigned signs, Reasons reasons) {
        tick();
        const auto key = canonical(polynomial, signs);
        if (polynomial.isConstant()) {
            const auto value = polynomial.constantValue();
            const unsigned actual = value > 0 ? Pos : value < 0 ? Neg : Zero;
            if (!(actual & signs)) throw Conflict{std::move(reasons)};
            return false;
        }
        const auto it = index_.find(key);
        if (it != index_.end()) {
            auto& old = facts_[it->second];
            const unsigned intersection = old.signs & signs;
            if (intersection == old.signs) return false;
            include(reasons, old.reasons);
            if (!intersection) throw Conflict{std::move(reasons)};
            old.signs = intersection;
            old.reasons = std::move(reasons);
        } else {
            if (signs == Any) return false;
            if (facts_.size() >= 256) throw ResourceExhausted("sign closure fact allocation exhausted");
            index_.emplace(key, facts_.size());
            facts_.push_back({std::move(polynomial), signs, std::move(reasons)});
        }
        changed_ = true;
        ++stats_.inferredFacts;
        return true;
    }
    Proof variableSign(VarId variable) {
        if (const auto it = fixed_.find(variable); it != fixed_.end())
            return {it->second.value > 0 ? Pos : it->second.value < 0 ? Neg : Zero, it->second.reasons};
        auto polynomial = RationalPolynomial::fromVar(variable, 1, 1);
        unsigned signs = Any;
        const auto it = index_.find(canonical(polynomial, signs));
        return it == index_.end() ? Proof{} : Proof{facts_[it->second].signs, facts_[it->second].reasons};
    }
    Proof monomialSign(const MonomialKey& monomial, const mpq_class& coefficient) {
        Proof result{coefficient > 0 ? Pos : coefficient < 0 ? Neg : Zero, {}};
        for (const auto& [variable, exponent] : monomial) {
            tick();
            auto factor = variableSign(variable);
            if (exponent % 2 == 0)
                factor.signs = ((factor.signs & Zero) ? Zero : 0) | ((factor.signs & (Neg | Pos)) ? Pos : 0);
            result.signs = combine(result.signs, factor.signs, true);
            include(result.reasons, factor.reasons);
        }
        return result;
    }
    Proof polynomialSign(const RationalPolynomial& polynomial) {
        Proof result{Zero, {}};
        for (const auto& [monomial, coefficient] : polynomial.terms()) {
            auto term = monomialSign(monomial, coefficient);
            result.signs = combine(result.signs, term.signs, false);
            include(result.reasons, term.reasons);
        }
        auto normalized = polynomial;
        unsigned orientation = Pos;
        const auto it = index_.find(canonical(normalized, orientation));
        if (it != index_.end()) {
            const auto& fact = facts_[it->second];
            const auto known = orientation == Pos ? fact.signs : negate(fact.signs);
            if ((result.signs & known) != result.signs) {
                result.signs &= known;
                include(result.reasons, fact.reasons);
                if (!result.signs) throw Conflict{std::move(result.reasons)};
            }
        }
        return result;
    }
    void bound(VarId variable, bool lower, const mpq_class& value, bool strict, const Reasons& reasons) {
        auto& range = ranges_[variable];
        auto& previous = lower ? range.lower : range.upper;
        if (!previous || (lower ? value > previous->value : value < previous->value) ||
            (value == previous->value && strict && !previous->strict))
            previous = Bound{value, strict, reasons};
        if (range.lower && range.upper) {
            Reasons support = range.lower->reasons;
            include(support, range.upper->reasons);
            if (range.lower->value > range.upper->value ||
                (range.lower->value == range.upper->value && (range.lower->strict || range.upper->strict)))
                throw Conflict{std::move(support)};
            if (range.lower->value == range.upper->value && !fixed_.contains(variable)) {
                fixed_.emplace(variable, Fixed{value, std::move(support)});
                changed_ = true;
            }
        }
        const auto polynomial = RationalPolynomial::fromVar(variable, 1, 1);
        if (lower && value >= 0) add(polynomial, value > 0 || strict ? Pos : Pos | Zero, reasons);
        if (!lower && value <= 0) add(polynomial, value < 0 || strict ? Neg : Neg | Zero, reasons);
    }
    void linearBounds(const Fact& fact) {
        const auto form = affine(fact.poly);
        if (!form) return;
        const mpq_class value = -form->constant / form->coefficient;
        if (!(fact.signs & Neg)) bound(form->variable, form->coefficient > 0, value, !(fact.signs & Zero), fact.reasons);
        if (!(fact.signs & Pos)) bound(form->variable, form->coefficient < 0, value, !(fact.signs & Zero), fact.reasons);
    }
    void necessarySupport(const Fact& fact, const std::vector<Proof>& terms, const Reasons& support) {
        const bool positive = fact.signs == Pos ||
            (!(fact.signs & Neg) && std::any_of(terms.begin(), terms.end(), [](const auto& p) { return p.signs == Neg; }));
        const bool negative = fact.signs == Neg ||
            (!(fact.signs & Pos) && std::any_of(terms.begin(), terms.end(), [](const auto& p) { return p.signs == Pos; }));
        for (const auto direction : {Pos, Neg}) {
            if (!(direction == Pos ? positive : negative)) continue;
            std::vector<VarId> common;
            bool first = true;
            size_t index = 0;
            for (const auto& [monomial, coefficient] : fact.poly.terms()) {
                (void)coefficient;
                if (!(terms[index++].signs & direction)) continue;
                std::vector<VarId> variables;
                for (const auto& [variable, exponent] : monomial) { (void)exponent; variables.push_back(variable); }
                if (first) { common = std::move(variables); first = false; }
                else {
                    std::vector<VarId> intersection;
                    std::set_intersection(common.begin(), common.end(), variables.begin(), variables.end(), std::back_inserter(intersection));
                    common = std::move(intersection);
                }
            }
            if (!first) for (auto variable : common)
                add(RationalPolynomial::fromVar(variable, 1, 1), Neg | Pos, support);
        }
    }
    void cancel(const Fact& fact) {
        std::map<VarId, int> common;
        bool first = true;
        for (const auto& [monomial, coefficient] : fact.poly.terms()) {
            (void)coefficient;
            std::map<VarId, int> powers(monomial.begin(), monomial.end());
            if (first) { common = std::move(powers); first = false; }
            else for (auto it = common.begin(); it != common.end();) {
                const auto found = powers.find(it->first);
                if (found == powers.end()) it = common.erase(it);
                else { it->second = std::min(it->second, found->second); ++it; }
            }
        }
        if (!(fact.signs & Zero)) for (const auto& [variable, exponent] : common) {
            (void)exponent;
            add(RationalPolynomial::fromVar(variable, 1, 1), Neg | Pos, fact.reasons);
        }
        unsigned divisorSign = Pos;
        Reasons support = fact.reasons;
        for (auto it = common.begin(); it != common.end();) {
            auto proof = variableSign(it->first);
            if (proof.signs & Zero) { it = common.erase(it); continue; }
            include(support, proof.reasons);
            divisorSign = combine(divisorSign, it->second % 2 ? proof.signs : Pos, true);
            ++it;
        }
        if (common.empty()) {
            if (fact.signs == Zero && fact.poly.terms().size() == 1) {
                const auto& monomial = fact.poly.terms().begin()->first;
                if (monomial.size() == 1)
                    add(RationalPolynomial::fromVar(monomial[0].first, 1, 1), Zero, fact.reasons);
            }
            return;
        }
        RationalPolynomial quotient;
        for (const auto& [monomial, coefficient] : fact.poly.terms()) {
            MonomialKey reduced;
            for (const auto& [variable, exponent] : monomial) {
                const auto it = common.find(variable);
                const auto power = exponent - (it == common.end() ? 0 : it->second);
                if (power) reduced.emplace_back(variable, power);
            }
            quotient.addTerm(reduced, coefficient);
        }
        if (add(std::move(quotient), combine(fact.signs, divisorSign, true), std::move(support))) ++stats_.cancellations;
    }
    std::optional<std::pair<RationalPolynomial, RationalPolynomial>> divide(
        const RationalPolynomial& polynomial, const RationalPolynomial& divisor, const Affine& form) {
        int degree = polynomial.degree(form.variable);
        if (degree < 1 || degree > 32) return std::nullopt;
        ++stats_.divisions;
        RationalPolynomial quotient, remainder = polynomial;
        while (degree >= 1) {
            tick(remainder.terms().size() + 1);
            auto term = remainder.leadingCoefficient(form.variable);
            term *= mpq_class(1) / form.coefficient;
            if (degree > 1) term = term * RationalPolynomial::fromVar(form.variable, degree - 1, 1);
            checkSize(term);
            quotient += term;
            remainder -= divisor * term;
            checkSize(remainder);
            const int next = remainder.degree(form.variable);
            if (next >= degree) return std::nullopt;
            degree = next;
        }
        return std::make_pair(std::move(quotient), std::move(remainder));
    }
    void affineDecompositions(const Fact& fact, size_t limit) {
        for (size_t i = 0; i < limit; ++i) {
            tick();
            const Fact divisor = facts_[i];
            const auto form = affine(divisor.poly);
            if (!form || form->constant == 0) continue;
            auto division = divide(fact.poly, divisor.poly, *form);
            if (!division || (division->first.isConstant() && division->second.isZero())) continue;
            auto quotient = polynomialSign(division->first);
            auto remainder = polynomialSign(division->second);
            const auto product = combine(divisor.signs, quotient.signs, true);
            const auto sum = combine(product, remainder.signs, false);
            Reasons support = divisor.reasons;
            include(support, quotient.reasons);
            include(support, remainder.reasons);
            add(fact.poly, sum, support);
            const bool zeroSum = (!(fact.signs & Neg) && !(product & Pos) && !(remainder.signs & Pos)) ||
                                 (!(fact.signs & Pos) && !(product & Neg) && !(remainder.signs & Neg));
            if (zeroSum) {
                include(support, fact.reasons);
                add(fact.poly - division->second, Zero, support);
                add(std::move(division->second), Zero, std::move(support));
            }
        }
    }
    void analyze(Fact fact, size_t limit) {
        bool substituted = false;
        for (const auto& [variable, fixed] : fixed_) if (fact.poly.contains(variable)) {
            tick(fact.poly.terms().size() + 1);
            fact.poly = fact.poly.substituteRational(variable, fixed.value);
            include(fact.reasons, fixed.reasons);
            substituted = true;
        }
        if (substituted) {
            if (add(std::move(fact.poly), fact.signs, std::move(fact.reasons))) ++stats_.substitutions;
            return;
        }
        linearBounds(fact);
        Proof sum{Zero, {}};
        std::vector<Proof> terms;
        for (const auto& [monomial, coefficient] : fact.poly.terms()) {
            terms.push_back(monomialSign(monomial, coefficient));
            sum.signs = combine(sum.signs, terms.back().signs, false);
            include(sum.reasons, terms.back().reasons);
        }
        add(fact.poly, sum.signs, sum.reasons);
        Reasons support = fact.reasons;
        include(support, sum.reasons);
        necessarySupport(fact, terms, support);
        const bool zeroSum = (!(fact.signs & Neg) && !(sum.signs & Pos)) ||
                             (!(fact.signs & Pos) && !(sum.signs & Neg));
        if (zeroSum) for (const auto& [monomial, coefficient] : fact.poly.terms()) {
            RationalPolynomial term;
            term.addTerm(monomial, coefficient);
            add(std::move(term), Zero, support);
        }
        cancel(fact);
        affineDecompositions(fact, limit);
    }
public:
    explicit SignClosure(PolynomialSignStatistics& statistics) : stats_(statistics) { facts_.reserve(256); }
    void run(const std::vector<SignRefuteConstraint>& constraints) {
        if (constraints.size() > 128) throw ResourceExhausted("sign closure input allocation exhausted");
        for (const auto& constraint : constraints) add(constraint.poly, signsOf(constraint.rel), {constraint.reason});
        stats_.inferredFacts = 0;
        for (size_t round = 0; round < 32; ++round) {
            ++stats_.rounds;
            changed_ = false;
            const size_t limit = facts_.size();
            for (size_t i = 0; i < limit; ++i) { tick(); analyze(facts_[i], limit); }
            if (!changed_) return;
        }
        throw ResourceExhausted("sign closure round allocation exhausted");
    }
};
} // namespace

std::optional<std::vector<SatLit>> refuteByPolynomialSignClosure(
    const std::vector<SignRefuteConstraint>& constraints, PolynomialSignStatistics* statistics) {
    PolynomialSignStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try { SignClosure(stats).run(constraints); }
    catch (Conflict& conflict) { return std::move(conflict.reasons); }
    catch (const ResourceExhausted&) { stats.exhausted = true; }
    return std::nullopt;
}
} // namespace xolver
