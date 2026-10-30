#include "search/refute/PolynomialSignClosure.h"
#include "base/WorkBudget.h"
#include <algorithm>
#include <chrono>
#include <iterator>
#include <map>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>

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
struct DivisionPivot { VarId variable; mpq_class coefficient; };
struct Projection { RationalPolynomial poly; Reasons reasons; };

size_t totalDegree(const RationalPolynomial& polynomial) {
    size_t result = 0;
    for (const auto& [monomial, coefficient] : polynomial.terms()) {
        (void)coefficient;
        size_t degree = 0;
        for (const auto& power : monomial) degree += power.second;
        result = std::max(result, degree);
    }
    return result;
}

void reduceZeroPowers(RationalPolynomial& polynomial) {
    // x^k*q=0 iff x*q=0 for k>=1, including x=0. Remove repeated
    // monomial content before indexing equations or scheduling eliminants.
    std::map<VarId, int> common;
    bool first = true;
    for (const auto& [monomial, coefficient] : polynomial.terms()) {
        (void)coefficient;
        if (first) { common.insert(monomial.begin(), monomial.end()); first = false; }
        else for (auto it = common.begin(); it != common.end();) {
            const auto power = std::find_if(monomial.begin(), monomial.end(), [&](const auto& value) {
                return value.first == it->first;
            });
            if (power == monomial.end()) it = common.erase(it);
            else { it->second = std::min(it->second, power->second); ++it; }
        }
        if (common.empty()) return;
    }
    for (auto it = common.begin(); it != common.end();)
        if (it->second <= 1) it = common.erase(it);
        else { --it->second; ++it; }
    if (common.empty()) return;
    RationalPolynomial reduced;
    for (const auto& [monomial, coefficient] : polynomial.terms()) {
        auto powers = monomial;
        for (auto& [variable, exponent] : powers) {
            const auto it = common.find(variable);
            if (it != common.end()) exponent -= it->second;
        }
        reduced.addTerm(powers, coefficient);
    }
    polynomial = std::move(reduced);
}

std::optional<VarId> zeroPowerVariable(const RationalPolynomial& polynomial) {
    if (polynomial.terms().size() != 1 || polynomial.terms().begin()->second == 0) return std::nullopt;
    const auto& monomial = polynomial.terms().begin()->first;
    return monomial.size() == 1 && monomial[0].second > 0 ? std::optional<VarId>(monomial[0].first) : std::nullopt;
}

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
    std::unordered_map<VarId, size_t> variableIndex_;
    std::unordered_set<size_t> substitutedFacts_;
    std::map<VarId, Range> ranges_;
    std::map<VarId, Fixed> fixed_;
    std::set<std::tuple<size_t, size_t, VarId>> eliminated_;
    std::unordered_set<std::string> projected_;
    std::multimap<std::tuple<size_t, size_t, size_t>, Projection> projections_;
    std::unordered_map<size_t, std::vector<DivisionPivot>> divisionPivots_;
    std::vector<size_t> divisionOrder_;
    size_t nextDecomposition_ = 0;
    bool preferProjection_ = true;
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
        if (signs == Zero) reduceZeroPowers(polynomial);
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
            substitutedFacts_.erase(it->second);
        } else {
            if (!signs) throw Conflict{std::move(reasons)};
            if (signs == Any) return false;
            if (facts_.size() >= 256) throw ResourceExhausted("sign closure fact allocation exhausted");
            index_.emplace(key, facts_.size());
            if (polynomial.terms().size() == 1) {
                const auto& [monomial, coefficient] = *polynomial.terms().begin();
                if (coefficient == 1 && monomial.size() == 1 && monomial[0].second == 1) {
                    variableIndex_.emplace(monomial[0].first, facts_.size());
                    ++stats_.indexedVariables;
                }
            }
            facts_.push_back({std::move(polynomial), signs, std::move(reasons)});
        }
        changed_ = true;
        ++stats_.inferredFacts;
        return true;
    }
    Proof variableSign(VarId variable) {
        ++stats_.variableLookups;
        if (const auto it = fixed_.find(variable); it != fixed_.end())
            return {it->second.value > 0 ? Pos : it->second.value < 0 ? Neg : Zero, it->second.reasons};
        const auto it = variableIndex_.find(variable);
        if (it == variableIndex_.end()) return {};
        ++stats_.variableIndexHits;
        // Retain the fact's stable index, not a copied sign or explanation:
        // later intersections must be visible to every monomial in this call.
        return {facts_[it->second].signs, facts_[it->second].reasons};
    }
    Proof monomialSign(const MonomialKey& monomial, const mpq_class& coefficient,
                       std::optional<std::pair<VarId, unsigned>> assumption = std::nullopt) {
        Proof result{coefficient > 0 ? Pos : coefficient < 0 ? Neg : Zero, {}};
        for (const auto& [variable, exponent] : monomial) {
            tick();
            auto factor = assumption && assumption->first == variable
                ? Proof{assumption->second, {}} : variableSign(variable);
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
            if (fact.signs == Zero) if (const auto variable = zeroPowerVariable(fact.poly))
                add(RationalPolynomial::fromVar(*variable, 1, 1), Zero, fact.reasons);
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
        const RationalPolynomial& polynomial, const RationalPolynomial& divisor, const DivisionPivot& form) {
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
    std::vector<DivisionPivot> divisionPivots(const RationalPolynomial& polynomial) {
        std::vector<DivisionPivot> result;
        for (auto variable : polynomial.variables()) {
            tick(polynomial.terms().size() + 1);
            if (polynomial.degree(variable) != 1) continue;
            const auto leading = polynomial.leadingCoefficient(variable);
            if (leading.isConstant() && leading.constantValue() != 0)
                result.push_back({variable, leading.constantValue()});
        }
        return result;
    }
    void affineDecompositions(const Fact& fact, size_t limit) {
        if (divisionOrder_.size() != limit) {
            divisionOrder_.clear();
            for (size_t i = 0; i < limit; ++i) divisionOrder_.push_back(i);
            // Scalar variable bounds expose product factors directly. Prefer
            // these and short affine forms to more expensive substitutions.
            std::stable_sort(divisionOrder_.begin(), divisionOrder_.end(), [&](size_t a, size_t b) {
                return facts_[a].poly.terms().size() < facts_[b].poly.terms().size();
            });
        }
        for (size_t i : divisionOrder_) {
            tick();
            const Fact divisor = facts_[i];
            if (std::any_of(fixed_.begin(), fixed_.end(), [&](const auto& value) {
                    return divisor.poly.contains(value.first);
                })) continue;
            auto pivot = divisionPivots_.find(i);
            if (pivot == divisionPivots_.end())
                pivot = divisionPivots_.emplace(i, divisionPivots(divisor.poly)).first;
            for (const auto& form : pivot->second) {
                auto division = divide(fact.poly, divisor.poly, form);
                if (!division || (division->first.isConstant() && division->second.isZero())) continue;
                if (divisor.signs == Zero) {
                    Reasons support = fact.reasons;
                    include(support, divisor.reasons);
                    add(division->second, fact.signs, std::move(support));
                    if (changed_) return;
                }
                auto quotient = divisor.signs == Zero ? Proof{} : polynomialSign(division->first);
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
                    add(division->second, Zero, support);
                }
                if (changed_) return;
                // p=d*q+r also entails r=p-d*q and d*q=p-r. Backward
                // sign propagation keeps zero factors: no inequality is divided
                // by d unless every feasible sign case justifies the consequence.
                include(support, fact.reasons);
                add(division->second, combine(fact.signs, negate(product), false), support);
                if (changed_) return;
                const auto requiredProduct = combine(fact.signs, negate(remainder.signs), false);
                unsigned quotientSigns = 0, divisorSigns = 0;
                for (auto sign : {Neg, Zero, Pos}) {
                    if (combine(divisor.signs, sign, true) & requiredProduct) quotientSigns |= sign;
                    if (combine(sign, quotient.signs, true) & requiredProduct) divisorSigns |= sign;
                }
                add(division->first, quotientSigns, support);
                if (changed_) return;
                add(divisor.poly, divisorSigns, std::move(support));
                if (changed_) return;
            }
        }
    }
    Proof factoredSign(const RationalPolynomial& polynomial, unsigned depth) {
        auto result = polynomialSign(polynomial);
        const auto variables = polynomial.variables();
        if (!depth || variables.size() < 2 || result.signs == Neg || result.signs == Pos) return result;
        for (size_t i = 0; i < facts_.size(); ++i) {
            tick();
            const auto& divisor = facts_[i];
            if (totalDegree(divisor.poly) != 1) continue;
            const auto factors = divisor.poly.variables();
            if (!std::includes(variables.begin(), variables.end(), factors.begin(), factors.end())) continue;
            auto pivots = divisionPivots_.find(i);
            if (pivots == divisionPivots_.end())
                pivots = divisionPivots_.emplace(i, divisionPivots(divisor.poly)).first;
            for (const auto& pivot : pivots->second) {
                auto division = divide(polynomial, divisor.poly, pivot);
                if (!division || (division->first.isConstant() && division->second.isZero())) continue;
                auto quotient = polynomialSign(division->first);
                const auto product = combine(divisor.signs, quotient.signs, true);
                if (product == Any) continue;
                auto remainder = factoredSign(division->second, depth - 1);
                const auto possible = combine(product, remainder.signs, false);
                if ((result.signs & possible) == result.signs) continue;
                result.signs &= possible;
                include(result.reasons, divisor.reasons);
                include(result.reasons, quotient.reasons);
                include(result.reasons, remainder.reasons);
                if (!result.signs) throw Conflict{std::move(result.reasons)};
                if (result.signs == Neg || result.signs == Pos) return result;
            }
        }
        return result;
    }
    void refutePendingProjections() {
        // Prove a pending equation impossible directly instead of first
        // materializing all lower-support consequences. Each recursive affine
        // decomposition removes a variable and keeps original SAT premises.
        for (const auto& [rank, projection] : projections_) {
            (void)rank;
            const auto proof = factoredSign(projection.poly, 2);
            if (proof.signs & Zero) continue;
            Reasons reasons = projection.reasons;
            include(reasons, proof.reasons);
            throw Conflict{std::move(reasons)};
        }
    }
    void enqueueProjection(RationalPolynomial polynomial, Reasons reasons) {
        // Over the reals, c*x^k=0 with nonzero c and k>0 is exactly x=0.
        if (const auto variable = zeroPowerVariable(polynomial))
            polynomial = RationalPolynomial::fromVar(*variable, 1, 1);
        unsigned signs = Zero;
        const auto key = canonical(polynomial, signs);
        if (polynomial.isConstant()) { add(std::move(polynomial), Zero, std::move(reasons)); return; }
        const auto found = index_.find(key);
        if (found != index_.end() && facts_[found->second].signs == Zero) return;
        if (!projected_.insert(key).second) return;
        if (projections_.size() >= 256) throw ResourceExhausted("sign projection allocation exhausted");
        const auto rank = std::make_tuple(totalDegree(polynomial), polynomial.variables().size(), polynomial.terms().size());
        projections_.emplace(rank, Projection{std::move(polynomial), std::move(reasons)});
    }
    void applyProjection() {
        while (!projections_.empty()) {
            tick();
            auto first = projections_.begin();
            auto projection = std::move(first->second);
            projections_.erase(first);
            if (add(std::move(projection.poly), Zero, std::move(projection.reasons))) {
                ++stats_.eliminations;
                return;
            }
        }
    }
    bool cancelledEquality(const Fact& fact) {
        if (fact.signs != Zero) return false;
        // The cheap queue has already installed the quotient of an equality
        // with an explained nonzero common factor. Eliminating its redundant
        // multiple again just manufactures higher-degree copies of the same
        // equation, which can starve independent consequences.
        for (auto variable : fact.poly.variables()) {
            if (variableSign(variable).signs & Zero) continue;
            if (std::all_of(fact.poly.terms().begin(), fact.poly.terms().end(), [&](const auto& term) {
                    return std::any_of(term.first.begin(), term.first.end(), [&](const auto& power) {
                        return power.first == variable;
                    });
                })) return true;
        }
        return false;
    }
    void collectProjections(const Fact& fact, size_t position, const std::vector<bool>& eligible) {
        if (!eligible[position]) return;
        const auto variables = fact.poly.variables();
        for (size_t other = 0; other < eligible.size(); ++other) {
            tick();
            if (other == position || !eligible[other]) continue;
            const Fact partner = facts_[other];
            const auto partnerVariables = partner.poly.variables();
            for (auto variable : variables) {
                tick();
                if (fact.poly.degree(variable) != 1 || partner.poly.degree(variable) != 1) continue;
                if (!eliminated_.emplace(std::min(position, other), std::max(position, other), variable).second)
                    continue;
                const auto a = fact.poly.leadingCoefficient(variable);
                const auto b = fact.poly.substituteRational(variable, mpq_class(0));
                const auto c = partner.poly.leadingCoefficient(variable);
                const auto d = partner.poly.substituteRational(variable, mpq_class(0));
                const size_t terms = a.terms().size() * d.terms().size() +
                                     c.terms().size() * b.terms().size();
                if (terms > 256) continue;
                tick(1 + terms);
                // From a*x+b=0 and c*x+d=0, cross multiplication gives
                // a*d-c*b=0, including a=0 or c=0. No division is used.
                auto resultant = a * d - c * b;
                // Prefer smaller supports; also retain degree-preserving
                // eliminants that remove a variable from the joint inputs.
                const auto supportSize = resultant.variables().size();
                if (supportSize >= std::max(variables.size(), partnerVariables.size())) {
                    std::vector<VarId> joint;
                    std::set_union(variables.begin(), variables.end(), partnerVariables.begin(), partnerVariables.end(),
                                   std::back_inserter(joint));
                    // A bilinear eliminant can retain either input's support
                    // while removing their shared variable. Keep that genuine
                    // reduction when it does not increase polynomial degree.
                    if (supportSize >= joint.size() ||
                        totalDegree(resultant) > std::max(totalDegree(fact.poly), totalDegree(partner.poly))) continue;
                }
                Reasons support = fact.reasons;
                include(support, partner.reasons);
                enqueueProjection(std::move(resultant), std::move(support));
            }
        }
    }
    void analyze(Fact fact, size_t position) {
        bool substituted = false;
        for (const auto& [variable, fixed] : fixed_) if (fact.poly.contains(variable)) {
            tick(fact.poly.terms().size() + 1);
            fact.poly = fact.poly.substituteRational(variable, fixed.value);
            include(fact.reasons, fixed.reasons);
            substituted = true;
        }
        if (substituted) {
            if (add(std::move(fact.poly), fact.signs, std::move(fact.reasons))) ++stats_.substitutions;
            // The explained rewritten fact receives all later sign analysis
            // and substitutions. Revisit this source only if its relation is
            // strengthened; add() invalidates this local mark in that case.
            substitutedFacts_.insert(position);
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
    }
    void refineVariableSigns(const Fact& fact) {
        for (auto variable : fact.poly.variables()) {
            tick();
            const auto known = variableSign(variable);
            if (known.signs == Neg || known.signs == Zero || known.signs == Pos) continue;
            unsigned remaining = known.signs;
            Reasons support = fact.reasons;
            include(support, known.reasons);
            for (auto candidate : {Neg, Zero, Pos}) {
                if (!(known.signs & candidate)) continue;
                Proof sum{Zero, {}};
                for (const auto& [monomial, coefficient] : fact.poly.terms()) {
                    auto term = monomialSign(monomial, coefficient, std::make_pair(variable, candidate));
                    sum.signs = combine(sum.signs, term.signs, false);
                    include(sum.reasons, term.reasons);
                }
                if (!(sum.signs & fact.signs)) {
                    remaining &= ~candidate;
                    include(support, sum.reasons);
                }
            }
            if (remaining != known.signs) {
                // The trial sign is discharged: every point with that sign
                // violates this original consequence under the other bounds.
                // No hypothetical premise enters the returned explanation.
                add(RationalPolynomial::fromVar(variable, 1, 1), remaining, std::move(support));
                return;
            }
        }
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
            for (size_t i = 0; i < limit; ++i) {
                tick();
                if (!substitutedFacts_.contains(i)) analyze(facts_[i], i);
            }
            if (changed_) continue;
            for (size_t i = 0; i < limit; ++i) {
                const Fact fact = facts_[i];
                if (std::any_of(fixed_.begin(), fixed_.end(), [&](const auto& value) {
                        return fact.poly.contains(value.first);
                    })) continue;
                refineVariableSigns(fact);
                if (changed_) break;
            }
            if (changed_) continue;
            // First saturate signs, exact bounds and fixed substitutions. One
            // new algebraic fact then returns to that cheap propagation queue.
            refutePendingProjections();
            std::vector<bool> eligible(limit, false);
            for (size_t i = 0; i < limit; ++i)
                eligible[i] = facts_[i].signs == Zero && !substitutedFacts_.contains(i) && !cancelledEquality(facts_[i]);
            for (size_t i = 0; i < limit; ++i) { tick(); collectProjections(facts_[i], i, eligible); }
            if (preferProjection_ || (!projections_.empty() && std::get<0>(projections_.begin()->first) <= 1)) {
                applyProjection();
                if (changed_) { preferProjection_ = false; continue; }
            }
            for (size_t offset = 0; offset < limit; ++offset) {
                tick();
                const size_t i = (nextDecomposition_ + offset) % limit;
                const Fact fact = facts_[i];
                if (std::any_of(fixed_.begin(), fixed_.end(), [&](const auto& value) {
                        return fact.poly.contains(value.first);
                    })) continue;
                affineDecompositions(fact, limit);
                if (changed_) { nextDecomposition_ = (i + 1) % limit; break; }
            }
            if (changed_) { preferProjection_ = true; continue; }
            applyProjection();
            if (changed_) preferProjection_ = false;
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
