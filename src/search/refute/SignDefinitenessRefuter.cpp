#include "search/refute/SignDefinitenessRefuter.h"

#include "base/WorkBudget.h"
#include <chrono>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>

namespace xolver {

namespace {

enum class VarSign { Unknown, PosStrict, NonNeg, NegStrict, NonPos };

struct VarSignInfo {
    VarSign sign = VarSign::Unknown;
    SatLit reason;
};

int strength(VarSign s) {
    switch (s) {
        case VarSign::PosStrict:
        case VarSign::NegStrict: return 2;
        case VarSign::NonNeg:
        case VarSign::NonPos:    return 1;
        default:                 return 0;
    }
}

// If p is univariate-linear (c*v + d, c != 0), return (v, c, d); else nullopt.
struct LinBound { VarId v; mpq_class c; mpq_class d; };
std::optional<LinBound> asLinearBound(const RationalPolynomial& p) {
    auto vars = p.variables();
    if (vars.size() != 1) return std::nullopt;
    const VarId v = *vars.begin();
    if (p.degree(v) != 1) return std::nullopt;
    mpq_class c = 0, d = 0;
    for (const auto& [mon, coeff] : p.terms()) {
        if (mon.empty()) d = coeff;
        else if (mon.size() == 1 && mon[0].first == v && mon[0].second == 1) c = coeff;
        else return std::nullopt;
    }
    if (c == 0) return std::nullopt;
    return LinBound{v, std::move(c), std::move(d)};
}

// Sign forced on v by  c*v + d  rel  0.
VarSign signFromBound(const LinBound& b, Relation rel) {
    const mpq_class B = -b.d / b.c;          // v  R  B
    Relation R = rel;
    if (b.c < 0) {
        switch (rel) {
            case Relation::Lt:  R = Relation::Gt;  break;
            case Relation::Leq: R = Relation::Geq; break;
            case Relation::Gt:  R = Relation::Lt;  break;
            case Relation::Geq: R = Relation::Leq; break;
            default: break;
        }
    }
    const int sB = sgn(B);
    switch (R) {
        case Relation::Gt:
            if (sB >= 0) return VarSign::PosStrict;   // v > B >= 0  =>  v > 0
            break;
        case Relation::Geq:
            if (sB > 0)  return VarSign::PosStrict;   // v >= B > 0  =>  v > 0
            if (sB == 0) return VarSign::NonNeg;      // v >= 0
            break;
        case Relation::Lt:
            if (sB <= 0) return VarSign::NegStrict;
            break;
        case Relation::Leq:
            if (sB < 0)  return VarSign::NegStrict;
            if (sB == 0) return VarSign::NonPos;
            break;
        default: break;   // Eq/Neq: no sign derived
    }
    return VarSign::Unknown;
}

using VarSigns = std::unordered_map<VarId, VarSignInfo>;

VarSigns collectVariableSigns(const std::vector<SignRefuteConstraint>& constraints) {
    std::unordered_map<VarId, VarSignInfo> varSign;
    for (const auto& c : constraints) {
        auto lb = asLinearBound(c.poly);
        if (!lb) continue;
        VarSign s = signFromBound(*lb, c.rel);
        if (s == VarSign::Unknown) continue;
        auto& slot = varSign[lb->v];
        if (strength(s) > strength(slot.sign)) { slot.sign = s; slot.reason = c.reason; }
    }
    return varSign;
}

} // namespace

std::optional<std::vector<SatLit>>
refuteBySignDefiniteness(const std::vector<SignRefuteConstraint>& constraints) {
    const auto varSign = collectVariableSigns(constraints);
    if (varSign.empty()) return std::nullopt;

    // 2. For each constraint, test sign-definiteness of its polynomial.
    for (const auto& c : constraints) {
        if (c.poly.isZero() || c.poly.isConstant()) continue;

        bool allNonNeg = true, allNonPos = true;
        bool strictPos = false, strictNeg = false;
        bool indeterminate = false;

        for (const auto& [mon, coeff] : c.poly.terms()) {
            if (coeff == 0) continue;
            bool positive = (sgn(coeff) > 0);
            bool strict = true;
            for (const auto& [v, e] : mon) {
                auto it = varSign.find(v);
                const VarSign vs = (it == varSign.end()) ? VarSign::Unknown : it->second.sign;
                if (vs == VarSign::Unknown) { indeterminate = true; break; }
                if (vs == VarSign::NonNeg) { strict = false; }
                else if (vs == VarSign::NegStrict) { if (e % 2 == 1) positive = !positive; }
                else if (vs == VarSign::NonPos) { strict = false; if (e % 2 == 1) positive = !positive; }
                // PosStrict: factor > 0, no flip, stays strict.
            }
            if (indeterminate) break;
            if (positive) { allNonPos = false; if (strict) strictPos = true; }
            else          { allNonNeg = false; if (strict) strictNeg = true; }
        }
        if (indeterminate) continue;

        // 3. Decide whether the definite sign contradicts the relation.
        bool refuted = false;
        if (allNonNeg && !allNonPos) {            // g >= 0
            if (strictPos) refuted = (c.rel == Relation::Eq || c.rel == Relation::Leq || c.rel == Relation::Lt);
            else           refuted = (c.rel == Relation::Lt);
        } else if (allNonPos && !allNonNeg) {     // g <= 0
            if (strictNeg) refuted = (c.rel == Relation::Eq || c.rel == Relation::Geq || c.rel == Relation::Gt);
            else           refuted = (c.rel == Relation::Gt);
        }
        if (!refuted) continue;

        // 4. Conflict = g's reason + the bound reasons of g's sign-fixed vars.
        std::vector<SatLit> clause;
        std::unordered_set<SatVar> seen;
        auto addLit = [&](SatLit l) { if (seen.insert(l.var).second) clause.push_back(l); };
        addLit(c.reason);
        for (VarId v : c.poly.variables()) {
            auto it = varSign.find(v);
            if (it != varSign.end()) addLit(it->second.reason);
        }
        return clause;
    }
    return std::nullopt;
}

namespace {
constexpr unsigned Negative = 1, Zero = 2, Positive = 4, UnknownSign = 7;

unsigned relationSigns(Relation relation) {
    switch (relation) {
        case Relation::Eq: return Zero;
        case Relation::Neq: return Negative | Positive;
        case Relation::Lt: return Negative;
        case Relation::Leq: return Negative | Zero;
        case Relation::Gt: return Positive;
        case Relation::Geq: return Positive | Zero;
    }
    return UnknownSign;
}

unsigned combineSigns(unsigned lhs, unsigned rhs, bool multiply) {
    unsigned result = 0;
    for (unsigned a : {Negative, Zero, Positive}) {
        if (!(lhs & a)) continue;
        for (unsigned b : {Negative, Zero, Positive}) {
            if (!(rhs & b)) continue;
            if (multiply) result |= a == Zero || b == Zero ? Zero : a == b ? Positive : Negative;
            else result |= a == Zero ? b : b == Zero ? a : a == b ? a : UnknownSign;
        }
    }
    return result;
}

void includeReasons(std::vector<SatLit>& target, const std::vector<SatLit>& source) {
    for (const auto lit : source)
        if (std::none_of(target.begin(), target.end(), [&](SatLit old) {
                return old.var == lit.var && old.sign == lit.sign;
            })) target.push_back(lit);
}

struct SignProof {
    unsigned signs = UnknownSign;
    std::vector<SatLit> reasons;
};

class QuadraticSignContext {
    const std::vector<SignRefuteConstraint>& constraints_;
    VarSigns variables_;
    WorkBudget budget_{200000};
    std::chrono::steady_clock::time_point deadline_ =
        std::chrono::steady_clock::now() + std::chrono::milliseconds(20);
    QuadraticSignStatistics& stats_;

    void tick(size_t amount = 1) {
        budget_.tick(amount);
        if (std::chrono::steady_clock::now() >= deadline_)
            throw ResourceExhausted("quadratic sign allocation exhausted");
    }
    static bool nonnegative(unsigned signs) { return (signs & Negative) == 0; }

    RationalPolynomial multiply(const RationalPolynomial& a, const RationalPolynomial& b) {
        const auto na = a.terms().size(), nb = b.terms().size();
        if (na && nb > 4096 / na)
            throw ResourceExhausted("quadratic sign product allocation exhausted");
        tick(na * nb + 1);
        return a * b;
    }

    SignProof monomialSum(const RationalPolynomial& polynomial) {
        SignProof result{Zero, {}};
        for (const auto& [monomial, coefficient] : polynomial.terms()) {
            tick(1 + mpz_sizeinbase(coefficient.get_num().get_mpz_t(), 2) / 64 +
                     mpz_sizeinbase(coefficient.get_den().get_mpz_t(), 2) / 64);
            if (coefficient == 0) continue;
            unsigned term = coefficient > 0 ? Positive : Negative;
            for (const auto& [var, exponent] : monomial) {
                tick();
                const auto it = variables_.find(var);
                const auto sign = it == variables_.end() ? VarSign::Unknown : it->second.sign;
                unsigned factor = UnknownSign;
                bool needsBound = false;
                if (exponent % 2 == 0) {
                    // An even power is nonnegative with no sign premise.
                    // A strict sign premise is needed only to exclude zero.
                    const bool strict = sign == VarSign::PosStrict || sign == VarSign::NegStrict;
                    factor = strict ? Positive : Positive | Zero;
                    needsBound = strict;
                } else {
                    switch (sign) {
                        case VarSign::PosStrict: factor = Positive; break;
                        case VarSign::NonNeg: factor = Positive | Zero; break;
                        case VarSign::NegStrict: factor = Negative; break;
                        case VarSign::NonPos: factor = Negative | Zero; break;
                        default: break;
                    }
                    needsBound = sign != VarSign::Unknown;
                }
                if (needsBound) includeReasons(result.reasons, {it->second.reason});
                term = combineSigns(term, factor, true);
            }
            result.signs = combineSigns(result.signs, term, false);
        }
        return result;
    }

    // Exact polynomial long division over Q[other variables], only when the
    // divisor's leading coefficient is a nonzero rational constant. Thus
    // dividend = divisor*quotient + remainder is an unconditional identity.
    std::optional<std::pair<RationalPolynomial, RationalPolynomial>> divide(
        const RationalPolynomial& dividend, const RationalPolynomial& divisor, VarId var) {
        const int divisorDegree = divisor.degree(var);
        const int degree = dividend.degree(var);
        if (divisorDegree < 1 || degree < divisorDegree || degree > 64 || divisorDegree > 64)
            return std::nullopt;
        tick(divisor.terms().size() + 1);
        const auto leading = divisor.leadingCoefficient(var);
        if (!leading.isConstant() || leading.constantValue() == 0) return std::nullopt;
        ++stats_.factorDivisions;
        const mpq_class inverse = 1 / leading.constantValue();
        RationalPolynomial quotient, remainder = dividend;
        for (int current = degree; current >= divisorDegree;) {
            tick(remainder.terms().size() + 1);
            auto term = multiply(remainder.leadingCoefficient(var),
                RationalPolynomial::fromVar(var, current - divisorDegree, inverse));
            quotient += term;
            remainder -= multiply(divisor, term);
            const int next = remainder.degree(var);
            if (next >= current) return std::nullopt;
            current = next;
        }
        return std::make_pair(std::move(quotient), std::move(remainder));
    }

    std::optional<SignProof> proveNonnegative(const RationalPolynomial& polynomial) {
        tick();
        auto direct = monomialSum(polynomial);
        if (nonnegative(direct.signs)) return direct;
        for (const auto& premise : constraints_) {
            tick(premise.poly.terms().size() + 1);
            if (premise.poly.isConstant()) continue;
            for (const auto var : premise.poly.variables()) {
                tick();
                auto division = divide(polynomial, premise.poly, var);
                if (!division) continue;
                auto quotient = monomialSum(division->first);
                const auto product = combineSigns(relationSigns(premise.rel), quotient.signs, true);
                if (!nonnegative(product)) continue;
                auto remainder = monomialSum(division->second);
                const auto sum = combineSigns(product, remainder.signs, false);
                if (!nonnegative(sum)) continue;
                includeReasons(quotient.reasons, remainder.reasons);
                includeReasons(quotient.reasons, {premise.reason});
                return SignProof{sum, std::move(quotient.reasons)};
            }
        }
        return std::nullopt;
    }

public:
    QuadraticSignContext(const std::vector<SignRefuteConstraint>& constraints,
                         QuadraticSignStatistics& stats)
        : constraints_(constraints), variables_(collectVariableSigns(constraints)), stats_(stats) {}

    std::optional<std::vector<SatLit>> refute() {
        for (const auto& constraint : constraints_) {
            tick(constraint.poly.terms().size() + 1);
            if (constraint.rel == Relation::Neq) continue;
            const bool strictRequired = constraint.rel == Relation::Eq ||
                constraint.rel == Relation::Leq || constraint.rel == Relation::Geq;
            const bool negate = constraint.rel == Relation::Gt || constraint.rel == Relation::Geq;
            for (int orientation = 0; orientation < (constraint.rel == Relation::Eq ? 2 : 1); ++orientation) {
                auto oriented = negate || orientation ? -constraint.poly : constraint.poly;
                mpq_class constant = 0;
                for (const auto& [monomial, coefficient] : oriented.terms())
                    if (monomial.empty()) constant = coefficient;
                // A strictly positive constant may be separated: proving p-k>=0
                // for k>0 proves p>0. This also handles strict integer atoms
                // normalized to a non-strict relation with a unit offset.
                const int variants = strictRequired && constant > 0 ? 2 : 1;
                for (int variant = 0; variant < variants; ++variant) {
                    auto polynomial = oriented;
                    if (variant) polynomial.addConstant(-constant);
                    polynomial.normalize();
                    for (const auto var : polynomial.variables()) {
                        tick();
                        if (polynomial.degree(var) != 2) continue;
                        ++stats_.quadraticAttempts;
                        const auto coefficients = polynomial.coefficients(var);
                        auto a = proveNonnegative(coefficients[2]);
                        if (!a) continue;
                        auto c = proveNonnegative(coefficients[0]);
                        if (!c) continue; // needed when a=0; discriminant alone is insufficient
                        auto determinant = multiply(coefficients[2], coefficients[0]);
                        determinant *= 4;
                        determinant -= multiply(coefficients[1], coefficients[1]);
                        auto determinantProof = proveNonnegative(determinant);
                        if (!determinantProof) continue;
                        // A positive determinant makes the quadratic strictly
                        // positive. A weak determinant allows a zero and cannot
                        // alone refute equality or a non-strict upper bound.
                        if (strictRequired && !variant && determinantProof->signs != Positive) continue;
                        includeReasons(a->reasons, c->reasons);
                        includeReasons(a->reasons, determinantProof->reasons);
                        includeReasons(a->reasons, {constraint.reason});
                        ++stats_.certified;
                        return std::move(a->reasons);
                    }
                }
            }
        }
        return std::nullopt;
    }

};
} // namespace

std::optional<std::vector<SatLit>>
refuteByQuadraticSigns(const std::vector<SignRefuteConstraint>& constraints,
                       QuadraticSignStatistics* statistics) {
    QuadraticSignStatistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
    try {
        return QuadraticSignContext(constraints, stats).refute();
    } catch (const ResourceExhausted&) {
        stats.exhausted = true;
    }
    return std::nullopt;
}

} // namespace xolver
