#include "theory/arith/refute/SignDefinitenessRefuter.h"

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

} // namespace

std::optional<std::vector<SatLit>>
refuteBySignDefiniteness(const std::vector<SignRefuteConstraint>& constraints) {
    // 1. Derive variable signs from single-variable linear bounds (strongest wins).
    std::unordered_map<VarId, VarSignInfo> varSign;
    for (const auto& c : constraints) {
        auto lb = asLinearBound(c.poly);
        if (!lb) continue;
        VarSign s = signFromBound(*lb, c.rel);
        if (s == VarSign::Unknown) continue;
        auto& slot = varSign[lb->v];
        if (strength(s) > strength(slot.sign)) { slot.sign = s; slot.reason = c.reason; }
    }
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

} // namespace xolver
