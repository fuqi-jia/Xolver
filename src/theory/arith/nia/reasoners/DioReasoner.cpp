#include "theory/arith/nia/reasoners/DioReasoner.h"

#include <gmpxx.h>
#include <map>
#include <optional>
#include <set>
#include <vector>

namespace xolver {

DioReasoner::DioReasoner(PolynomialKernel& kernel) : kernel_(kernel) {}

NiaReasoningResult DioReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const std::vector<DioCongruence>& congruences) {
    if (congruences.empty())
        return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // Index congruences by variable (first congruence per variable).
    std::map<VarId, const DioCongruence*> cong;
    for (const auto& g : congruences) cong.emplace(g.var, &g);

    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;

        // Reduce  Σ aᵢ·xᵢ + c₀  modulo the COMMON modulus m of the variables'
        // congruences. Every non-constant monomial must be a single integer
        // variable (exponent 1) carrying a congruence with the same modulus m;
        // a nonlinear monomial, or a variable without such a congruence, leaves
        // slack, so the equality cannot be soundly reduced and is skipped.
        mpz_class m = 0;    // common modulus (0 = not yet pinned)
        mpz_class acc = 0;  // Σ aᵢ·rᵢ + c₀
        bool reducible = true;
        std::vector<SatLit> reasons{c.reason};
        std::set<std::pair<uint32_t, bool>> seen{{c.reason.var, c.reason.sign}};
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) {  // constant term
                acc += t.coefficient;
                continue;
            }
            if (t.powers.size() != 1 || t.powers[0].second != 1) {
                reducible = false;
                break;  // nonlinear monomial
            }
            auto it = cong.find(t.powers[0].first);
            if (it == cong.end()) {
                reducible = false;
                break;  // variable has no congruence
            }
            const DioCongruence& g = *it->second;
            if (m == 0) {
                m = g.modulus;
            } else if (m != g.modulus) {
                reducible = false;
                break;  // mixed moduli (a later increment can CRT/gcd-combine)
            }
            acc += t.coefficient * g.residue;
            if (seen.insert({g.reason.var, g.reason.sign}).second)
                reasons.push_back(g.reason);
        }
        if (!reducible || m <= 1) continue;

        // The equality forces  Σ aᵢ·rᵢ + c₀ ≡ 0 (mod m); a nonzero residue
        // means no integer solution exists ⇒ UNSAT. Exact for any modulus
        // (e.g. 2^32), with no residue enumeration.
        if (acc % m != 0) {
            return {NiaReasoningKind::Conflict, TheoryConflict{reasons}, std::nullopt};
        }
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
