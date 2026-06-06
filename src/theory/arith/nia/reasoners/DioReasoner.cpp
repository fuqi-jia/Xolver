#include "theory/arith/nia/reasoners/DioReasoner.h"

#include <gmpxx.h>
#include <map>
#include <optional>
#include <set>
#include <vector>

namespace xolver {

namespace {
// Reduce r into the canonical residue [0, m).
mpz_class normMod(const mpz_class& r, const mpz_class& m) {
    mpz_class x = r % m;
    if (x < 0) x += m;
    return x;
}
}  // namespace

DioReasoner::DioReasoner(PolynomialKernel& kernel) : kernel_(kernel) {}

NiaReasoningResult DioReasoner::run(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const std::vector<DioCongruence>& congruences) {
    // Internal congruence with ACCUMULATED reasons (so a derived congruence
    // carries the literals of the equalities + congruences it was derived from,
    // for a sound conflict clause).
    struct Cong { mpz_class residue; mpz_class modulus; std::vector<SatLit> reasons; };
    std::map<VarId, Cong> cong;
    for (const auto& g : congruences)
        cong[g.var] = {normMod(g.residue, g.modulus), g.modulus, {g.reason}};
    if (cong.empty()) return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};

    // Pre-extract the linear form of every Eq constraint (drop nonlinear ones —
    // they leave slack this kernel cannot reduce).
    struct Lin { std::map<VarId, mpz_class> coeffs; mpz_class cst; SatLit reason; };
    std::vector<Lin> eqs;
    for (const auto& c : constraints) {
        if (c.rel != Relation::Eq) continue;
        auto termsOpt = kernel_.terms(c.poly);
        if (!termsOpt) continue;
        Lin lin;
        lin.cst = 0;
        lin.reason = c.reason;
        bool ok = true;
        for (const auto& t : *termsOpt) {
            if (t.powers.empty()) { lin.cst = t.coefficient; continue; }
            if (t.powers.size() != 1 || t.powers[0].second != 1) { ok = false; break; }
            lin.coeffs[t.powers[0].first] += t.coefficient;
        }
        if (ok && !lin.coeffs.empty()) eqs.push_back(std::move(lin));
    }

    auto addReasons = [](std::vector<SatLit>& dst, std::set<std::pair<uint32_t, bool>>& seen,
                         const std::vector<SatLit>& src) {
        for (const auto& l : src)
            if (seen.insert({l.var, l.sign}).second) dst.push_back(l);
    };

    // PROPAGATION fixpoint: when an equality has exactly ONE variable lacking a
    // congruence, that variable's coefficient is ±1, and every other variable
    // carries a congruence with the SAME modulus m, solve for the missing
    // variable mod m:  a_t·t + S = 0  =>  t ≡ -a_t·S (mod m)  (1/a_t = a_t for
    // a_t = ±1). This derives e.g. z9 ≡ 2·y2 along an equality chain. Sound:
    // a logical consequence of the equality and the used congruences; reasons
    // accumulate.
    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto& e : eqs) {
            VarId target = 0;
            bool haveTarget = false, multiMissing = false, mixedMod = false;
            mpz_class m = 0;
            for (const auto& [v, a] : e.coeffs) {
                (void)a;
                auto it = cong.find(v);
                if (it == cong.end()) {
                    if (haveTarget) { multiMissing = true; break; }
                    target = v;
                    haveTarget = true;
                } else if (m == 0) {
                    m = it->second.modulus;
                } else if (m != it->second.modulus) {
                    mixedMod = true;
                }
            }
            if (multiMissing || !haveTarget || mixedMod || m == 0) continue;
            const mpz_class av = e.coeffs.at(target);
            if (av != 1 && av != -1) continue;

            mpz_class sumRest = e.cst;
            std::vector<SatLit> rs;
            std::set<std::pair<uint32_t, bool>> seen;
            addReasons(rs, seen, {e.reason});
            for (const auto& [v, a] : e.coeffs) {
                if (v == target) continue;
                const Cong& cv = cong.at(v);
                sumRest += a * cv.residue;
                addReasons(rs, seen, cv.reasons);
            }
            cong[target] = {normMod(-av * sumRest, m), m, std::move(rs)};
            changed = true;
        }
    }

    // CHECK: every equality whose variables all carry a same-modulus congruence
    // must satisfy  Σ aᵢ·rᵢ + c₀ ≡ 0 (mod m); a nonzero residue ⇒ UNSAT.
    for (const auto& e : eqs) {
        mpz_class m = 0, acc = e.cst;
        bool reducible = true;
        std::vector<SatLit> rs;
        std::set<std::pair<uint32_t, bool>> seen;
        addReasons(rs, seen, {e.reason});
        for (const auto& [v, a] : e.coeffs) {
            auto it = cong.find(v);
            if (it == cong.end()) { reducible = false; break; }
            if (m == 0) m = it->second.modulus;
            else if (m != it->second.modulus) { reducible = false; break; }
            acc += a * it->second.residue;
            addReasons(rs, seen, it->second.reasons);
        }
        if (!reducible || m <= 1) continue;
        if (acc % m != 0)
            return {NiaReasoningKind::Conflict, TheoryConflict{rs}, std::nullopt};
    }
    return {NiaReasoningKind::NoChange, std::nullopt, std::nullopt};
}

} // namespace xolver
