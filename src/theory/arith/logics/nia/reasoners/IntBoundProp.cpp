#include "theory/arith/logics/nia/reasoners/IntBoundProp.h"

namespace xolver::intprop {
namespace {

constexpr int MAX_VARS = 1024;   // bounded; oversized systems bail (no over-tightening)

mpz_class floordiv(const mpz_class& a, const mpz_class& m) {   // m > 0
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), a.get_mpz_t(), m.get_mpz_t());
    return q;
}
mpz_class ceildiv(const mpz_class& a, const mpz_class& m) {    // m > 0
    mpz_class q;
    mpz_cdiv_q(q.get_mpz_t(), a.get_mpz_t(), m.get_mpz_t());
    return q;
}

// Tighten bounds[j] for the equality, using the other variables' bounds. Returns
// false iff the variable's domain becomes empty (⇒ Unsat). `changed` is set true if
// the bound strictly tightened.
bool tightenForVar(const omega::Constraint& c, int j, const mpz_class& aj,
                   std::map<int, Bound>& bounds, bool& changed) {
    // Range of S = Σ_{i≠j} aᵢxᵢ + c from the other vars' current bounds. A side is
    // "open" (infinite) if a contributing var lacks the bound that side needs.
    mpz_class sLo = c.constant, sHi = c.constant;
    bool sLoFinite = true, sHiFinite = true;
    for (const auto& [v, a] : c.coeffs) {
        if (v == j) continue;
        const Bound& b = bounds[v];
        if (a > 0) {
            if (b.hasLo) sLo += a * b.lo; else sLoFinite = false;   // min uses lo
            if (b.hasHi) sHi += a * b.hi; else sHiFinite = false;   // max uses hi
        } else {  // a < 0: min uses hi, max uses lo
            if (b.hasHi) sLo += a * b.hi; else sLoFinite = false;
            if (b.hasLo) sHi += a * b.lo; else sHiFinite = false;
        }
    }

    // aⱼ·xⱼ = −S ∈ [−sHi, −sLo].  (numLo finite iff sHi finite, numHi iff sLo finite.)
    const bool numLoFinite = sHiFinite, numHiFinite = sLoFinite;
    const mpz_class numLo = -sHi, numHi = -sLo;
    const mpz_class m = abs(aj);

    // Derive integer bounds on xⱼ; dividing by a negative aⱼ flips the interval.
    bool newLoF = false, newHiF = false;
    mpz_class newLo, newHi;
    if (aj > 0) {
        if (numLoFinite) { newLo = ceildiv(numLo, m);  newLoF = true; }
        if (numHiFinite) { newHi = floordiv(numHi, m); newHiF = true; }
    } else {
        if (numHiFinite) { newLo = ceildiv(-numHi, m);  newLoF = true; }
        if (numLoFinite) { newHi = floordiv(-numLo, m); newHiF = true; }
    }

    Bound& bj = bounds[j];
    if (newLoF && (!bj.hasLo || newLo > bj.lo)) { bj.lo = newLo; bj.hasLo = true; changed = true; }
    if (newHiF && (!bj.hasHi || newHi < bj.hi)) { bj.hi = newHi; bj.hasHi = true; changed = true; }
    if (bj.hasLo && bj.hasHi && bj.lo > bj.hi) return false;   // empty domain ⇒ Unsat
    return true;
}

}  // namespace

Result propagate(const std::vector<omega::Constraint>& cs,
                 std::map<int, Bound>& bounds, int maxRounds) {
    // Register every equality variable (default unbounded) and screen size.
    for (const auto& c : cs) {
        if (c.rel != omega::Constraint::Eq) continue;
        for (const auto& [v, a] : c.coeffs) { (void)a; bounds.emplace(v, Bound{}); }
    }
    if (bounds.size() > static_cast<size_t>(MAX_VARS)) return Result::Ok;   // bounded; no claim

    for (int round = 0; round < maxRounds; ++round) {
        bool changed = false;
        for (const auto& c : cs) {
            if (c.rel != omega::Constraint::Eq) continue;
            for (const auto& [j, aj] : c.coeffs) {
                if (aj == 0) continue;
                if (!tightenForVar(c, j, aj, bounds, changed)) return Result::Unsat;
            }
        }
        if (!changed) break;   // fixpoint
    }
    return Result::Ok;
}

}  // namespace xolver::intprop
