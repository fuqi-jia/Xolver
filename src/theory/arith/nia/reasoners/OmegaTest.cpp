#include "theory/arith/nia/reasoners/OmegaTest.h"

#include <algorithm>
#include <iterator>

namespace xolver {
namespace omega {
namespace {

// Floor division (GMP's mpz / truncates toward zero; the integer tightening needs floor).
mpz_class floordiv(const mpz_class& a, const mpz_class& b) {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return q;
}

// gcd of all coefficient magnitudes (constant excluded). Returns 0 iff no coeffs.
mpz_class coeffGcd(const Constraint& c) {
    mpz_class g = 0;
    for (const auto& [v, a] : c.coeffs) {
        (void)v;
        mpz_class t;
        mpz_gcd(t.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
        g = t;
    }
    return g;
}

// Normalize one constraint in place to `(Σ + const) Eq|Geq 0`, gcd-tightened.
// Returns false iff the constraint is by itself a contradiction (⇒ system Unsat).
bool normalizeOne(Constraint& c) {
    // Leq (e ≤ 0) → negate to (−e ≥ 0).
    if (c.rel == Constraint::Leq) {
        for (auto& [v, a] : c.coeffs) { (void)v; a = -a; }
        c.constant = -c.constant;
        c.rel = Constraint::Geq;
    }
    // Strip explicit zero coefficients.
    for (auto it = c.coeffs.begin(); it != c.coeffs.end();)
        it = (it->second == 0) ? c.coeffs.erase(it) : std::next(it);

    const mpz_class g = coeffGcd(c);
    if (g == 0) {  // pure-constant constraint: decide it directly.
        return c.rel == Constraint::Eq ? (c.constant == 0) : (c.constant >= 0);
    }
    if (c.rel == Constraint::Eq) {
        if (c.constant % g != 0) return false;          // g ∤ const ⇒ no integer solution
        for (auto& [v, a] : c.coeffs) { (void)v; a /= g; }
        c.constant /= g;
    } else {  // Geq: Σ(a/g)x + ⌊const/g⌋ ≥ 0  (sound integer tightening — LHS is a g-multiple)
        for (auto& [v, a] : c.coeffs) { (void)v; a /= g; }
        c.constant = floordiv(c.constant, g);
    }
    return true;
}

mpz_class mabs(const mpz_class& a) { return a < 0 ? mpz_class(-a) : a; }

// Substitute variable k by the expression (Σ e[v]·x_v + e0) in constraint c.
void substitute(Constraint& c, int k,
                const std::map<int, mpz_class>& e, const mpz_class& e0) {
    auto it = c.coeffs.find(k);
    if (it == c.coeffs.end()) return;             // c does not mention x_k
    const mpz_class a = it->second;
    c.coeffs.erase(it);
    for (const auto& [v, ev] : e) c.coeffs[v] += a * ev;
    c.constant += a * e0;
    for (auto i = c.coeffs.begin(); i != c.coeffs.end();)
        i = (i->second == 0) ? c.coeffs.erase(i) : std::next(i);
}

// Balanced residue of a modulo m (m>0): â ≡ a (mod m), â ∈ (−m/2, m/2] (round-half-up).
mpz_class balancedResidue(const mpz_class& a, const mpz_class& m) {
    return a - m * floordiv(2 * a + m, 2 * m);
}

// Pugh §2.2 equality elimination. Returns false iff a contradiction is proven
// (⇒ Unsat). On true, all equalities have been substituted out (system is now
// inequalities only) OR the safety guard tripped (no claim — caller continues).
bool eliminateEqualities(std::vector<Constraint>& cs, int& nextVar) {
    // Sound fallback: a runaway elimination just stops (yields SatOrUnknown) — it
    // NEVER produces a false Unsat. Termination is guaranteed in theory (max coeff
    // strictly decreases); the guard only defends against a pathological blowup.
    for (int guard = 0; guard < 200000; ++guard) {
        int ei = -1;
        for (int i = 0; i < static_cast<int>(cs.size()); ++i)
            if (cs[i].rel == Constraint::Eq) { ei = i; break; }
        if (ei < 0) return true;                  // no equalities remain

        if (cs[ei].coeffs.empty()) {              // constant-only equality
            if (cs[ei].constant != 0) return false;   // c == 0, c≠0 ⇒ Unsat
            cs.erase(cs.begin() + ei);
            continue;
        }
        // pivot = variable with smallest |coeff|; flip the equality so its coeff > 0.
        int k = cs[ei].coeffs.begin()->first;
        mpz_class ak = cs[ei].coeffs.begin()->second;
        for (const auto& [v, a] : cs[ei].coeffs)
            if (mabs(a) < mabs(ak)) { k = v; ak = a; }
        if (ak < 0) {
            for (auto& [v, a] : cs[ei].coeffs) { (void)v; a = -a; }
            cs[ei].constant = -cs[ei].constant;
            ak = -ak;
        }

        if (ak == 1) {
            // x_k = −(Σ_{j≠k} a_j x_j + c). Drop the equality, substitute everywhere.
            std::map<int, mpz_class> e;
            for (const auto& [v, a] : cs[ei].coeffs) if (v != k) e[v] = -a;
            const mpz_class e0 = -cs[ei].constant;
            cs.erase(cs.begin() + ei);
            for (auto& c : cs) { substitute(c, k, e, e0); if (!normalizeOne(c)) return false; }
        } else {
            // |a_k|>1: balanced-residue reduction. m = a_k+1 ⇒ â_k = −1, so
            // x_k = Σ_{j≠k} â_j x_j + â_0 − m·σ (fresh σ). Substituting into the
            // pivot equality leaves it m-divisible → normalizeOne shrinks it.
            const mpz_class m = ak + 1;
            const int sigma = nextVar++;
            std::map<int, mpz_class> e;
            for (const auto& [v, a] : cs[ei].coeffs)
                if (v != k) e[v] = balancedResidue(a, m);
            e[sigma] = -m;
            const mpz_class e0 = balancedResidue(cs[ei].constant, m);
            for (auto& c : cs) { substitute(c, k, e, e0); if (!normalizeOne(c)) return false; }
        }
    }
    return true;  // guard tripped — no claim
}

// Real-shadow Fourier–Motzkin elimination over the (Geq-only) inequalities.
// Returns false iff a contradiction is proven (⇒ Unsat). On true, either all
// variables were projected away leaving only satisfiable constants, or the budget
// tripped (no claim). SOUND for UNSAT: the real projection is a relaxation, so a
// projected contradiction implies the original (integer) system is infeasible.
// (Combined with the per-constraint integer tightening in normalizeOne, this
// already catches many integer-infeasible systems; the exact integer-only gap is
// closed by the dark shadow in a later commit.)
bool realShadowFM(std::vector<Constraint>& cs) {
    const size_t BUDGET = 6000;
    for (int guard = 0; guard < 100000; ++guard) {
        // Count, per variable, how many lower (coeff>0) vs upper (coeff<0) bounds.
        std::map<int, std::pair<long, long>> cnt;
        for (const auto& c : cs)
            for (const auto& [v, a] : c.coeffs)
                (a > 0 ? cnt[v].first : cnt[v].second)++;
        if (cnt.empty()) return true;            // no variables remain

        // Greedy: eliminate the variable with the fewest lower×upper pairs.
        int pick = cnt.begin()->first;
        long bestProd = -1;
        for (const auto& [v, lu] : cnt) {
            long prod = lu.first * lu.second;
            if (bestProd < 0 || prod < bestProd) { bestProd = prod; pick = v; }
        }

        std::vector<Constraint> lowers, uppers, next;
        for (auto& c : cs) {
            auto it = c.coeffs.find(pick);
            if (it == c.coeffs.end()) next.push_back(std::move(c));
            else if (it->second > 0) lowers.push_back(std::move(c));
            else uppers.push_back(std::move(c));
        }
        // Project each lower×upper pair (a·lower + b·upper cancels `pick`). Unpaired
        // lower/upper bounds impose no constraint after projecting (the var is free
        // on that side) and are simply dropped.
        for (const auto& lo : lowers) {
            const mpz_class b = lo.coeffs.at(pick);             // > 0
            for (const auto& up : uppers) {
                const mpz_class a = -up.coeffs.at(pick);        // > 0
                Constraint proj;
                proj.rel = Constraint::Geq;
                for (const auto& [v, c2] : lo.coeffs) if (v != pick) proj.coeffs[v] += a * c2;
                for (const auto& [v, c2] : up.coeffs) if (v != pick) proj.coeffs[v] += b * c2;
                proj.constant = a * lo.constant + b * up.constant;
                for (auto i = proj.coeffs.begin(); i != proj.coeffs.end();)
                    i = (i->second == 0) ? proj.coeffs.erase(i) : std::next(i);
                if (!normalizeOne(proj)) return false;          // projected contradiction ⇒ Unsat
                if (proj.coeffs.empty()) continue;              // trivially-true constant ⇒ drop
                next.push_back(std::move(proj));
                if (next.size() > BUDGET) return true;          // blowup ⇒ no claim
            }
        }
        cs = std::move(next);
    }
    return true;  // guard tripped — no claim
}

}  // namespace

Result decide(std::vector<Constraint> cs) {
    // ── Stage 0: normalize + per-constraint contradiction screen ──
    for (auto& c : cs)
        if (!normalizeOne(c)) return Result::Unsat;

    // ── Stage 1: equality elimination ──
    int nextVar = 0;
    for (const auto& c : cs)
        for (const auto& [v, a] : c.coeffs) { (void)a; nextVar = std::max(nextVar, v + 1); }
    if (!eliminateEqualities(cs, nextVar)) return Result::Unsat;

    // ── Stage 2: real-shadow Fourier–Motzkin ──
    // Any equality the elimination guard left behind becomes two inequalities
    // (e ≥ 0 ∧ −e ≥ 0) so FM stays sound.
    std::vector<Constraint> ineqs;
    for (auto& c : cs) {
        if (c.rel != Constraint::Eq) { ineqs.push_back(std::move(c)); continue; }
        Constraint lo = c, hi;
        lo.rel = Constraint::Geq;
        hi.rel = Constraint::Geq;
        for (const auto& [v, a] : c.coeffs) hi.coeffs[v] = -a;
        hi.constant = -c.constant;
        if (!normalizeOne(lo) || !normalizeOne(hi)) return Result::Unsat;
        ineqs.push_back(std::move(lo));
        ineqs.push_back(std::move(hi));
    }
    if (!realShadowFM(ineqs)) return Result::Unsat;

    // Stage 3 (dark shadow + exact splinters) follows in a later commit; until then
    // a real-feasible-but-integer-infeasible residue is reported SatOrUnknown.
    return Result::SatOrUnknown;
}

}  // namespace omega
}  // namespace xolver
