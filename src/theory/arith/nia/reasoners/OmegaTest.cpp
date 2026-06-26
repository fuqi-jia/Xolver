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

// Drop variables that are bounded on only ONE side (only lower or only upper
// bounds): such a variable can be pushed to ±∞ to satisfy all its constraints
// regardless of the other variables, so those constraints impose nothing on the
// rest (Fourier–Motzkin: an unpaired bound projects to nothing). Sound.
void dropOneSidedVars(std::vector<Constraint>& cs) {
    for (bool changed = true; changed;) {
        changed = false;
        std::map<int, std::pair<long, long>> cnt;  // var -> (#lower, #upper)
        for (const auto& c : cs)
            for (const auto& [v, a] : c.coeffs) (a > 0 ? cnt[v].first : cnt[v].second)++;
        for (const auto& [v, lu] : cnt) {
            if (lu.first == 0 || lu.second == 0) {
                const int dead = v;
                cs.erase(std::remove_if(cs.begin(), cs.end(),
                         [&](const Constraint& c) { return c.coeffs.count(dead) != 0; }),
                         cs.end());
                changed = true;
                break;
            }
        }
    }
}

// EXACT integer elimination (Pugh §2.3 — dark shadow + splinters). Returns Unsat
// iff the conjunction has no integer solution (complete within the node budget;
// budget exhaustion yields SatOrUnknown — sound, never a false Unsat). The exact
// projection of a variable x is: (S has an integer solution) ⟺ (dark shadow has
// one) ∨ (some splinter has one). So S is UNSAT ⟺ dark shadow UNSAT ∧ every
// splinter UNSAT — proved by recursion. SOUNDNESS of claiming UNSAT relies on the
// splinter set covering all near-boundary integer solutions; the fuzz harness
// (0 false-UNSAT vs z3) is the guard.
Result decideRec(std::vector<Constraint> cs, long& nodes) {
    if (++nodes > 400000) return Result::SatOrUnknown;          // budget ⇒ no claim (splinter blowup)

    for (auto& c : cs)
        if (!normalizeOne(c)) return Result::Unsat;

    int nextVar = 0;
    for (const auto& c : cs)
        for (const auto& [v, a] : c.coeffs) { (void)a; nextVar = std::max(nextVar, v + 1); }
    if (!eliminateEqualities(cs, nextVar)) return Result::Unsat;

    // Any equality the guard left → two inequalities (sound).
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
    cs = std::move(ineqs);

    dropOneSidedVars(cs);
    for (auto& c : cs)
        if (!normalizeOne(c)) return Result::Unsat;

    // Pick the variable with the fewest lower×upper pairs (least splinter blowup).
    std::map<int, std::pair<long, long>> cnt;
    for (const auto& c : cs)
        for (const auto& [v, a] : c.coeffs) (a > 0 ? cnt[v].first : cnt[v].second)++;
    int x = -1;
    long best = -1;
    for (const auto& [v, lu] : cnt)
        if (lu.first > 0 && lu.second > 0) {
            long prod = lu.first * lu.second;
            if (best < 0 || prod < best) { best = prod; x = v; }
        }
    if (x < 0) return Result::SatOrUnknown;   // no two-sided var ⇒ feasible (constants already screened)

    std::vector<Constraint> lowers, uppers, rest;
    for (auto& c : cs) {
        auto it = c.coeffs.find(x);
        if (it == c.coeffs.end()) rest.push_back(c);
        else if (it->second > 0) lowers.push_back(c);
        else uppers.push_back(c);
    }
    mpz_class a = 1;  // largest upper-bound coefficient on x
    for (const auto& up : uppers) { mpz_class au = -up.coeffs.at(x); if (au > a) a = au; }

    // (1) Dark shadow: real projection of each (lower,upper) pair, tightened by
    //     −(α−1)(β−1). If it (recursively) has a solution, S may be SAT ⇒ no claim.
    {
        std::vector<Constraint> sdark = rest;
        for (const auto& lo : lowers) {
            const mpz_class b = lo.coeffs.at(x);
            for (const auto& up : uppers) {
                const mpz_class al = -up.coeffs.at(x);
                Constraint proj;
                proj.rel = Constraint::Geq;
                for (const auto& [v, c2] : lo.coeffs) if (v != x) proj.coeffs[v] += al * c2;
                for (const auto& [v, c2] : up.coeffs) if (v != x) proj.coeffs[v] += b * c2;
                proj.constant = al * lo.constant + b * up.constant - (al - 1) * (b - 1);
                sdark.push_back(std::move(proj));
            }
        }
        if (decideRec(std::move(sdark), nodes) != Result::Unsat) return Result::SatOrUnknown;
    }

    // (2) Splinters: dark shadow is UNSAT, so any integer solution sits within
    //     (a·β − a − β)/a of a lower bound β·x ≥ L. For each lower bound and each
    //     k in [0, ⌊(a·β − a − β)/a⌋], pin β·x = L + k (an equality) and recurse.
    //     If any pinned system is satisfiable, S is SAT ⇒ no claim.
    for (const auto& lo : lowers) {
        const mpz_class b = lo.coeffs.at(x);
        const mpz_class kmax = floordiv(a * b - a - b, a);
        for (mpz_class k = 0; k <= kmax; ++k) {
            std::vector<Constraint> sk = cs;
            Constraint pin = lo;
            pin.rel = Constraint::Eq;
            pin.constant = lo.constant - k;
            sk.push_back(std::move(pin));
            if (decideRec(std::move(sk), nodes) != Result::Unsat) return Result::SatOrUnknown;
        }
    }
    return Result::Unsat;   // dark shadow UNSAT and every splinter UNSAT ⇒ no integer solution
}

}  // namespace

Result decide(std::vector<Constraint> cs) {
    // Pugh's exact Omega test: normalize → equality elimination → dark shadow +
    // splinter recursion (decideRec). COMPLETE for integer UNSAT within the node
    // budget; budget exhaustion / unhandled forms yield SatOrUnknown — never a
    // false Unsat (validated by the fuzz harness vs z3).
    long nodes = 0;
    return decideRec(std::move(cs), nodes);
}

}  // namespace omega
}  // namespace xolver
