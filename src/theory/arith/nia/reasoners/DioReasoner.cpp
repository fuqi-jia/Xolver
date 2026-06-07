#include "theory/arith/nia/reasoners/DioReasoner.h"

#include <algorithm>
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

std::optional<std::vector<SatLit>> DioReasoner::tightenConflict(
    const std::vector<DioLinForm>& constraints,
    const std::map<std::string, DioVarBound>& bounds) {
    // Lattice equalities, each with the literal(s) justifying it. Three sources:
    //  (1) the explicit equality atoms (single reason);
    //  (2) bound-PINNED variables (lo == hi) → the equality `v = lo`, justified
    //      by both bound literals — how a mod-zero expressed as `r ≤ 0 ∧ r ≥ 0`
    //      (rather than `r = 0`) still feeds the divisibility `x = M·q + r`;
    //  (3) folded complementary inequality pairs (`f ≤ c` ∧ `f ≥ c` ⟹ `f = c`),
    //      justified by both inequality literals — how the SVCOMP overflow-wrap
    //      chain (all inequalities, no equality atoms) enters the lattice.
    struct IEq { std::vector<std::pair<std::string, mpz_class>> coeffs; mpz_class cst;
                 std::vector<SatLit> reasons; };
    std::vector<IEq> ieqs;
    std::vector<DioLinForm> neqs;

    // (1) explicit equalities; collect disequalities; gather the inequalities
    //     keyed by sign-normalized form for complementary-pair folding (3).
    struct UL { bool hasU=false, hasL=false; mpz_class u, l; SatLit ur, lr; };
    std::map<std::vector<std::pair<std::string, mpz_class>>, UL> ineqGroups;
    for (const auto& c : constraints) {
        if (c.rel == Relation::Eq) { ieqs.push_back({c.coeffs, c.cst, {c.reason}}); continue; }
        if (c.rel == Relation::Neq) { neqs.push_back(c); continue; }
        // Leq / Geq (callers pre-convert strict Lt/Gt to integer non-strict).
        if (c.rel != Relation::Leq && c.rel != Relation::Geq) continue;
        if (c.coeffs.empty()) continue;
        Relation rel = c.rel;
        // Sign-normalize so the leading (first) coefficient is positive; flip the
        // relation if we negate. `key` is the canonical form Σkey·v; the bound is
        // on key: Leq ⟹ key ≤ -cst', Geq ⟹ key ≥ -cst'.
        bool neg = c.coeffs.front().second < 0;
        std::vector<std::pair<std::string, mpz_class>> key;
        for (const auto& [v, a] : c.coeffs) key.emplace_back(v, neg ? -a : a);
        mpz_class kc = neg ? -c.cst : c.cst;
        if (neg) rel = (rel == Relation::Leq) ? Relation::Geq : Relation::Leq;
        UL& g = ineqGroups[key];
        if (rel == Relation::Leq) { if (!g.hasU || -kc < g.u) { g.hasU = true; g.u = -kc; g.ur = c.reason; } }
        else                      { if (!g.hasL || -kc > g.l) { g.hasL = true; g.l = -kc; g.lr = c.reason; } }
    }
    if (neqs.empty()) return std::nullopt;

    // (2) bound-pinned vars → equalities.
    for (const auto& [v, bb] : bounds) {
        if (!(bb.hasLo && bb.hasHi && bb.lo == bb.hi)) continue;
        std::vector<SatLit> rs = bb.loReasons;
        rs.insert(rs.end(), bb.hiReasons.begin(), bb.hiReasons.end());
        ieqs.push_back({{{v, mpz_class(1)}}, -bb.lo, std::move(rs)});  // v - lo = 0
    }
    // (3) complementary inequality pairs with equal tight bound → equality.
    for (const auto& [key, g] : ineqGroups) {
        if (!(g.hasU && g.hasL && g.u == g.l)) continue;
        ieqs.push_back({key, -g.u, {g.ur, g.lr}});  // key - u = 0
    }
    if (ieqs.empty()) return std::nullopt;

    // Column space = every variable appearing in a (lattice) equality or a diseq.
    std::map<std::string, int> colIdx;
    std::vector<std::string> cols;
    auto intern = [&](const std::string& v) {
        auto it = colIdx.find(v);
        if (it != colIdx.end()) return it->second;
        int id = static_cast<int>(cols.size());
        colIdx[v] = id;
        cols.push_back(v);
        return id;
    };
    for (const auto& e : ieqs) for (const auto& [v, a] : e.coeffs) { (void)a; intern(v); }
    for (const auto& d : neqs) for (const auto& [v, a] : d.coeffs) { (void)a; intern(v); }
    const int n = static_cast<int>(cols.size());
    const int m = static_cast<int>(ieqs.size());
    if (n == 0) return std::nullopt;

    // SNF is super-linear in rows×cols — skip pathological systems so this never
    // becomes a time sink on large QF_(A)NIA inputs.
    constexpr size_t CAP = 256;
    if (ieqs.size() > CAP || cols.size() > CAP) return std::nullopt;

    // A·x = b  (Σ a·x = -cst).  Coefficients are already integer.
    IntMatrix A(m, std::vector<mpz_class>(n, mpz_class(0)));
    std::vector<mpz_class> b(m, mpz_class(0));
    for (int i = 0; i < m; ++i) {
        for (const auto& [v, a] : ieqs[i].coeffs) A[i][colIdx.at(v)] += a;
        b[i] = -ieqs[i].cst;
    }

    std::vector<std::optional<mpz_class>> lo(n), hi(n);
    for (int j = 0; j < n; ++j) {
        auto it = bounds.find(cols[j]);
        if (it == bounds.end()) continue;
        if (it->second.hasLo) lo[j] = it->second.lo;
        if (it->second.hasHi) hi[j] = it->second.hi;
    }

    for (const auto& d : neqs) {
        std::vector<mpz_class> formW(n, mpz_class(0));
        for (const auto& [v, a] : d.coeffs) formW[colIdx.at(v)] += a;
        if (!latticeForcesFormZero(A, b, lo, hi, formW, d.cst)) continue;

        // Sound conflict: the lattice equalities (incl. the pinned-bound ones,
        // with their bound literals), this disequality, and the bound literals of
        // the form's variables (the hull) are jointly inconsistent. Including
        // ALL lattice reasons is an over-approximation, hence sound.
        std::vector<SatLit> rs;
        std::set<std::pair<uint32_t, bool>> seen;
        auto add = [&](const SatLit& l) { if (seen.insert({l.var, l.sign}).second) rs.push_back(l); };
        for (const auto& e : ieqs) for (const auto& l : e.reasons) add(l);
        add(d.reason);
        for (int j = 0; j < n; ++j) {
            if (formW[j] == 0) continue;
            auto it = bounds.find(cols[j]);
            if (it == bounds.end()) continue;
            for (const auto& l : it->second.loReasons) add(l);
            for (const auto& l : it->second.hiReasons) add(l);
        }
        return rs;
    }
    return std::nullopt;
}

bool DioReasoner::latticeForcesFormZero(
    const IntMatrix& A,
    const std::vector<mpz_class>& b,
    const std::vector<std::optional<mpz_class>>& lo,
    const std::vector<std::optional<mpz_class>>& hi,
    const std::vector<mpz_class>& formW,
    const mpz_class& formC) {
    const int m = static_cast<int>(A.size());
    const int n = (m > 0) ? static_cast<int>(A[0].size()) : static_cast<int>(formW.size());
    if (n == 0 || m == 0) return false;  // no equality lattice → cannot force
    if (static_cast<int>(formW.size()) != n || static_cast<int>(lo.size()) != n ||
        static_cast<int>(hi.size()) != n || static_cast<int>(b.size()) != m)
        return false;  // defensive dimension check — never a false conflict

    // Every form variable (nonzero weight) must be bounded both sides; otherwise
    // the hull is unbounded and no tightening is possible.
    for (int j = 0; j < n; ++j) {
        if (formW[j] == 0) continue;
        if (!lo[j] || !hi[j]) return false;
    }

    SmithNormalForm snf = smithNormalForm(A);          // U·A·V = D
    std::vector<mpz_class> bp = matVec(snf.U, b);       // b' = U·b
    const int diagN = std::min(snf.m, snf.n);

    // Existence: if A·x = b has NO integer solution, the equalities ALONE are
    // UNSAT — out of this core's scope (presolve HNF owns the pure-equality
    // conflict). Return false so we never mis-attribute it to the disequality.
    for (int i = 0; i < snf.m; ++i) {
        mpz_class d = (i < diagN) ? snf.D[i][i] : mpz_class(0);
        bool bad = (d != 0) ? (bp[i] % d != 0) : (bp[i] != 0);
        if (bad) return false;
    }

    // Particular solution y, free columns, x0 = V·y.
    std::vector<mpz_class> y(n, mpz_class(0));
    std::vector<bool> isFree(n, true);
    for (int i = 0; i < diagN; ++i)
        if (snf.D[i][i] != 0) { y[i] = bp[i] / snf.D[i][i]; isFree[i] = false; }
    std::vector<mpz_class> x0 = matVec(snf.V, y);
    std::vector<int> freeCols;
    for (int j = 0; j < n; ++j) if (isFree[j]) freeCols.push_back(j);

    // A0 = form(x0); g = gcd over free cols f of (Σ_k formW[k]·V[k][f]).
    // The form's achievable values lie in A0 + g·ℤ (sound: the free parameters
    // s_f contribute Σ_f (Σ_k formW[k]·V[k][f])·s_f ∈ g·ℤ).
    mpz_class A0 = formC;
    for (int k = 0; k < n; ++k) A0 += formW[k] * x0[k];
    mpz_class g = 0;
    for (int f : freeCols) {
        mpz_class cf = 0;
        for (int k = 0; k < n; ++k) cf += formW[k] * snf.V[k][f];
        mpz_class tmp;
        mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), cf.get_mpz_t());
        g = tmp;
    }
    g = abs(g);

    // Bound hull [Lmin, Lmax] of the form (all form vars are bounded, checked).
    mpz_class Lmin = formC, Lmax = formC;
    for (int k = 0; k < n; ++k) {
        if (formW[k] == 0) continue;
        const mpz_class& l = *lo[k];
        const mpz_class& h = *hi[k];
        if (formW[k] > 0) { Lmin += formW[k] * l; Lmax += formW[k] * h; }
        else              { Lmin += formW[k] * h; Lmax += formW[k] * l; }
    }
    if (Lmin > Lmax) return false;  // defensive (only if some lo > hi)

    if (g == 0) {
        // The form is constant A0 on the entire solution lattice. It is forced
        // to 0 iff A0 == 0 and 0 is in the hull (else the system is infeasible —
        // still UNSAT under form≠0, but we keep the crisp "forced 0" contract).
        return (A0 == 0 && Lmin <= 0 && 0 <= Lmax);
    }

    // Form lattice points: v ≡ A0 (mod g). Smallest such v ≥ Lmin.
    mpz_class r = ((A0 % g) + g) % g;                       // canonical residue
    mpz_class off = (((r - (Lmin % g)) % g) + g) % g;
    mpz_class v0 = Lmin + off;                              // leftmost point ≥ Lmin
    if (v0 > Lmax) return true;                             // hull ∩ lattice = ∅ → UNSAT
    // achievable(form) ⊆ {v0, v0+g, …} ∩ [Lmin, Lmax]. Asserting form≠0 is UNSAT
    // iff every such point is 0 — i.e. v0 == 0 and the next point overshoots.
    if (v0 == 0) return (v0 + g > Lmax);
    return false;                                           // a nonzero point ≤ Lmax exists
}

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
