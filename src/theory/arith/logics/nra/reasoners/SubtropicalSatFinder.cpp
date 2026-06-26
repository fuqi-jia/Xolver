#include "theory/arith/logics/nra/reasoners/SubtropicalSatFinder.h"

#include <algorithm>
#include <functional>

namespace xolver {

namespace {

// --- Exact rational Fourier-Motzkin ----------------------------------------
// A row encodes the inequality  <coeff, a>  >=  rhs.
struct LpRow {
    std::vector<mpq_class> coeff;  // length n
    mpq_class rhs;
};

// Eliminate variable `j` from `rows` (Fourier-Motzkin) into `out`, the reduced
// system in the remaining variables. Returns false on row-count overflow.
bool eliminateVar(const std::vector<LpRow>& rows, int j, int n, long rowCap,
                  std::vector<LpRow>& out) {
    std::vector<const LpRow*> pos, neg;
    out.clear();
    for (const auto& r : rows) {
        const int s = sgn(r.coeff[j]);
        if (s > 0) pos.push_back(&r);
        else if (s < 0) neg.push_back(&r);
        else out.push_back(r);  // var j absent: carry through unchanged
    }
    for (const LpRow* p : pos) {
        for (const LpRow* q : neg) {
            // Positive combination cancelling a_j: mp = -q[j] (>0), mq = p[j] (>0).
            const mpq_class mp = -q->coeff[j];
            const mpq_class mq = p->coeff[j];
            LpRow comb;
            comb.coeff.assign(n, mpq_class(0));
            for (int i = 0; i < n; ++i) comb.coeff[i] = mp * p->coeff[i] + mq * q->coeff[i];
            comb.coeff[j] = 0;  // exact cancellation
            comb.rhs = mp * p->rhs + mq * q->rhs;
            out.push_back(std::move(comb));
            if (static_cast<long>(out.size()) > rowCap) return false;
        }
    }
    return true;
}

// Feasibility of  {<c,a> >= rhs}  over the rationals. If `witness` is non-null
// and feasible, fills a feasible point. Returns false on infeasibility OR
// row-cap overflow (sound for our use: caller treats it as "no witness here").
bool fmSolve(std::vector<LpRow> rows, int n, long rowCap,
             std::vector<mpq_class>* witness) {
    // systems[k+1] = the system in variables 0..k, captured just before
    // eliminating variable k (we eliminate from n-1 down to 0).
    std::vector<std::vector<LpRow>> systems(n + 1);
    std::vector<LpRow> cur = std::move(rows);
    for (int j = n - 1; j >= 0; --j) {
        systems[j + 1] = cur;
        std::vector<LpRow> next;
        if (!eliminateVar(cur, j, n, rowCap, next)) return false;
        cur = std::move(next);
    }
    for (const auto& r : cur) {  // no vars left: rows are 0 >= rhs
        if (sgn(r.rhs) > 0) return false;
    }
    if (!witness) return true;

    witness->assign(n, mpq_class(0));
    for (int j = 0; j < n; ++j) {
        bool hasLo = false, hasHi = false;
        mpq_class lo, hi;
        for (const auto& r : systems[j + 1]) {
            const int s = sgn(r.coeff[j]);
            if (s == 0) continue;
            mpq_class rem = r.rhs;
            for (int i = 0; i < j; ++i) rem -= r.coeff[i] * (*witness)[i];
            const mpq_class bound = rem / r.coeff[j];  // a_j >= bound (s>0) / <= bound (s<0)
            if (s > 0) { if (!hasLo || bound > lo) { lo = bound; hasLo = true; } }
            else       { if (!hasHi || bound < hi) { hi = bound; hasHi = true; } }
        }
        if (hasLo && hasHi) (*witness)[j] = (lo + hi) / 2;
        else if (hasLo)     (*witness)[j] = lo;
        else if (hasHi)     (*witness)[j] = hi;
        else                (*witness)[j] = 0;
    }
    return true;
}

// --- GF(2) linear system (reduced-row-echelon) -----------------------------
struct Gf2System {
    int n;
    std::vector<std::vector<char>> rows;  // RREF, distinct pivot columns
    std::vector<char> rhs;
    std::vector<int> pivotCol;
    explicit Gf2System(int n_) : n(n_) {}

    // Add  <row, sigma> = b. Returns false iff inconsistent (0 = 1).
    bool add(std::vector<char> row, char b) {
        for (size_t i = 0; i < rows.size(); ++i) {
            if (row[pivotCol[i]]) {
                for (int c = 0; c < n; ++c) row[c] ^= rows[i][c];
                b ^= rhs[i];
            }
        }
        int lead = -1;
        for (int c = 0; c < n; ++c) if (row[c]) { lead = c; break; }
        if (lead == -1) return b == 0;
        for (size_t i = 0; i < rows.size(); ++i) {  // back-reduce for RREF
            if (rows[i][lead]) {
                for (int c = 0; c < n; ++c) rows[i][c] ^= row[c];
                rhs[i] ^= b;
            }
        }
        rows.push_back(std::move(row));
        rhs.push_back(b);
        pivotCol.push_back(lead);
        return true;
    }

    std::vector<char> solve() const {  // free vars = 0; valid because RREF
        std::vector<char> sigma(n, 0);
        for (size_t i = 0; i < rows.size(); ++i) sigma[pivotCol[i]] = rhs[i];
        return sigma;
    }
};

// Consistency of a collected set of parity equations.
bool gf2Consistent(const std::vector<std::pair<std::vector<char>, char>>& eqs, int n) {
    Gf2System sys(n);
    for (const auto& e : eqs) {
        if (!sys.add(e.first, e.second)) return false;
    }
    return true;
}

} // namespace

// ============================================================================

SubtropicalResult SubtropicalSatFinder::find(
    const std::vector<SubtropicalConstraint>& constraints,
    const std::vector<VarId>& vars) const {
    SubtropicalResult res;

    const int n = static_cast<int>(vars.size());
    if (n == 0 || n > cfg_.maxVars) { res.unsupported = true; return res; }
    if (static_cast<int>(constraints.size()) > cfg_.maxConstraints) {
        res.unsupported = true; return res;
    }

    std::unordered_map<VarId, int> idx;
    idx.reserve(vars.size() * 2);
    for (int i = 0; i < n; ++i) idx.emplace(vars[i], i);

    struct Mono { std::vector<int> e; int csign; };
    struct Cons { std::vector<Mono> monos; Relation rel; };
    std::vector<Cons> cons;
    cons.reserve(constraints.size());

    int totalMonos = 0;
    for (const auto& c : constraints) {
        if (c.rel == Relation::Eq) { res.unsupported = true; return res; }
        Cons cc; cc.rel = c.rel;
        for (const auto& m : c.monomials) {
            if (m.coeff == 0) continue;
            Mono mm; mm.e.assign(n, 0); mm.csign = sgn(m.coeff);
            for (const auto& [v, exp] : m.powers) {
                auto it = idx.find(v);
                if (it == idx.end()) { res.unsupported = true; return res; }
                mm.e[it->second] += exp;
            }
            cc.monos.push_back(std::move(mm));
            if (++totalMonos > cfg_.maxMonomials) { res.unsupported = true; return res; }
        }
        if (cc.monos.empty()) {  // "0 rel 0"
            if (c.rel == Relation::Geq || c.rel == Relation::Leq) continue;  // true
            return res;  // 0>0 / 0<0 / 0!=0 false: whole system unsat -> not found
        }
        cons.push_back(std::move(cc));
    }
    if (cons.empty()) { res.found = true; return res; }  // all constraints trivially true

    // Backtracking frame search.
    long nodes = 0;
    std::vector<LpRow> lpRows;
    std::vector<std::pair<std::vector<char>, char>> parityEqs;
    std::vector<mpq_class> witnessA;

    std::function<bool(size_t)> recurse = [&](size_t k) -> bool {
        if (++nodes > cfg_.searchNodeCap) return false;
        if (k == cons.size()) {
            return fmSolve(lpRows, n, cfg_.fmRowCap, &witnessA);
        }
        const Cons& cc = cons[k];
        for (size_t fi = 0; fi < cc.monos.size(); ++fi) {
            const Mono& f = cc.monos[fi];

            const size_t lpFrom = lpRows.size();
            for (size_t gi = 0; gi < cc.monos.size(); ++gi) {
                if (gi == fi) continue;
                const Mono& g = cc.monos[gi];
                LpRow r; r.coeff.assign(n, mpq_class(0)); r.rhs = 1;
                for (int i = 0; i < n; ++i) r.coeff[i] = f.e[i] - g.e[i];
                lpRows.push_back(std::move(r));
            }
            const bool lpOk = fmSolve(lpRows, n, cfg_.fmRowCap, nullptr);

            bool parityPushed = false, parityOk = true;
            if (lpOk && cc.rel != Relation::Neq) {
                const int reqSign = (cc.rel == Relation::Gt || cc.rel == Relation::Geq) ? 1 : -1;
                // sign(c_f)*(-1)^{<e_f,sigma>} = reqSign  =>  parity bit b
                const char b = (reqSign * f.csign > 0) ? 0 : 1;
                std::vector<char> row(n, 0);
                for (int i = 0; i < n; ++i) row[i] = static_cast<char>(f.e[i] & 1);
                parityEqs.emplace_back(std::move(row), b);
                parityPushed = true;
                parityOk = gf2Consistent(parityEqs, n);
            }

            if (lpOk && parityOk && recurse(k + 1)) return true;

            lpRows.resize(lpFrom);
            if (parityPushed) parityEqs.pop_back();
        }
        return false;
    };

    if (!recurse(0)) return res;  // not found

    // Success: rational direction in witnessA, signs from the parity system.
    Gf2System gf2(n);
    for (const auto& e : parityEqs) gf2.add(e.first, e.second);
    const std::vector<char> sigma = gf2.solve();

    // Clear denominators: integer direction = D * a, D = lcm of denominators.
    mpz_class D = 1;
    for (const auto& q : witnessA) {
        const mpz_class den = q.get_den();
        mpz_class g; mpz_gcd(g.get_mpz_t(), D.get_mpz_t(), den.get_mpz_t());
        D = D / g * den;
    }
    res.found = true;
    for (int i = 0; i < n; ++i) {
        mpq_class scaled = witnessA[i] * mpq_class(D);
        scaled.canonicalize();  // integer now (denominator 1)
        res.dir.exponents[vars[i]] = scaled.get_num();
        res.dir.signs[vars[i]] = (i < static_cast<int>(sigma.size()) && sigma[i]) ? -1 : 1;
    }
    return res;
}

std::unordered_map<VarId, mpq_class>
SubtropicalSatFinder::materialize(const SubtropicalDirection& dir,
                                  const std::vector<VarId>& vars,
                                  const mpq_class& base) {
    std::unordered_map<VarId, mpq_class> model;
    const mpz_class bz = base.get_num();  // base is an integer > 1
    for (VarId v : vars) {
        mpz_class a = 0;
        auto ei = dir.exponents.find(v);
        if (ei != dir.exponents.end()) a = ei->second;
        int s = 1;
        auto si = dir.signs.find(v);
        if (si != dir.signs.end()) s = si->second;

        const mpz_class aAbs = abs(a);
        mpz_class mag;
        mpz_pow_ui(mag.get_mpz_t(), bz.get_mpz_t(), mpz_get_ui(aAbs.get_mpz_t()));
        mpq_class val(mag);
        if (sgn(a) < 0) val = mpq_class(1) / val;
        if (s < 0) val = -val;
        val.canonicalize();
        model[v] = val;
    }
    return model;
}

} // namespace xolver
