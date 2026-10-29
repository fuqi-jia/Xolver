#include "search/nra/reasoners/SubtropicalSatFinder.h"
#include "search/lra/GeneralSimplex.h"

#include <algorithm>
#include <functional>
#include <map>

namespace xolver {

namespace {

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
    const std::vector<VarId>& vars, Statistics* statistics) const {
    Statistics local;
    auto& stats = statistics ? *statistics : local;
    stats = {};
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

    // All frame choices share one exact linear context. Definitions are
    // unconditional; only their >= 1 bounds belong to a choice level. Keeping
    // the basis and assignments across siblings avoids rebuilding/eliminating
    // the same prefix, without retaining a withdrawn branch bound.
    GeneralSimplex simplex;
    ++stats.contexts;
    std::vector<int> columns;
    for (int i = 0; i < n; ++i) columns.push_back(simplex.addVar("direction-" + std::to_string(i)));
    using Row = std::vector<std::pair<int, mpq_class>>;
    std::map<Row, int> definitions;
    const BoundInfo lower(BoundValue(DeltaRational(1)), SatLit::positive(1)); // private
    std::vector<std::pair<std::vector<char>, char>> parityEqs;
    std::vector<mpq_class> witnessA;

    std::function<bool(size_t)> recurse = [&](size_t k) -> bool {
        if (++stats.nodes > cfg_.searchNodeCap) { stats.exhausted = true; return false; }
        if (k == cons.size()) {
            const auto delta = simplex.computeSafeDelta();
            for (const auto column : columns) {
                const auto value = simplex.value(column);
                witnessA.push_back(value.a + value.b * delta);
            }
            return true;
        }
        const Cons& cc = cons[k];
        for (size_t fi = 0; fi < cc.monos.size(); ++fi) {
            ++stats.frames;
            const Mono& f = cc.monos[fi];
            const size_t parityFrom = parityEqs.size();
            if (cc.rel != Relation::Neq) {
                const int reqSign = (cc.rel == Relation::Gt || cc.rel == Relation::Geq) ? 1 : -1;
                const char b = (reqSign * f.csign > 0) ? 0 : 1;
                std::vector<char> row(n, 0);
                for (int i = 0; i < n; ++i) row[i] = static_cast<char>(f.e[i] & 1);
                parityEqs.emplace_back(std::move(row), b);
                if (!gf2Consistent(parityEqs, n)) {
                    ++stats.parityConflicts;
                    parityEqs.resize(parityFrom);
                    continue;
                }
            }
            const int level = static_cast<int>(k) + 1;
            bool feasible = true;
            for (size_t gi = 0; gi < cc.monos.size(); ++gi) {
                if (gi == fi) continue;
                Row row;
                for (int i = 0; i < n; ++i)
                    if (const int coefficient = f.e[i] - cc.monos[gi].e[i])
                        row.emplace_back(columns[i], coefficient);
                if (row.empty()) { feasible = false; break; } // 0 >= 1
                auto it = definitions.find(row);
                if (it == definitions.end()) {
                    if (static_cast<long>(definitions.size()) >= cfg_.linearRowCap) {
                        stats.exhausted = true;
                        feasible = false;
                        break;
                    }
                    const int column = simplex.addConstraint(row, 0);
                    if (column < 0) { feasible = false; break; }
                    it = definitions.emplace(std::move(row), column).first;
                    ++stats.definitions;
                } else ++stats.reusedRows;
                if (!simplex.assertLower(it->second, lower, level)) { feasible = false; break; }
            }
            if (feasible) {
                ++stats.linearChecks;
                const auto result = simplex.check();
                feasible = result == GeneralSimplex::Result::Sat;
                stats.exhausted |= result == GeneralSimplex::Result::Unknown;
            }
            if (feasible && recurse(k + 1)) return true;
            simplex.backtrackToLevel(static_cast<int>(k), GeneralSimplex::AssignmentPolicy::Preserve);
            ++stats.backtracks;
            parityEqs.resize(parityFrom);
            if (stats.exhausted) return false;
        }
        return false;
    };

    if (!recurse(0)) return res; // no candidate, never an UNSAT verdict

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
