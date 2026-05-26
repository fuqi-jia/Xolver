// ZOLVER_PP_PG_CNF: Plaisted-Greenbaum polarity-aware CNF.
//
// A polarity bug in PG-CNF can only DROP a defining clause, which relaxes the
// encoding and can only turn an unsat formula spuriously sat (never the
// reverse). So we validate against GROUND TRUTH: for random boolean formulas,
// the atomized SAT instance must be satisfiable iff the formula is truly
// satisfiable (brute-forced over all assignments) — for BOTH pg-off and pg-on.
// If the two ever disagree with the oracle, PG is unsound.
#include <doctest/doctest.h>
#include "frontend/atomization/Atomizer.h"
#include "sat/SatSolver.h"
#include "expr/ir.h"
#include <random>
#include <vector>
#include <string>
#include <functional>

using namespace zolver;

namespace {

struct BoolHarness {
    CoreIr ir;
    SortId boolS;
    std::vector<std::string> vars;
    std::vector<ExprId> varIds;

    explicit BoolHarness(int nvars) {
        boolS = ir.allocateSortId();
        ir.registerSort(boolS, SortKind::Bool);
        ir.setBoolSortId(boolS);
        for (int i = 0; i < nvars; ++i) {
            vars.push_back(std::string(1, char('a' + i)));
            varIds.push_back(mk(Kind::Variable, {}, Payload(vars.back())));
        }
    }
    ExprId mk(Kind k, std::vector<ExprId> ch, Payload p = Payload()) {
        CoreExpr e; e.kind = k; e.sort = boolS;
        e.children = SmallVector<ExprId, 4>(ch.begin(), ch.end());
        e.payload = std::move(p);
        return ir.add(std::move(e));
    }
};

// Brute-force truth value of `id` under a bitmask assignment (bit i = var i).
bool evalBool(const CoreIr& ir, ExprId id, unsigned mask,
              const std::vector<std::string>& vars) {
    const CoreExpr& e = ir.get(id);
    switch (e.kind) {
        case Kind::ConstBool: return std::get<bool>(e.payload.value);
        case Kind::Variable: {
            const std::string& n = std::get<std::string>(e.payload.value);
            for (size_t i = 0; i < vars.size(); ++i)
                if (vars[i] == n) return (mask >> i) & 1u;
            return false;
        }
        case Kind::Not: return !evalBool(ir, e.children[0], mask, vars);
        case Kind::And:
            for (ExprId c : e.children) if (!evalBool(ir, c, mask, vars)) return false;
            return true;
        case Kind::Or:
            for (ExprId c : e.children) if (evalBool(ir, c, mask, vars)) return true;
            return false;
        case Kind::Implies:
            return !evalBool(ir, e.children[0], mask, vars) ||
                    evalBool(ir, e.children[1], mask, vars);
        case Kind::Xor:
            return evalBool(ir, e.children[0], mask, vars) !=
                   evalBool(ir, e.children[1], mask, vars);
        default: return false;  // generator produces nothing else
    }
}

bool bruteSatisfiable(const CoreIr& ir, ExprId root,
                      const std::vector<std::string>& vars) {
    for (unsigned m = 0; m < (1u << vars.size()); ++m)
        if (evalBool(ir, root, m, vars)) return true;
    return false;
}

// Minimal counting SatSolver: tallies clauses/vars without solving. Used to
// prove PG actually REDUCES clause count (so the flag is not a silent no-op).
struct CountingSat : SatSolver {
    int clauses = 0;
    SatVar nv = 0;
    SatVar newVar() override { return ++nv; }
    void addClause(const std::vector<SatLit>&) override { ++clauses; }
    SolveResult solve() override { return SolveResult::Unknown; }
    SolveResult solve(const std::vector<SatLit>&) override { return SolveResult::Unknown; }
    bool value(SatVar) const override { return false; }
};

int countClauses(CoreIr& ir, ExprId root, SortId boolS, bool pg) {
    CountingSat sat;
    Atomizer atom(sat);
    atom.setBoolSortId(boolS);
    atom.setPgCnf(pg);
    atom.computePolarities({root}, ir);
    SatLit lit = atom.atomize(root, ir);
    sat.addClause({lit});
    return sat.clauses;
}

// SAT-status of the PG-encoded formula. Fresh SatSolver + Atomizer per call.
bool encodeAndSolveIsSat(CoreIr& ir, ExprId root, SortId boolS, bool pg) {
    auto sat = createSatSolver();
    REQUIRE(sat);
    Atomizer atom(*sat);
    atom.setBoolSortId(boolS);
    atom.setPgCnf(pg);
    atom.computePolarities({root}, ir);
    SatLit lit = atom.atomize(root, ir);
    sat->addClause({lit});
    return sat->solve() == SatSolver::SolveResult::Sat;
}

} // namespace

TEST_CASE("PG-CNF: equisatisfiable with ground truth (random boolean formulas)") {
    // PG cannot lean on the model validator as a backstop (it does not catch
    // QF_UF false-SATs on the default path), so PG must be correct BY ITSELF.
    // This is the primary guarantee: a broad ground-truth differential. The
    // generator deliberately builds a DAG (re-using subexpressions) and n-ary
    // And/Or so subformulas are reached at MULTIPLE polarities — the exact
    // stress for the polarity-union logic that PG relies on.
    std::mt19937 rng(0x9E3779B9);
    const int K = 4;  // a,b,c,d -> brute force over 16 assignments
    int sawSat = 0, sawUnsat = 0, sawShared = 0;

    for (int iter = 0; iter < 2000; ++iter) {
        BoolHarness h(K);
        std::vector<ExprId> pool(h.varIds);  // shareable subexpressions (DAG)

        std::function<ExprId(int)> gen = [&](int d) -> ExprId {
            // ~1/4 of the time, REUSE an existing node -> DAG sharing, so the
            // same subformula occurs under different parents/polarities.
            if (pool.size() > K && rng() % 4 == 0) {
                ++sawShared;
                return pool[rng() % pool.size()];
            }
            ExprId e;
            if (d <= 0 || rng() % 3 == 0) {
                int r = rng() % (K + 2);
                e = (r < K) ? h.varIds[r]
                            : h.mk(Kind::ConstBool, {}, Payload(r == K));
            } else {
                switch (rng() % 5) {
                    case 0: e = h.mk(Kind::Not, {gen(d - 1)}); break;
                    case 1:
                    case 2: {
                        int nc = 2 + static_cast<int>(rng() % 3);  // n-ary 2..4
                        std::vector<ExprId> ch;
                        for (int i = 0; i < nc; ++i) ch.push_back(gen(d - 1));
                        e = h.mk((rng() % 2) ? Kind::And : Kind::Or, ch);
                        break;
                    }
                    case 3: e = h.mk(Kind::Implies, {gen(d - 1), gen(d - 1)}); break;
                    default: e = h.mk(Kind::Xor, {gen(d - 1), gen(d - 1)}); break;
                }
            }
            pool.push_back(e);
            return e;
        };

        ExprId root = gen(4);
        bool truth = bruteSatisfiable(h.ir, root, h.vars);
        truth ? ++sawSat : ++sawUnsat;

        bool off = encodeAndSolveIsSat(h.ir, root, h.boolS, /*pg=*/false);
        bool on  = encodeAndSolveIsSat(h.ir, root, h.boolS, /*pg=*/true);

        // The plain Tseitin encoder is the trusted reference; PG must match it
        // AND both must match the brute-force ground truth.
        CHECK(off == truth);
        CHECK(on == truth);
    }
    // The corpus must exercise both verdicts AND actual DAG sharing, else it is
    // weaker than it looks.
    CHECK(sawSat > 0);
    CHECK(sawUnsat > 0);
    CHECK(sawShared > 0);
}

TEST_CASE("PG-CNF: nested single-polarity contradiction stays unsat") {
    // (and a (not a)) -- the inner And is positive-only; PG must still keep the
    // x->def half that forces both a and !a, so it is unsat under PG too.
    BoolHarness h(1);
    ExprId a = h.varIds[0];
    ExprId root = h.mk(Kind::And, {a, h.mk(Kind::Not, {a})});
    CHECK(encodeAndSolveIsSat(h.ir, root, h.boolS, false) == false);
    CHECK(encodeAndSolveIsSat(h.ir, root, h.boolS, true) == false);
}

TEST_CASE("PG-CNF: reduces clause count on single-polarity structure") {
    // (or a (and b c)) asserted positively: every node is positive-only, so PG
    // drops the unused def->x halves -> strictly fewer clauses than full Tseitin.
    BoolHarness h(3);
    ExprId andBC = h.mk(Kind::And, {h.varIds[1], h.varIds[2]});
    ExprId root = h.mk(Kind::Or, {h.varIds[0], andBC});
    int full = countClauses(h.ir, root, h.boolS, /*pg=*/false);
    int pg   = countClauses(h.ir, root, h.boolS, /*pg=*/true);
    CHECK(pg < full);
}

TEST_CASE("PG-CNF: negated disjunction (neg-polarity Or) stays correct") {
    // (not (or a b)) is sat only at a=b=false. The Or occurs negatively, so PG
    // keeps the def->x half {(x|!a),(x|!b)}; forcing !x then forces !a and !b.
    BoolHarness h(2);
    ExprId orAB = h.mk(Kind::Or, {h.varIds[0], h.varIds[1]});
    ExprId root = h.mk(Kind::Not, {orAB});
    CHECK(encodeAndSolveIsSat(h.ir, root, h.boolS, true) == true);  // a=b=false

    // ...and (and (not (or a b)) a) is unsat: forcing a contradicts !a.
    ExprId conj = h.mk(Kind::And, {root, h.varIds[0]});
    CHECK(encodeAndSolveIsSat(h.ir, conj, h.boolS, true) == false);
}
