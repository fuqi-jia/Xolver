#include "api/SolverImpl.h"
#ifdef XOLVER_ENABLE_PROOFS
#include "proof/AletheProof.h"
#include "proof/BoolClausalProof.h"
#include "proof/TheoryProofSink.h"
#include "sat/SatSolver.h"
#include "expr/Smt2Dumper.h"
#include <gmpxx.h>
#include <fstream>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <set>
#include <tuple>
#include <optional>
#include <algorithm>
#include <cstdio>
#endif

namespace xolver {

#ifdef XOLVER_ENABLE_PROOFS
namespace {
// Is `id` a linear-arithmetic term that la_generic can certify AND that
// dumpExprToSMT2 renders as sort-safe SMT-LIB? Allowed: variables, INTEGER
// constants (bare-integer print, coerced by Carcara in arithmetic), and
// +/-/*/unary-minus. Excluded: division (la_generic treats `(/ x c)` as an opaque
// term, so the Farkas combination can't cancel the variable), NON-integer real
// constants (which print as `1/3` — invalid as an SMT-LIB Real literal), and any
// other / non-linear construct. Conservative: an excluded atom stays SKELETON.
bool proofLinSafe(ExprId id, const CoreIr& ir) {
    const auto& e = ir.get(id);
    switch (e.kind) {
        case Kind::Variable: return true;
        case Kind::ConstInt: return true;
        case Kind::ConstReal: {
            mpq_class q(std::get<std::string>(e.payload.value));
            q.canonicalize();
            return q.get_den() == 1;
        }
        case Kind::Add:
        case Kind::Sub:
        case Kind::Mul:
        case Kind::Neg:
            for (ExprId c : e.children)
                if (!proofLinSafe(c, ir)) return false;
            return true;
        default:
            return false;
    }
}

// --- Independent Farkas verifier (for signed-multiplier equality certs) ------
// A rational linear form over IR variables: sum of (var -> coeff) plus a constant.
struct LinForm {
    std::map<ExprId, mpq_class> v;
    mpq_class k;
};

// Accumulate `scale * <linear term id>` into `out`; false if non-linear/unsupported.
bool proofLinForm(ExprId id, const CoreIr& ir, const mpq_class& scale, LinForm& out) {
    const auto& e = ir.get(id);
    switch (e.kind) {
        case Kind::Variable: out.v[id] += scale; return true;
        case Kind::ConstInt:
            out.k += scale * mpq_class(std::get<int64_t>(e.payload.value));
            return true;
        case Kind::ConstReal: {
            mpq_class q(std::get<std::string>(e.payload.value));
            q.canonicalize();
            out.k += scale * q;
            return true;
        }
        case Kind::Add:
            for (ExprId c : e.children)
                if (!proofLinForm(c, ir, scale, out)) return false;
            return true;
        case Kind::Sub: {
            if (e.children.empty()) return false;
            if (!proofLinForm(e.children[0], ir, scale, out)) return false;
            for (size_t i = 1; i < e.children.size(); ++i)
                if (!proofLinForm(e.children[i], ir, -scale, out)) return false;
            return true;
        }
        case Kind::Neg:
            for (ExprId c : e.children)
                if (!proofLinForm(c, ir, -scale, out)) return false;
            return true;
        case Kind::Mul: {
            // Linear only: at most one non-constant factor; fold the constant ones.
            mpq_class coef = scale;
            ExprId nonConst = NullExpr;
            for (ExprId c : e.children) {
                LinForm cf;
                if (!proofLinForm(c, ir, 1, cf)) return false;
                if (cf.v.empty()) coef *= cf.k;
                else if (nonConst == NullExpr) nonConst = c;
                else return false;  // two variable factors -> nonlinear
            }
            if (nonConst == NullExpr) { out.k += coef; return true; }
            return proofLinForm(nonConst, ir, coef, out);
        }
        default:
            return false;
    }
}

// An atom's left-hand form in Carcara's la_generic `>= 0` convention, plus flags.
struct AtomForm { LinForm ni; bool strict = false; bool isEq = false; };

// Build the >=0-form of an arithmetic atom: a<=b / a<b -> (b-a); a>=b / a>b ->
// (a-b); a=b -> (a-b) (sign-free). Mirrors la_generic's internal normalization so
// a verified non-negative combination is exactly one Carcara accepts.
bool proofAtomForm(ExprId atomId, const CoreIr& ir, AtomForm& out) {
    const auto& e = ir.get(atomId);
    if (e.children.size() != 2) return false;
    ExprId a = e.children[0], b = e.children[1];
    out = {};
    switch (e.kind) {
        case Kind::Leq: case Kind::Lt:
            if (!proofLinForm(b, ir, 1, out.ni) || !proofLinForm(a, ir, -1, out.ni)) return false;
            out.strict = (e.kind == Kind::Lt);
            return true;
        case Kind::Geq: case Kind::Gt:
            if (!proofLinForm(a, ir, 1, out.ni) || !proofLinForm(b, ir, -1, out.ni)) return false;
            out.strict = (e.kind == Kind::Gt);
            return true;
        case Kind::Eq:
            if (!proofLinForm(a, ir, 1, out.ni) || !proofLinForm(b, ir, -1, out.ni)) return false;
            out.isEq = true;
            return true;
        default:
            return false;
    }
}

// True iff sum_i coeff_i * atom_i.ni cancels every variable and the residual
// constant K refutes the combined relation (K < 0, or K <= 0 if a strict atom
// participates). Inequality coeffs must be >= 0; equality coeffs are sign-free.
bool proofFarkasContradicts(const std::vector<AtomForm>& atoms,
                            const std::vector<mpq_class>& coeffs) {
    LinForm sum;
    bool anyStrict = false;
    for (size_t i = 0; i < atoms.size(); ++i) {
        const mpq_class& s = coeffs[i];
        for (const auto& [var, c] : atoms[i].ni.v) sum.v[var] += s * c;
        sum.k += s * atoms[i].ni.k;
        if (atoms[i].strict && s != 0) anyStrict = true;
    }
    for (auto& [var, c] : sum.v) { c.canonicalize(); if (c != 0) return false; }
    sum.k.canonicalize();
    return anyStrict ? (sum.k <= 0) : (sum.k < 0);
}

// For an eq_transitive cert: every literal must be a TOP-LEVEL Eq atom; exactly
// ONE is negative (the conclusion disequality) and the rest positive (the asserted
// chain equalities); and the chain must TRANSITIVELY CONNECT the conclusion's two
// terms. The last is an independent union-find over the asserted equalities — it
// confirms a pure transitivity conflict and rejects any congruence-involved one
// (where the equalities don't directly connect the endpoints), for which
// eq_transitive would be wrong. Sound by construction; Carcara is the final gate.
bool proofEufTransitivityOk(const std::vector<std::pair<ExprId, bool>>& lits,
                            const CoreIr& ir,
                            const std::unordered_set<ExprId>& posAssert,
                            const std::unordered_set<ExprId>& negAssert) {
    std::unordered_map<ExprId, ExprId> parent;
    auto find = [&](ExprId x) {
        while (parent.count(x) && parent[x] != x) x = parent[x];
        parent[x] = x;
        return x;
    };
    ExprId concL = NullExpr, concR = NullExpr;
    int neg = 0;
    for (const auto& [atomId, positive] : lits) {
        // assume-validity: a positive literal asserts `atom` (must be a top-level
        // assertion); a negative literal asserts `(not atom)` (the negation must be
        // a top-level assertion — for a disequality, the asserted (not (= l r)) or
        // the asserted binary (distinct l r)).
        if (positive ? !posAssert.count(atomId) : !negAssert.count(atomId)) return false;
        const auto& e = ir.get(atomId);
        const bool isEq = (e.kind == Kind::Eq && e.children.size() == 2);
        const bool isDistinct = (e.kind == Kind::Distinct && e.children.size() == 2);
        if (!isEq && !isDistinct) return false;
        // A positive Eq (or a negated binary Distinct) asserts l = r — a chain edge.
        // A negated Eq (or a positive binary Distinct) asserts l != r — the single
        // conclusion. Binary `distinct` is exactly `(not (= ))`, so it flips the
        // polarity meaning relative to Eq.
        const bool assertsEquality = isEq ? positive : !positive;
        if (assertsEquality) {
            parent[find(e.children[0])] = find(e.children[1]);
        } else {
            if (++neg > 1) return false;
            concL = e.children[0];
            concR = e.children[1];
        }
    }
    // concL == concR is a self-disequality (distinct a a): a 1-edge "chain" that
    // eq_transitive can't express. Reject here so it falls through to the congruence
    // path, where the refl rule discharges it.
    return neg == 1 && concL != NullExpr && concL != concR && find(concL) == find(concR);
}

// --- Phase F1: pure-propositional (flat-clausal) Boolean-assembly proof --------
// When an UNSAT instance has NO theory atoms — every assertion is a Boolean
// literal or a flat disjunction of literals — the refutation is purely
// propositional. Build a flat CNF directly from the assertions (one clause each,
// NO Tseitin proxy variables), refute it with a dedicated SAT solve that captures
// the LRAT resolution chain, and translate that LRAT into a single Alethe proof
// (clausify via `or` + replay resolution). The proof is checked by Carcara
// against the IR-derived problem (the same assertions). Returns nullopt — degrade
// to the DRAT path — if any assertion is not flat-clausal, the flat CNF does not
// refute (it must, but we never assume), or the LRAT does not translate cleanly.
std::optional<proof::AletheProof>
tryFlatClausalBooleanProof(const CoreIr& ir, const std::vector<ExprId>& assertions) {
    if (assertions.empty()) return std::nullopt;
    const SortId boolSort = ir.boolSortId();

    std::unordered_map<ExprId, int> varOf;     // bool-var ExprId -> SAT var (1-based)
    std::vector<ExprId> varExpr;               // varExpr[v] = the bool var's ExprId
    varExpr.push_back(NullExpr);               // index 0 unused (vars are 1-based)

    auto isBoolVar = [&](ExprId id) {
        const auto& e = ir.get(id);
        if (e.kind != Kind::Variable ||
            !std::holds_alternative<std::string>(e.payload.value))
            return false;
        // A declared Bool variable can carry an unregistered SortId, so accept
        // both the canonical bool sort and any sort whose kind resolves to Bool.
        if (e.sort == boolSort) return true;
        auto sk = ir.sortKind(e.sort);
        return sk && *sk == SortKind::Bool;
    };
    // Map a clause-literal expr to a signed SAT int, registering its variable.
    auto litOf = [&](ExprId id) -> std::optional<int> {
        bool neg = false;
        const auto* e = &ir.get(id);
        if (e->kind == Kind::Not && e->children.size() == 1) {
            neg = true;
            id = e->children[0];
            e = &ir.get(id);
        }
        if (!isBoolVar(id)) return std::nullopt;
        auto it = varOf.find(id);
        int v;
        if (it == varOf.end()) {
            v = static_cast<int>(varExpr.size());
            varOf[id] = v;
            varExpr.push_back(id);
        } else {
            v = it->second;
        }
        return neg ? -v : v;
    };

    std::vector<proof::ClausalAssertion> clausal;
    std::vector<std::vector<int>> cnf;
    clausal.reserve(assertions.size());
    cnf.reserve(assertions.size());

    for (ExprId a : assertions) {
        const auto& e = ir.get(a);
        proof::ClausalAssertion ca;
        ca.smtText = dumpExprToSMT2(a, ir);
        std::vector<int> lits;
        if (e.kind == Kind::Or) {
            if (e.children.empty()) return std::nullopt;
            for (ExprId c : e.children) {
                auto l = litOf(c);
                if (!l) return std::nullopt;
                lits.push_back(*l);
                ca.clauseTerms.push_back(dumpExprToSMT2(c, ir));
            }
            // An `(or ...)` ALWAYS clausifies via the `or` rule (even a 1-disjunct
            // `(or p)`): the assume term is the disjunction, not the bare literal,
            // so resolution needs the extracted `(cl p)`, never `(cl (or p))`.
            ca.isUnit = false;
        } else {
            // A bare literal assertion: a Bool variable or its negation.
            auto l = litOf(a);
            if (!l) return std::nullopt;
            lits.push_back(*l);
            ca.clauseTerms.push_back(ca.smtText);
            ca.isUnit = true;
        }
        clausal.push_back(std::move(ca));
        cnf.push_back(std::move(lits));
    }

    const int numVars = static_cast<int>(varExpr.size()) - 1;
    if (numVars <= 0) return std::nullopt;

    // Refute the flat CNF on a dedicated SAT solve with LRAT capture. This never
    // touches the main solve; a wrong result only causes a degrade, never a proof.
    auto sat = createSatSolver();
    if (!sat->enableLratCapture()) return std::nullopt;
    for (int i = 0; i < numVars; ++i) (void)sat->newVar();   // declare vars 1..k
    for (const auto& clause : cnf) {
        std::vector<SatLit> sc;
        sc.reserve(clause.size());
        for (int l : clause)
            sc.push_back(SatLit{static_cast<SatVar>(l < 0 ? -l : l), l > 0});
        sat->addClause(sc);
    }
    if (sat->solve() != SatSolver::SolveResult::Unsat) return std::nullopt;

    std::vector<LratClause> lrat;
    if (!sat->getLratProof(lrat)) return std::nullopt;

    std::vector<proof::LratStep> steps;
    steps.reserve(lrat.size());
    for (const auto& c : lrat)
        steps.push_back(proof::LratStep{c.original, c.id, c.lits, c.chain});

    std::vector<std::string> varTerm(varExpr.size());
    for (size_t v = 1; v < varExpr.size(); ++v)
        varTerm[v] = dumpExprToSMT2(varExpr[v], ir);

    return proof::buildClausalRefutation(clausal, steps, varTerm);
}

// Return the single DISTINCT conflict cert, or nullptr if the sink holds zero or
// >=2 distinct conflicts. A theory may re-derive the same conflict several times
// during search (e.g. EUF saturation / SAT re-check), so identical certs collapse
// to one — that single conflict alone refutes the asserted literals. Two genuinely
// different conflicts need Boolean assembly (later) and stay skeleton.
const proof::TheoryConflictCert*
proofUniqueConflict(const std::vector<proof::TheoryConflictCert>& cs) {
    if (cs.empty()) return nullptr;
    auto same = [](const proof::TheoryConflictCert& a, const proof::TheoryConflictCert& b) {
        if (a.rule != b.rule || a.lits.size() != b.lits.size()) return false;
        for (const auto& la : a.lits) {
            bool f = false;
            for (const auto& lb : b.lits) if (la == lb) { f = true; break; }
            if (!f) return false;
        }
        return true;
    };
    for (size_t i = 1; i < cs.size(); ++i)
        if (!same(cs[0], cs[i])) return nullptr;
    return &cs[0];
}

// Collect the DISTINCT conflict certs (one representative per equivalence class
// under the same order-insensitive `same` predicate proofUniqueConflict uses). A
// theory re-derives the same conflict many times during search; F2b feeds each
// distinct conflict as one lemma clause, so identical certs must collapse to one
// (duplicate input clauses would otherwise mis-align the LRAT feed-order replay).
std::vector<const proof::TheoryConflictCert*>
proofDistinctConflicts(const std::vector<proof::TheoryConflictCert>& cs) {
    auto same = [](const proof::TheoryConflictCert& a, const proof::TheoryConflictCert& b) {
        if (a.rule != b.rule || a.lits.size() != b.lits.size()) return false;
        for (const auto& la : a.lits) {
            bool f = false;
            for (const auto& lb : b.lits) if (la == lb) { f = true; break; }
            if (!f) return false;
        }
        return true;
    };
    std::vector<const proof::TheoryConflictCert*> out;
    for (const auto& c : cs) {
        bool dup = false;
        for (const auto* o : out) if (same(*o, c)) { dup = true; break; }
        if (!dup) out.push_back(&c);
    }
    return out;
}

// --- EUF congruence proof reconstruction -----------------------------------
// Reconstruct a Carcara-checkable proof that lhs = rhs from the asserted LEAF
// equalities, via eq_transitive over a leaf chain and eq_congruent over function
// arguments, then resolve with the asserted disequality lhs != rhs to the empty
// clause. INDEPENDENT of the e-graph's internal justification: we trust only the
// leaf equalities + the IR term structure, and Carcara is the final gate — a
// reconstruction that doesn't actually entail the equality fails to resolve and
// is rejected offline, never claimed. Each emitted clause literal is written in
// its sub-proof's own orientation (eq_congruent/eq_transitive tolerate flipped
// argument equalities), so the orientation-sensitive final resolution cancels.
struct EufCongruenceProver {
    const CoreIr& ir;
    proof::AletheProof& p;
    std::map<std::pair<ExprId, ExprId>, std::pair<std::string, std::string>> leaf; // key -> (assumeId, atom)
    std::unordered_map<ExprId, std::vector<ExprId>> adj;   // leaf-equality graph
    std::map<std::pair<ExprId, ExprId>, std::string> memo; // proven pair -> produced literal
    std::vector<std::string> premises;                     // used assume/step ids (unique, ordered)
    std::unordered_set<std::string> premiseSet;

    // --- Phase F2a lemma mode -------------------------------------------------
    // In lemmaMode the prover does NOT assume the leaf equalities (they come from
    // the clausified original assertions and are resolved away by the propositional
    // replay); instead it RECORDS every tautology step it emits — the lemma clauses
    // (cl (not leaf_i)... (= u v)) over theory atoms — so the caller can feed them
    // as input clauses to the abstraction's SAT solve and map each LRAT id back to
    // its step. The closed-proof callers (proofEufCongruence/proofBoolCongruence)
    // leave lemmaMode false and the behaviour is byte-identical to before.
    bool lemmaMode = false;
    struct EmittedLemmaStep {
        std::string id;                                  // the Alethe step id
        std::vector<std::pair<std::string, bool>> lits;  // (atom, positive-in-clause)
    };
    std::vector<EmittedLemmaStep> lemmaSteps;

    static std::pair<ExprId, ExprId> key(ExprId a, ExprId b) {
        return a < b ? std::make_pair(a, b) : std::make_pair(b, a);
    }
    void use(const std::string& id) {
        if (premiseSet.insert(id).second) premises.push_back(id);
    }
    std::string term(ExprId id) const { return dumpExprToSMT2(id, ir); }

    // Add CONGRUENCE edges to `adj` so the transitivity BFS can route through
    // equalities that hold by congruence, not just directly-asserted leaves (e.g.
    // u = f(a,b), v = f(a,c), b = c ⊢ u = v passes through f(a,b) = f(a,c)). A small
    // congruence-closure fixpoint over the terms reachable from the leaves and the
    // conclusion: two same-function applications with already-connected arguments
    // become a new edge; prove() later discharges each via eq_congruent. Bounded by
    // the finite term set; any cycle is harmless (prove() memoizes + caps depth).
    void augmentCongruenceEdges(ExprId lhsId, ExprId rhsId) {
        std::unordered_map<ExprId, ExprId> parent;
        std::vector<ExprId> apps;
        std::vector<ExprId> stack{lhsId, rhsId};
        for (const auto& [k, v] : leaf) { (void)v; stack.push_back(k.first); stack.push_back(k.second); }
        std::unordered_set<ExprId> seen;
        while (!stack.empty()) {
            ExprId x = stack.back();
            stack.pop_back();
            if (x == NullExpr || x >= ir.size() || !seen.insert(x).second) continue;
            parent[x] = x;
            const auto& e = ir.get(x);
            if (e.kind == Kind::UFApply && !e.children.empty()) apps.push_back(x);
            for (ExprId c : e.children) stack.push_back(c);
        }
        auto find = [&](ExprId x) { while (parent[x] != x) x = parent[x]; return x; };
        auto uni = [&](ExprId a, ExprId b) { parent[find(a)] = find(b); };
        for (const auto& [k, v] : leaf) { (void)v; uni(k.first, k.second); }
        bool changed = true;
        while (changed) {
            changed = false;
            for (size_t i = 0; i < apps.size(); ++i) {
                const auto& ei = ir.get(apps[i]);
                for (size_t j = i + 1; j < apps.size(); ++j) {
                    if (find(apps[i]) == find(apps[j])) continue;
                    const auto& ej = ir.get(apps[j]);
                    if (ei.children.size() != ej.children.size() ||
                        std::get<std::string>(ei.payload.value) !=
                            std::get<std::string>(ej.payload.value)) continue;
                    bool allEq = true;
                    for (size_t a = 0; a < ei.children.size(); ++a)
                        if (find(ei.children[a]) != find(ej.children[a])) { allEq = false; break; }
                    if (!allEq) continue;
                    uni(apps[i], apps[j]);
                    adj[apps[i]].push_back(apps[j]);
                    adj[apps[j]].push_back(apps[i]);
                    changed = true;
                }
            }
        }
    }

    // Shortest leaf-equality-graph path s..t (inclusive); empty if unconnected.
    std::vector<ExprId> bfsPath(ExprId s, ExprId t) {
        std::unordered_map<ExprId, ExprId> prev;
        std::unordered_set<ExprId> seen{s};
        std::vector<ExprId> q{s};
        for (size_t h = 0; h < q.size(); ++h) {
            ExprId x = q[h];
            if (x == t) break;
            auto it = adj.find(x);
            if (it == adj.end()) continue;
            for (ExprId y : it->second)
                if (seen.insert(y).second) { prev[y] = x; q.push_back(y); }
        }
        if (!seen.count(t)) return {};
        std::vector<ExprId> path{t};
        while (path.back() != s) path.push_back(prev[path.back()]);
        std::reverse(path.begin(), path.end());
        return path;
    }

    // Establish (= u v) (as a positive unit producible from the recorded premises),
    // returning the exact literal string produced, or "" if outside the fragment.
    std::string prove(ExprId u, ExprId v, int depth) {
        // Termination backstop: a sound proof never needs to recurse deeper than the
        // number of distinct terms (memoization proves each pair once). Bounds any
        // pathological recursion from the augmented graph; degrades to skeleton, never
        // unsound.
        if (depth > static_cast<int>(ir.size())) return "";
        auto k = key(u, v);
        if (auto it = memo.find(k); it != memo.end()) return it->second;
        // (refl) identical terms — e.g. a self-disequality (distinct a a) or a
        // congruence whose argument position is syntactically the same term.
        if (u == v) {
            std::string concl = "(= " + term(u) + " " + term(u) + ")";
            std::string sid = p.step({concl}, "refl");
            if (lemmaMode) lemmaSteps.push_back({sid, {{concl, true}}});
            else use(sid);
            return memo[k] = concl;
        }
        // (a) directly-asserted leaf equality. In lemmaMode the leaf is NOT a
        // premise (it is referenced as `(not leaf)` in the enclosing congruence/
        // transitivity clause and supplied by the clausified original).
        if (auto it = leaf.find(k); it != leaf.end()) {
            if (!lemmaMode) use(it->second.first);
            return memo[k] = it->second.second;
        }
        // (b) congruence: f(A) vs f(B), same function symbol and arity.
        const auto& eu = ir.get(u);
        const auto& ev = ir.get(v);
        if (eu.kind == Kind::UFApply && ev.kind == Kind::UFApply &&
            !eu.children.empty() && eu.children.size() == ev.children.size() &&
            std::get<std::string>(eu.payload.value) ==
                std::get<std::string>(ev.payload.value)) {
            std::vector<std::string> clause;
            std::vector<std::pair<std::string, bool>> lits;
            bool ok = true;
            for (size_t i = 0; i < eu.children.size(); ++i) {
                std::string li = prove(eu.children[i], ev.children[i], depth + 1);
                if (li.empty()) { ok = false; break; }
                clause.push_back("(not " + li + ")");
                lits.push_back({li, false});
            }
            if (ok) {
                std::string concl = "(= " + term(u) + " " + term(v) + ")";
                clause.push_back(concl);
                lits.push_back({concl, true});
                std::string sid = p.step(clause, "eq_congruent");
                if (lemmaMode) lemmaSteps.push_back({sid, lits});
                else use(sid);
                return memo[k] = concl;
            }
        }
        // (c) transitivity over a >=2-edge leaf chain (1 edge is case (a)).
        std::vector<ExprId> path = bfsPath(u, v);
        if (path.size() >= 3) {
            std::vector<std::string> clause;
            std::vector<std::pair<std::string, bool>> lits;
            bool ok = true;
            for (size_t i = 0; i + 1 < path.size(); ++i) {
                std::string li = prove(path[i], path[i + 1], depth + 1);
                if (li.empty()) { ok = false; break; }
                clause.push_back("(not " + li + ")");
                lits.push_back({li, false});
            }
            if (ok) {
                std::string concl = "(= " + term(u) + " " + term(v) + ")";
                clause.push_back(concl);
                lits.push_back({concl, true});
                std::string sid = p.step(clause, "eq_transitive");
                if (lemmaMode) lemmaSteps.push_back({sid, lits});
                else use(sid);
                return memo[k] = concl;
            }
        }
        return "";
    }
};

// Try to build a congruence/transitivity refutation into `out`. leafEqs are the
// positively-asserted (= u v) atoms (uId, vId, asserted-atom-string); lhsId/rhsId
// + diseqAssume are the asserted disequality. Returns true on success (out filled
// with a complete refutation); false leaves `out` to be discarded (-> skeleton).
bool proofEufCongruence(ExprId lhsId, ExprId rhsId,
                        const std::vector<std::tuple<ExprId, ExprId, std::string>>& leafEqs,
                        const std::string& diseqAssume,
                        const CoreIr& ir, proof::AletheProof& out) {
    EufCongruenceProver cp{ir, out, {}, {}, {}, {}, {}};
    for (const auto& [u, v, atom] : leafEqs) {
        std::string id = out.assume(atom);
        cp.leaf[EufCongruenceProver::key(u, v)] = {id, atom};
        cp.adj[u].push_back(v);
        cp.adj[v].push_back(u);
    }
    std::string diseqId = out.assume(diseqAssume);
    cp.augmentCongruenceEdges(lhsId, rhsId);
    if (cp.prove(lhsId, rhsId, 0).empty()) return false;
    std::vector<std::string> resPrem = cp.premises;
    resPrem.push_back(diseqId);
    out.step(/*clause=*/{}, "resolution", resPrem);
    return true;
}

// Boolean-assembly increment 1: a predicate/Boolean congruence conflict. A
// Bool-valued application is asserted TRUE (predTrueId, atom predTrueAtom) and a
// congruent one asserted FALSE (predFalseId, atom predFalseAtom); they are equal
// by congruence over the asserted leaf equalities. Reconstruct:
//   (= predTrue predFalse)         — congruence/transitivity over the leaves,
//   equiv1 -> (cl (not predTrue) predFalse),
//   resolve with the predicate assumes (predTrue, (not predFalse)) -> (cl).
// Mirrors the de-risked, Carcara-valid euf_003 shape. INDEPENDENT of the e-graph
// (trusts only the leaf equalities + IR structure); Carcara is the final gate.
bool proofBoolCongruence(ExprId predTrueId, ExprId predFalseId,
                         const std::vector<std::tuple<ExprId, ExprId, std::string>>& leafEqs,
                         const std::string& predTrueAtom,
                         const std::string& predFalseAtom,
                         const CoreIr& ir, proof::AletheProof& out) {
    EufCongruenceProver cp{ir, out, {}, {}, {}, {}, {}};
    for (const auto& [u, v, atom] : leafEqs) {
        std::string id = out.assume(atom);
        cp.leaf[EufCongruenceProver::key(u, v)] = {id, atom};
        cp.adj[u].push_back(v);
        cp.adj[v].push_back(u);
    }
    std::string hTrue = out.assume(predTrueAtom);                    // (f a)
    std::string hFalse = out.assume("(not " + predFalseAtom + ")");  // (not (f b))
    cp.augmentCongruenceEdges(predTrueId, predFalseId);
    // Prove (= predTrue predFalse) in the passed orientation (so equiv1 cancels
    // with the predicate assumes).
    std::string eqLit = cp.prove(predTrueId, predFalseId, 0);
    if (eqLit.empty()) return false;
    // Collapse the congruence premises into the unit equality, then equiv1.
    std::string eqUnit = out.step({eqLit}, "resolution", cp.premises);
    std::string eqv = out.step({"(not " + predTrueAtom + ")", predFalseAtom},
                               "equiv1", {eqUnit});
    out.step(/*clause=*/{}, "resolution", {eqv, hTrue, hFalse});
    return true;
}

// --- Phase F2a/F2b: theory-lemma Boolean assembly ---------------------------
// Generalizes the F1 flat-clausal path to a theory UNSAT whose refutation needs
// one OR MORE theory lemmas (the canonical case: an EUF congruence whose
// conclusion disequality is buried in a top-level n-ary `(distinct ...)` or an
// `(and ...)`, so it is NOT a top-level assertion the closed-proof path can
// assume). Mechanism:
//   1. Abstract each theory atom of the ORIGINAL (pre-purification) assertions to
//      one propositional variable (rendered via dumpExprToSMT2 — the abstraction's
//      "variables" ARE the real atoms in the Alethe proof).
//   2. Clausify the originals: n-ary distinct -> `distinct_elim` + `equiv1` +
//      resolution + `and :args(k)`; `(and ..)` -> `and :args(k)`; `(or ..)` ->
//      `or`; binary distinct / negated atom / bare atom -> the assume IS the unit.
//   3. For EACH distinct conflict cert, derive its theory tautology clause
//      (cl (not leaf_i).. (= l r)) as a REAL sub-proof (eq_congruent /
//      eq_transitive over the leaves, lemma mode — leaves come from the clausified
//      original, not assumed). A conflict that is a DIRECT leaf vs its negation
//      (euf_016: `(= c a)` and `(not (= c a))`) yields NO lemma step — the
//      clausified original already contains the contradicting unit clauses — so it
//      simply contributes no lemma clause. Duplicate lemma clauses are fed once.
//   4. Refute (clausified-original + all lemma clauses) on a dedicated CaDiCaL LRAT
//      solve and replay the resolution to the empty clause.
// Returns nullopt -> degrade to the DRAT/skeleton path -> when any assertion shape
// is unsupported, or the abstraction is not propositionally unsat with the captured
// conflict lemmas (the conflict set is insufficient — would need CEGAR, out of
// scope). Carcara is the final gate: a wrong assembly is REJECTED offline, never
// claimed.
std::optional<proof::AletheProof>
tryTheoryLemmaBooleanProof(const CoreIr& ir,
                           const std::vector<ExprId>& originalAssertions,
                           const std::vector<const proof::TheoryConflictCert*>& certs) {
    if (certs.empty()) return std::nullopt;
    if (originalAssertions.empty()) return std::nullopt;

    proof::AletheProof proof;
    auto term = [&](ExprId id) { return dumpExprToSMT2(id, ir); };

    // Atom abstraction: each distinct rendered atom string -> a 1-based SAT var.
    std::unordered_map<std::string, int> atomVar;
    std::vector<std::string> varTerm;
    varTerm.push_back("");  // index 0 unused (vars are 1-based)
    auto reg = [&](const std::string& atom) -> int {
        auto it = atomVar.find(atom);
        if (it != atomVar.end()) return it->second;
        int v = static_cast<int>(varTerm.size());
        atomVar[atom] = v;
        varTerm.push_back(atom);
        return v;
    };
    // A clause literal: the underlying atom (a positive equality / comparison /
    // bool atom) plus its sign. A binary `(distinct x y)` is a negated equality;
    // logical connectives are not abstractable literals (-> nullopt -> degrade).
    auto litFromExpr = [&](ExprId id) -> std::optional<std::pair<std::string, bool>> {
        bool pos = true;
        const auto* e = &ir.get(id);
        while (e->kind == Kind::Not && e->children.size() == 1) {
            pos = !pos; id = e->children[0]; e = &ir.get(id);
        }
        if (e->kind == Kind::Distinct && e->children.size() == 2)
            return std::make_pair("(= " + term(e->children[0]) + " " + term(e->children[1]) + ")", !pos);
        switch (e->kind) {
            case Kind::And: case Kind::Or: case Kind::Implies:
            case Kind::Xor: case Kind::Ite: case Kind::Distinct:
                return std::nullopt;
            default: break;
        }
        return std::make_pair(term(id), pos);
    };

    std::vector<std::vector<int>> cnf;
    std::vector<std::string> origStepId;  // feed-order Alethe step per input clause

    // Assume each original assertion up front (Carcara expects assumes first).
    std::vector<std::string> assumeId;
    assumeId.reserve(originalAssertions.size());
    for (ExprId a : originalAssertions) assumeId.push_back(proof.assume(term(a)));

    // Clausify each original assertion into propositional clauses + the Alethe
    // step that proves each clause's (cl ...).
    for (size_t ai = 0; ai < originalAssertions.size(); ++ai) {
        ExprId a = originalAssertions[ai];
        const std::string& hId = assumeId[ai];
        const auto& e = ir.get(a);
        if (e.kind == Kind::Distinct && e.children.size() >= 3) {
            // n-ary distinct -> the pairwise And via distinct_elim, then `and`.
            std::vector<std::string> pairTerms;       // "(not (= ti tj))" per pair
            std::vector<std::pair<size_t, size_t>> pairs;
            for (size_t i = 0; i < e.children.size(); ++i)
                for (size_t j = i + 1; j < e.children.size(); ++j) {
                    pairTerms.push_back("(not (= " + term(e.children[i]) + " "
                                                   + term(e.children[j]) + "))");
                    pairs.emplace_back(i, j);
                }
            std::string andTerm = "(and";
            for (const auto& pt : pairTerms) andTerm += " " + pt;
            andTerm += ")";
            std::string dren = term(a);  // "(distinct ...)"
            std::string s1 = proof.step({"(= " + dren + " " + andTerm + ")"}, "distinct_elim");
            std::string s2 = proof.step({"(not " + dren + ")", andTerm}, "equiv1", {s1});
            std::string s3 = proof.step({andTerm}, "resolution", {s2, hId});
            for (size_t k = 0; k < pairs.size(); ++k) {
                std::string atom = "(= " + term(e.children[pairs[k].first]) + " "
                                         + term(e.children[pairs[k].second]) + ")";
                int v = reg(atom);
                std::string sc = proof.step({pairTerms[k]}, "and", {s3}, {std::to_string(k)});
                cnf.push_back({-v});
                origStepId.push_back(sc);
            }
        } else if (e.kind == Kind::And) {
            for (size_t k = 0; k < e.children.size(); ++k) {
                auto li = litFromExpr(e.children[k]);
                if (!li) return std::nullopt;
                int v = reg(li->first);
                std::string sc = proof.step({term(e.children[k])}, "and", {hId}, {std::to_string(k)});
                cnf.push_back({li->second ? v : -v});
                origStepId.push_back(sc);
            }
        } else if (e.kind == Kind::Or) {
            if (e.children.empty()) return std::nullopt;
            std::vector<std::string> clauseTerms;
            std::vector<int> lits;
            for (ExprId c : e.children) {
                auto li = litFromExpr(c);
                if (!li) return std::nullopt;
                int v = reg(li->first);
                lits.push_back(li->second ? v : -v);
                clauseTerms.push_back(term(c));
            }
            std::string so = proof.step(clauseTerms, "or", {hId});
            cnf.push_back(lits);
            origStepId.push_back(so);
        } else {
            // Unit: a bare atom, a negation, or a binary distinct — the assume IS
            // the (cl ...) clause.
            auto li = litFromExpr(a);
            if (!li) return std::nullopt;
            int v = reg(li->first);
            cnf.push_back({li->second ? v : -v});
            origStepId.push_back(hId);
        }
    }

    // Dedup clauses by canonical (sorted, unique) literal set: re-derived conflicts
    // yield identical lemma clauses, and a duplicate input clause would mis-align the
    // LRAT feed-order replay (origStepId is indexed 1:1 with the original clauses).
    std::set<std::vector<int>> seenClause;
    auto canon = [](std::vector<int> c) {
        std::sort(c.begin(), c.end());
        c.erase(std::unique(c.begin(), c.end()), c.end());
        return c;
    };
    for (const auto& c : cnf) seenClause.insert(canon(c));

    // Theory lemmas (F2b): for EACH distinct conflict cert, classify its literals
    // into leaf equalities (positive Eq) + the single conclusion disequality
    // (negative Eq, or positive binary Distinct), then derive (cl (not leaf_i)..
    // (= l r)) in lemma mode and feed it as one input clause. A cert we cannot build
    // a sub-proof for (unsupported rule/shape, or outside the EUF fragment) is simply
    // SKIPPED — if it was essential, the propositional-unsat check below fails and we
    // degrade. A DIRECT leaf-vs-negation conflict (euf_016) produces no lemma step;
    // the clausified original already carries the contradiction.
    for (const proof::TheoryConflictCert* certPtr : certs) {
        const auto& cert = *certPtr;
        if (cert.rule != "eq_transitive" || cert.lits.empty()) continue;
        ExprId lhsId = NullExpr, rhsId = NullExpr;
        std::vector<std::tuple<ExprId, ExprId, std::string>> leafEqs;
        int conclusions = 0;
        bool classOk = true;
        for (const auto& [atomId, positive] : cert.lits) {
            const auto& e = ir.get(atomId);
            const bool isEq2 = (e.kind == Kind::Eq && e.children.size() == 2);
            const bool isDist2 = (e.kind == Kind::Distinct && e.children.size() == 2);
            if (isEq2 && positive) {
                leafEqs.emplace_back(e.children[0], e.children[1], term(atomId));
            } else if ((isEq2 && !positive) || (isDist2 && positive)) {
                lhsId = e.children[0]; rhsId = e.children[1]; ++conclusions;
            } else {
                classOk = false; break;
            }
        }
        if (!classOk || conclusions != 1 || lhsId == NullExpr) continue;

        EufCongruenceProver cp{ir, proof, {}, {}, {}, {}, {}};
        cp.lemmaMode = true;
        for (const auto& [u, v, atom] : leafEqs) {
            cp.leaf[EufCongruenceProver::key(u, v)] = {std::string(), atom};
            cp.adj[u].push_back(v);
            cp.adj[v].push_back(u);
        }
        cp.augmentCongruenceEdges(lhsId, rhsId);
        if (cp.prove(lhsId, rhsId, 0).empty()) continue;  // outside fragment -> skip
        for (const auto& ls : cp.lemmaSteps) {
            std::vector<int> lits;
            lits.reserve(ls.lits.size());
            for (const auto& [atom, posInClause] : ls.lits) {
                int v = reg(atom);
                lits.push_back(posInClause ? v : -v);
            }
            if (!seenClause.insert(canon(lits)).second) continue;  // duplicate
            cnf.push_back(std::move(lits));
            origStepId.push_back(ls.id);
        }
    }

    // Refute the abstraction (clausified-original + all lemma clauses) on a dedicated
    // CaDiCaL LRAT solve. Not unsat -> the captured conflict set is insufficient (the
    // refutation needs lemmas not in the sink, e.g. propagation lemmas -> CEGAR, out
    // of scope) -> degrade.
    const int numVars = static_cast<int>(varTerm.size()) - 1;
    if (numVars <= 0) return std::nullopt;
    auto sat = createSatSolver();
    if (!sat->enableLratCapture()) return std::nullopt;
    for (int i = 0; i < numVars; ++i) (void)sat->newVar();
    for (const auto& clause : cnf) {
        std::vector<SatLit> sc;
        sc.reserve(clause.size());
        for (int l : clause)
            sc.push_back(SatLit{static_cast<SatVar>(l < 0 ? -l : l), l > 0});
        sat->addClause(sc);
    }
    if (sat->solve() != SatSolver::SolveResult::Unsat) return std::nullopt;
    std::vector<LratClause> lrat;
    if (!sat->getLratProof(lrat)) return std::nullopt;
    std::vector<proof::LratStep> steps;
    steps.reserve(lrat.size());
    for (const auto& c : lrat)
        steps.push_back(proof::LratStep{c.original, c.id, c.lits, c.chain});

    if (!proof::appendLratResolutionReplay(proof, origStepId, steps, varTerm))
        return std::nullopt;
    return proof;
}
} // namespace
#endif

// ---------------------------------------------------------------------------
// Solver public API
// ---------------------------------------------------------------------------

Solver::Solver() : pImpl(std::make_unique<Impl>()) {
    pImpl->reset();
}

Solver::~Solver() = default;

void Solver::reset() { pImpl->reset(); }

bool Solver::parseFile(std::string_view filename) {
    return pImpl->parseFile(filename);
}

void Solver::push() {
    if (pImpl->ir) pImpl->ir->pushScope();
}

void Solver::pop(uint32_t n) {
    if (pImpl->ir) {
        for (uint32_t i = 0; i < n; ++i) pImpl->ir->popScope();
    }
}

void Solver::setLogic(std::string_view logic) {
    pImpl->logic = std::string(logic);
    // Pre-register the standard sorts so the IR sees a non-NullSort
    // boolSortId/intSortId/realSortId before any user assertion or
    // checkSat() call. Without this, an API-mode user that never calls
    // boolSort()/intSort() explicitly leaves the IR's sort table empty,
    // which downstream (BoolSubtermPurifier, Atomizer, model dump) treat
    // as "Boolean variables not classifiable" — producing empty models
    // and broken get-model behavior. CLI gets these sorts populated as
    // a side effect of SOMTParser; the API never had that bridge.
    // Sound because allocating a sort id is idempotent (getOrCreateXxx
    // returns the cached id on repeat calls).
    pImpl->getOrCreateBoolSort();
    if (logic.find("LIA") != std::string_view::npos ||
        logic.find("NIA") != std::string_view::npos ||
        logic.find("LIRA") != std::string_view::npos ||
        logic.find("NIRA") != std::string_view::npos ||
        logic.find("IDL") != std::string_view::npos ||
        logic.find("DTLIA") != std::string_view::npos ||
        logic.find("DTNIA") != std::string_view::npos ||
        logic.find("ALIA") != std::string_view::npos ||
        logic.find("ANIA") != std::string_view::npos) {
        pImpl->getOrCreateIntSort();
    }
    if (logic.find("LRA") != std::string_view::npos ||
        logic.find("NRA") != std::string_view::npos ||
        logic.find("LIRA") != std::string_view::npos ||
        logic.find("NIRA") != std::string_view::npos ||
        logic.find("RDL") != std::string_view::npos ||
        logic.find("ALRA") != std::string_view::npos) {
        pImpl->getOrCreateRealSort();
    }
}

void Solver::setOption(std::string_view key, OptionValue value) {
    pImpl->options[std::string(key)] = std::move(value);
}

OptionValue Solver::getOption(std::string_view key) const {
    auto it = pImpl->options.find(std::string(key));
    if (it != pImpl->options.end()) return it->second;
    return OptionValue(false);
}

Sort Solver::boolSort() { return Sort{pImpl->getOrCreateBoolSort()}; }
Sort Solver::intSort()  { return Sort{pImpl->getOrCreateIntSort()}; }
Sort Solver::realSort() { return Sort{pImpl->getOrCreateRealSort()}; }
Sort Solver::bvSort(uint32_t) { return Sort{}; /* TODO */ }
Sort Solver::fpSort(uint32_t, uint32_t) { return Sort{}; /* TODO */ }

Term Solver::mkConst(Sort s, std::string_view name) {
    CoreExpr e;
    e.kind = Kind::Variable;
    e.sort = s.id();
    e.payload = Payload(std::string(name));
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkVar(Sort s, std::string_view name) {
    // In CoreIr, variables and constants both use Kind::Variable.
    return mkConst(s, name);
}

Term Solver::mkBool(bool v) {
    CoreExpr e;
    e.kind = Kind::ConstBool;
    e.sort = pImpl->getOrCreateBoolSort();
    e.payload = Payload(v);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkInt(int64_t v) {
    CoreExpr e;
    e.kind = Kind::ConstInt;
    e.sort = pImpl->getOrCreateIntSort();
    e.payload = Payload(v);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkReal(const std::string& rational) {
    CoreExpr e;
    e.kind = Kind::ConstReal;
    e.sort = pImpl->getOrCreateRealSort();
    e.payload = Payload(rational);
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

Term Solver::mkOp(uint32_t kind, std::vector<Term> args) {
    CoreExpr e;
    e.kind = static_cast<Kind>(kind);
    // Simple sort inference: for arithmetic ops, take sort from first arg;
    // for boolean ops (And, Or, etc.), use bool sort;
    // for comparisons (Eq, Lt, etc.), use bool sort.
    if (args.empty()) {
        e.sort = NullSort;
    } else if (e.kind == Kind::And || e.kind == Kind::Or || e.kind == Kind::Not ||
               e.kind == Kind::Implies || e.kind == Kind::Xor ||
               e.kind == Kind::Eq || e.kind == Kind::Distinct ||
               e.kind == Kind::Lt || e.kind == Kind::Leq ||
               e.kind == Kind::Gt || e.kind == Kind::Geq) {
        e.sort = pImpl->getOrCreateBoolSort();
    } else if (e.kind == Kind::Ite && args.size() >= 2) {
        // Ite's sort is the branch sort (then/else), NOT the condition (args[0],
        // which is Bool). Take it from the then-branch.
        e.sort = pImpl->ir ? pImpl->ir->get(args[1].id()).sort : NullSort;
    } else {
        // Use the sort of the first argument if IR is available.
        if (pImpl->ir) {
            e.sort = pImpl->ir->get(args[0].id()).sort;
        } else {
            e.sort = NullSort;
        }
    }
    for (const auto& a : args) {
        e.children.push_back(a.id());
    }
    ExprId id = pImpl->ensureIr().add(e);
    return Term{id};
}

void Solver::assertFormula(Term t) {
    pImpl->ensureIr().addAssertion(t.id());
    // A programmatic assertion would be lost on a portfolio re-parse, so it
    // taints re-parseability: the portfolio executor must stay single-arm.
    pImpl->sourcePath_.clear();
}

void Solver::setPropagator(Propagator* p) {
    if (pImpl) pImpl->userPropagator_ = p;
}

void Solver::clearPropagator() {
    if (pImpl) pImpl->userPropagator_ = nullptr;
}

// #19/#49 native-crash firewall: libpoly / GMP can SIGSEGV / SIGABRT / SIGFPE deep
// in real-algebraic computation on degenerate inputs (a class the C++ try/catch
// below cannot intercept — signals are not exceptions). When enabled, a synchronous
// crash during the solve siglongjmps back and the verdict becomes Unknown (SOUND —
// an incomplete answer, never a wrong one), preserving the process so the
// regression runner / incremental API survive a single bad case instead of dying.
// The signal is synchronous, so it is delivered to the faulting (solve) thread; the
// jmp_buf + active flag are thread_local so the handler resolves to that thread's
// recovery point. Default-OFF: XOLVER_SIGNAL_FIREWALL=1 to enable.
namespace {
thread_local sigjmp_buf g_solveCrashJmp;
thread_local volatile sig_atomic_t g_solveCrashActive = 0;
void solveCrashHandler(int sig) {
    if (g_solveCrashActive) {
        g_solveCrashActive = 0;
        siglongjmp(g_solveCrashJmp, sig);
    }
    // Not inside a guarded solve — restore default disposition and re-raise so a
    // genuine crash outside the firewall is NOT masked.
    std::signal(sig, SIG_DFL);
    std::raise(sig);
}
}  // namespace

Result Solver::checkSat() {
    // Start the global solve wall-clock so per-engine budgets can scale to the
    // time remaining (P0-A). Unset / 0 => no deadline => no behavior change.
    wall::beginSolve(env::paramLong("XOLVER_WALLCLOCK_MS", 0));
    Result r;
    // Non-static: re-read per solve so per-call control works (one getenv/solve is
    // negligible) and so a unit test can toggle the firewall between checkSat calls.
    const bool sigFirewall = env::diag("XOLVER_SIGNAL_FIREWALL");
    struct sigaction oldSegv{}, oldAbrt{}, oldFpe{};
    bool fwInstalled = false;
    if (sigFirewall) {
        if (sigsetjmp(g_solveCrashJmp, 1) != 0) {
            // Recovered from a native crash mid-solve.
            if (fwInstalled) {
                sigaction(SIGSEGV, &oldSegv, nullptr);
                sigaction(SIGABRT, &oldAbrt, nullptr);
                sigaction(SIGFPE, &oldFpe, nullptr);
            }
            g_solveCrashActive = 0;
            pImpl->lastUnknownReason_ =
                "native crash (signal) during solve — firewalled to Unknown";
            pImpl->lastModel_.reset();
            wall::endSolve();
            return Result::Unknown;
        }
        struct sigaction sa{};
        sa.sa_handler = solveCrashHandler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = SA_NODEFER;
        sigaction(SIGSEGV, &sa, &oldSegv);
        sigaction(SIGABRT, &sa, &oldAbrt);
        sigaction(SIGFPE, &sa, &oldFpe);
        fwInstalled = true;
        g_solveCrashActive = 1;
    }
    // Top-level bad_alloc firewall (iter#18, pre-existing class). A pathological
    // input (e.g. AProVE aproveSMT4461031801876451415: 16 vars + nested
    // assertion) can OOM deep in atomization / theory / SAT layers before any
    // budget-guard reacts. Returning Unknown via this catch is sound and
    // preserves the solver process (vs aborting with std::terminate or
    // emitting the `(error std::bad_alloc)` token that downstream pipelines
    // interpret as a hard crash). The catch is at the OUTER boundary so any
    // bad_alloc — regardless of which inner stage allocated past the
    // process limit — surfaces as a clean Unknown verdict.
    try {
        // Test-only hook to exercise the native-crash firewall (#19/#49). Gated by
        // an env var no production path sets; raises a synchronous SIGSEGV inside
        // the guarded region so the firewall's recover-to-Unknown can be tested.
        if (env::diag("XOLVER_TEST_FORCE_CRASH")) {
            volatile int* p = nullptr;
            *p = 1;  // SIGSEGV
        }
        int ebsRounds = env::paramInt("XOLVER_ESCALATING_BOUNDED_SAT", 0);
        if (ebsRounds > 0 && !std::getenv("XOLVER_STRAT_PORTFOLIO")) {
            int budget = env::paramInt("XOLVER_ESCALATING_BOUNDED_SAT_BUDGET_MS", 15000);
            r = pImpl->checkSatEscalatingBoundedSat(ebsRounds, budget);
        } else {
            r = std::getenv("XOLVER_STRAT_PORTFOLIO")
                    ? pImpl->checkSatPortfolio()
                    : pImpl->checkSatInternal();
        }
    } catch (const std::bad_alloc&) {
        pImpl->lastUnknownReason_ = "out-of-memory (bad_alloc) — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    } catch (const std::length_error& e) {
        // libgmp / std::vector etc. throw length_error when a polynomial DAG
        // attempts to construct a container past max_size — a different
        // exception class than bad_alloc but the same crash-class symptom.
        // Iter#19 extension of the iter#18 firewall: same Unknown-conversion
        // contract.
        pImpl->lastUnknownReason_ =
            std::string("length_error (") + e.what() +
            ") — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    } catch (const std::exception& e) {
        // Catch-all for any other std::exception escaping the inner solve.
        // Sound: returns Unknown for any case the solver could not complete
        // cleanly. Preserves the solver process for downstream cases (e.g.
        // run_regression --j-mode running many files per worker).
        pImpl->lastUnknownReason_ =
            std::string("exception (") + e.what() +
            ") — solver firewalled to Unknown";
        pImpl->lastModel_.reset();
        r = Result::Unknown;
    }
    if (fwInstalled) {
        g_solveCrashActive = 0;
        sigaction(SIGSEGV, &oldSegv, nullptr);
        sigaction(SIGABRT, &oldAbrt, nullptr);
        sigaction(SIGFPE, &oldFpe, nullptr);
    }
    wall::endSolve();
#ifdef XOLVER_ENABLE_PROOFS
    // Phase C: if this proof-mode solve collected exactly ONE theory conflict
    // certificate, that conflict alone refutes the asserted literals — render its
    // atoms via the CoreIr we own and emit a complete Alethe theory proof to
    // <base>.alethe (Carcara checks it against the original problem). Only the
    // unambiguous single-conflict case for now; multi-conflict / Boolean assembly
    // is later. A wrong certificate is rejected by Carcara offline (never
    // claimed), so this only ADDS a verifiable artifact next to the DRAT.
    pImpl->lastProof_.clear();  // fresh per solve
    const proof::TheoryConflictCert* uc =
        (r == Result::Unsat && pImpl->ir)
            ? proofUniqueConflict(pImpl->proofSink_.conflicts()) : nullptr;
    if (uc) {
        auto pit = pImpl->options.find("produce-proofs");
        if (pit != pImpl->options.end() &&
            pit->second.kind == OptionValue::String && !pit->second.s.empty()) {
            const auto& c = *uc;
            // Soundness guard: the Farkas multipliers come from the simplex (the
            // certificate is correct by Farkas' lemma + the infeasible-row
            // invariant), so we only need ASSUME-validity here: emit the la_generic
            // proof ONLY when every conflict literal is POSITIVELY asserted and is
            // a TOP-LEVEL problem assertion (so the proof's `assume` matches a real
            // premise) AND is an arithmetic comparison (Lt/Leq/Gt/Geq/Eq — the
            // forms la_generic reasons over). Anything else (negated/nested atoms,
            // non-arith) stays a VERIFIED-SKELETON. A wrong multiplier would still
            // be rejected by Carcara offline, never claimed.
            std::optional<proof::AletheProof> builtProof;
            const auto& asserts = pImpl->ir->assertions();
            std::unordered_set<ExprId> assertSet(asserts.begin(), asserts.end());
            // Negated atoms of the top-level (not X) assertions — the assume-valid
            // forms of EUF disequalities (the conclusion of a transitivity/congruence
            // conflict is asserted as (not (= l r))).
            std::unordered_set<ExprId> negAssert;
            for (ExprId a : asserts) {
                const auto& e = pImpl->ir->get(a);
                if (e.kind == Kind::Not && e.children.size() == 1)
                    negAssert.insert(e.children[0]);
            }
            if (!c.lits.empty() && c.rule == "la_generic") {
                // LRA: each literal positively-asserted, top-level, an arithmetic
                // comparison (inequality OR equality), and linear + sort-safe (no
                // division / no non-integer real constants — else la_generic can't
                // certify it or the dumped problem won't parse).
                bool ok = (c.lits.size() == c.args.size());
                bool hasEq = false;
                for (const auto& [atomId, positive] : c.lits) {
                    if (!positive || !assertSet.count(atomId)) { ok = false; break; }
                    const auto& e = pImpl->ir->get(atomId);
                    if (e.kind != Kind::Lt && e.kind != Kind::Leq &&
                        e.kind != Kind::Gt && e.kind != Kind::Geq &&
                        e.kind != Kind::Eq) { ok = false; break; }
                    if (e.kind == Kind::Eq) hasEq = true;
                    for (ExprId ch : e.children)
                        if (!proofLinSafe(ch, *pImpl->ir)) { ok = false; break; }
                    if (!ok) break;
                }
                // The simplex's Farkas multipliers are non-negative bound coeffs; for
                // an EQUALITY atom that is the wrong sign half the time (it depends on
                // whether the upper or lower bound was used). Independently VERIFY the
                // Farkas combination and search the ± sign of each equality multiplier
                // for one that genuinely refutes; emit only a verified, Carcara-valid
                // sign assignment, else stay skeleton. Pure-inequality conflicts keep
                // the simplex coeffs as-is (no verification, no regression).
                std::vector<std::string> emitArgs;
                if (ok && hasEq) {
                    std::vector<AtomForm> forms(c.lits.size());
                    std::vector<mpq_class> mag(c.lits.size());
                    std::vector<int> eqIdx;
                    for (size_t i = 0; ok && i < c.lits.size(); ++i) {
                        if (!proofAtomForm(c.lits[i].first, *pImpl->ir, forms[i])) { ok = false; break; }
                        mpq_class q(c.args[i]); q.canonicalize();
                        mag[i] = abs(q);
                        if (forms[i].isEq) eqIdx.push_back(static_cast<int>(i));
                    }
                    if (ok && eqIdx.size() > 12) ok = false;  // bound the sign search
                    if (ok) {
                        bool found = false;
                        for (uint32_t mask = 0; !found && mask < (1u << eqIdx.size()); ++mask) {
                            std::vector<mpq_class> coeffs(c.lits.size());
                            for (size_t i = 0; i < c.lits.size(); ++i) coeffs[i] = mag[i];
                            for (size_t j = 0; j < eqIdx.size(); ++j)
                                if (mask & (1u << j)) coeffs[eqIdx[j]] = -coeffs[eqIdx[j]];
                            if (proofFarkasContradicts(forms, coeffs)) {
                                emitArgs.resize(c.lits.size());
                                for (size_t i = 0; i < c.lits.size(); ++i)
                                    emitArgs[i] = coeffs[i].get_str();
                                found = true;
                            }
                        }
                        ok = found;
                    }
                }
                if (ok) {
                    std::vector<proof::AssertedLit> lits;
                    lits.reserve(c.lits.size());
                    for (const auto& [eid, positive] : c.lits)
                        lits.push_back({dumpExprToSMT2(eid, *pImpl->ir), positive});
                    builtProof = proof::buildConflictRefutation(
                        lits, c.rule, hasEq ? emitArgs : c.args);
                }
            } else if (!c.lits.empty() && c.rule == "eq_transitive") {
                if (proofEufTransitivityOk(c.lits, *pImpl->ir, assertSet, negAssert)) {
                    // PURE TRANSITIVITY: the independent union-find connects the
                    // conclusion endpoints. Render each literal, mapping a binary
                    // distinct to its underlying equality with flipped polarity.
                    std::vector<proof::AssertedLit> lits;
                    lits.reserve(c.lits.size());
                    for (const auto& [eid, positive] : c.lits) {
                        const auto& e = pImpl->ir->get(eid);
                        if (e.kind == Kind::Distinct && e.children.size() == 2) {
                            std::string eq = "(= " + dumpExprToSMT2(e.children[0], *pImpl->ir)
                                           + " " + dumpExprToSMT2(e.children[1], *pImpl->ir) + ")";
                            lits.push_back({std::move(eq), !positive});
                        } else {
                            lits.push_back({dumpExprToSMT2(eid, *pImpl->ir), positive});
                        }
                    }
                    builtProof = proof::buildConflictRefutation(lits, c.rule, c.args);
                } else {
                    // CONGRUENCE: reconstruct via eq_congruent over function args +
                    // eq_transitive over leaf chains. Classify the literals into leaf
                    // equalities (positive Eq) and the single conclusion disequality
                    // (negative Eq or positive binary Distinct), each assume-valid.
                    ExprId lhsId = NullExpr, rhsId = NullExpr;
                    std::string diseqAssume;
                    std::vector<std::tuple<ExprId, ExprId, std::string>> leafEqs;
                    bool congOk = true;
                    int conclusions = 0;
                    for (const auto& [atomId, positive] : c.lits) {
                        const auto& e = pImpl->ir->get(atomId);
                        const bool isEq2 = (e.kind == Kind::Eq && e.children.size() == 2);
                        const bool isDist2 = (e.kind == Kind::Distinct && e.children.size() == 2);
                        if (isEq2 && positive) {
                            if (!assertSet.count(atomId)) { congOk = false; break; }
                            leafEqs.emplace_back(e.children[0], e.children[1],
                                                 dumpExprToSMT2(atomId, *pImpl->ir));
                        } else if ((isEq2 && !positive && negAssert.count(atomId)) ||
                                   (isDist2 && positive && assertSet.count(atomId))) {
                            lhsId = e.children[0];
                            rhsId = e.children[1];
                            ++conclusions;
                            diseqAssume = "(not (= " + dumpExprToSMT2(lhsId, *pImpl->ir) + " "
                                                     + dumpExprToSMT2(rhsId, *pImpl->ir) + "))";
                        } else {
                            congOk = false;
                            break;
                        }
                    }
                    // A self-disequality (distinct a a) has no leaf equalities — the
                    // refl path handles it — so only require a single conclusion.
                    if (congOk && conclusions == 1) {
                        proof::AletheProof cong;
                        if (proofEufCongruence(lhsId, rhsId, leafEqs, diseqAssume,
                                               *pImpl->ir, cong))
                            builtProof = std::move(cong);
                    }
                }
            } else if (!c.lits.empty() && c.rule == "bool_congruence") {
                // Boolean-assembly increment 1: a Bool e-class is both true and
                // false. Classify the reasons: a positive Eq is a leaf equality; a
                // positive UFApply is the asserted-true predicate; a negative
                // UFApply is the asserted-false predicate. Assume-validity: leaf
                // equalities and the true predicate are positive top-level
                // assertions; the false predicate's negation is a top-level (not X)
                // assertion. Anything else -> skeleton.
                ExprId predTrueId = NullExpr, predFalseId = NullExpr;
                std::vector<std::tuple<ExprId, ExprId, std::string>> leafEqs;
                bool bcOk = true;
                int nTrue = 0, nFalse = 0;
                for (const auto& [atomId, positive] : c.lits) {
                    const auto& e = pImpl->ir->get(atomId);
                    if (e.kind == Kind::Eq && e.children.size() == 2 && positive) {
                        if (!assertSet.count(atomId)) { bcOk = false; break; }
                        leafEqs.emplace_back(e.children[0], e.children[1],
                                             dumpExprToSMT2(atomId, *pImpl->ir));
                    } else if (e.kind == Kind::UFApply) {
                        if (positive) {
                            if (!assertSet.count(atomId)) { bcOk = false; break; }
                            predTrueId = atomId; ++nTrue;
                        } else {
                            if (!negAssert.count(atomId)) { bcOk = false; break; }
                            predFalseId = atomId; ++nFalse;
                        }
                    } else {
                        bcOk = false; break;
                    }
                }
                if (bcOk && nTrue == 1 && nFalse == 1) {
                    proof::AletheProof bc;
                    if (proofBoolCongruence(
                            predTrueId, predFalseId, leafEqs,
                            dumpExprToSMT2(predTrueId, *pImpl->ir),
                            dumpExprToSMT2(predFalseId, *pImpl->ir),
                            *pImpl->ir, bc))
                        builtProof = std::move(bc);
                }
            }
            if (builtProof) {
                // The proof references post-normalization IR atoms, so it is
                // checked against an IR-derived problem (terms match by
                // construction); the original->IR step is trusted preprocessing.
                std::string problemStr = dumpProblemToSMT2(*pImpl->ir, pImpl->ir->assertions());
                std::string aletheStr = builtProof->serialize();
                std::ofstream pout(pit->second.s + ".smt2");
                if (pout) pout << problemStr;
                std::ofstream aout(pit->second.s + ".alethe");
                if (aout) aout << aletheStr;
                // Also expose it via the public Solver::getProof() value.
                pImpl->lastProof_.set(std::move(aletheStr), std::move(problemStr));
            }
        }
    }
    // Phase F2a/F2b: theory-lemma Boolean assembly. Runs when at least one theory
    // conflict cert exists but the closed-proof path above did NOT emit (e.g. the
    // conflict's disequality is buried in a top-level n-ary `(distinct ...)` / And,
    // not a top-level assertion — or the refutation needs MULTIPLE distinct conflicts,
    // so proofUniqueConflict returned null). Clausify the ORIGINAL assertions over
    // their theory atoms, splice EACH distinct conflict's theory tautology as a real
    // sub-proof, and replay the propositional refutation from a dedicated LRAT solve —
    // one Carcara-checked Alethe proof against the original problem. Degrades silently
    // (the captured conflict set may be insufficient -> CEGAR, out of scope).
    if (r == Result::Unsat && pImpl->ir && pImpl->lastProof_.isEmpty() &&
        !pImpl->proofSink_.conflicts().empty()) {
        auto pit = pImpl->options.find("produce-proofs");
        if (pit != pImpl->options.end() &&
            pit->second.kind == OptionValue::String && !pit->second.s.empty()) {
            const auto& origAsserts = pImpl->originalAssertions_;
            auto distinctCerts = proofDistinctConflicts(pImpl->proofSink_.conflicts());
            auto bp = tryTheoryLemmaBooleanProof(*pImpl->ir, origAsserts, distinctCerts);
            if (bp) {
                std::string problemStr = dumpProblemToSMT2(*pImpl->ir, origAsserts);
                std::string aletheStr = bp->serialize();
                std::ofstream pout(pit->second.s + ".smt2");
                if (pout) pout << problemStr;
                std::ofstream aout(pit->second.s + ".alethe");
                if (aout) aout << aletheStr;
                pImpl->lastProof_.set(std::move(aletheStr), std::move(problemStr));
            }
        }
    }
    // Phase F1: pure-propositional Boolean assembly. Runs only when no single-
    // conflict theory proof was emitted above (lastProof_ still empty) and the
    // instance is flat-clausal propositional — then the refutation is replayed
    // from the SAT engine's LRAT as one Carcara-checkable Alethe proof. Degrades
    // silently (DRAT remains the fallback) on anything it can't translate.
    if (r == Result::Unsat && pImpl->ir && pImpl->lastProof_.isEmpty()) {
        auto pit = pImpl->options.find("produce-proofs");
        if (pit != pImpl->options.end() &&
            pit->second.kind == OptionValue::String && !pit->second.s.empty()) {
            // Use the ORIGINAL (pre-purification) assertion roots: Boolean
            // purification rewrites the IR into boolpur_* proxy equalities that
            // are not flat-clausal, but the original `(or ...)` / unit assertions
            // are — and proving against the original problem is strictly better.
            const auto& origAsserts = pImpl->originalAssertions_;
            auto bp = tryFlatClausalBooleanProof(*pImpl->ir, origAsserts);
            if (bp) {
                std::string problemStr =
                    dumpProblemToSMT2(*pImpl->ir, origAsserts);
                std::string aletheStr = bp->serialize();
                std::ofstream pout(pit->second.s + ".smt2");
                if (pout) pout << problemStr;
                std::ofstream aout(pit->second.s + ".alethe");
                if (aout) aout << aletheStr;
                pImpl->lastProof_.set(std::move(aletheStr), std::move(problemStr));
            }
        }
    }
    proof::setActiveProofSink(nullptr);
#endif
    return r;
}

Result Solver::checkSatAssuming(std::vector<Term> assumptions) {
    pImpl->lastAssumptions_ = assumptions;
    // Sound fallback core: until the SAT layer reports a minimized subset, the
    // whole assumption set is a valid (if non-minimal) core.
    pImpl->lastUnsatCore_ = assumptions;

    // Preferred path (hard assertions present): pass the assumptions to the SAT
    // core as real assumption LITERALS rather than asserting them. Each
    // assumption atom is observed by the theory via atomize, CaDiCaL assumes its
    // literal, and on UNSAT failed() yields the MINIMIZED core (see
    // checkSatInternal). Not mutating the assertion list means lowering can never
    // rewrite an assumption, and getUnsatCore() returns the true failing subset.
    const bool haveHardAssertions = pImpl->ir && !pImpl->ir->assertions().empty();
    if (haveHardAssertions) {
        pImpl->assumptionRoots_.clear();
        pImpl->assumptionRoots_.reserve(assumptions.size());
        for (Term a : assumptions) pImpl->assumptionRoots_.push_back(a.id());
        Result r = checkSat();
        pImpl->assumptionRoots_.clear();
        return r;
    }

    // Degenerate path (no hard assertions): the SAT-assumption route would have
    // nothing to drive theory setup / would short-circuit on the empty assertion
    // set. Fall back to the original behavior — assert the assumptions as
    // formulas so the worker reaches a real solve — giving the correct verdict
    // with the conservative full-set core (no minimization, but no regression).
    push();
    for (Term a : assumptions) assertFormula(a);
    Result r = checkSat();
    pop();
    return r;
}

Model Solver::getModel() const {
    Model model;
    if (!pImpl) return model;

    if (!pImpl->lastModel_) return model;

    const auto& theoryModel = *pImpl->lastModel_;

    // Map variable names to ExprIds from CoreIr. Prefer the string
    // `assignments` channel; fall back to the typed `numericAssignments`
    // channel (RealValue) when the string channel is empty. The numeric
    // channel is the path the LIA solver uses by default when no string
    // serialization is requested. Without this fallback, an API-mode
    // caller (Solver::getModel() invoked programmatically, no CLI
    // `get-model` command) sees an empty Model even on a successful
    // checkSat → Sat. Pre-existing bug uncovered by test_api LIA test.
    if (pImpl->ir) {
        for (ExprId id = 0; id < static_cast<ExprId>(pImpl->ir->size()); ++id) {
            const auto& expr = pImpl->ir->get(id);
            if (expr.kind != Kind::Variable) continue;
            if (!std::holds_alternative<std::string>(expr.payload.value)) continue;
            const std::string& name = std::get<std::string>(expr.payload.value);
            auto it = theoryModel.assignments.find(name);
            if (it != theoryModel.assignments.end()) {
                model.setValue(id, it->second);
                continue;
            }
            // Fallback: typed numeric channel.
            auto nit = theoryModel.numericAssignments.find(name);
            if (nit != theoryModel.numericAssignments.end()) {
                if (auto q = nit->second.tryAsRational()) {
                    model.setValue(id, q->get_str());
                }
            }
        }
    }

    return model;
}
Term Solver::getValue(Term t) {
    if (!pImpl || !pImpl->ir) return Term{};

    const auto& expr = pImpl->ir->get(t.id());
    auto sortKind = pImpl->ir->sortKind(expr.sort);

    // Prefer the typed numeric channel (RealValue) when available: it carries
    // exact values including algebraic ones (e.g. √2 for x²=2), which the
    // legacy string channel cannot represent losslessly.
    if (pImpl->lastModel_ && std::holds_alternative<std::string>(expr.payload.value)) {
        const std::string& name = std::get<std::string>(expr.payload.value);
        const auto& num = pImpl->lastModel_->numericAssignments;
        auto nit = num.find(name);
        if (nit != num.end()) {
            const RealValue& rv = nit->second;
            if (sortKind == SortKind::Int && rv.isExactInteger()) {
                mpz_class fl = rv.floor();
                if (fl.fits_slong_p()) return mkInt(static_cast<int64_t>(fl.get_si()));
            }
            return mkReal(rv.toSmtLib2());
        }
    }

    // Legacy string channel.
    Model m = getModel();
    const std::string* val = m.getValue(t.id());
    if (!val) return Term{};

    if (sortKind == SortKind::Int) {
        int64_t v = std::stoll(*val);
        return mkInt(v);
    } else if (sortKind == SortKind::Real) {
        return mkReal(*val);
    } else if (sortKind == SortKind::Bool) {
        return mkBool(*val == "true");
    }
    return Term{};
}
std::vector<Term> Solver::getUnsatCore() const {
    if (!pImpl) return {};
    // Assumption-based core: the minimized subset of the checkSatAssuming
    // assumptions that CaDiCaL's failed() reported as necessary for UNSAT
    // (falls back to the full assumption set when no SAT-level minimization was
    // available, e.g. UNSAT proven in preprocessing). Sound, possibly
    // non-minimal. Meaningful only after checkSatAssuming() returned Unsat.
    return pImpl->lastUnsatCore_;
}

bool Solver::unsatCoreRequested() const {
    if (!pImpl) return false;
    auto it = pImpl->options.find("produce-unsat-cores");
    if (it != pImpl->options.end() && it->second.kind == OptionValue::Bool &&
        it->second.b)
        return true;
    if (!pImpl->parser) return false;
    auto opts = pImpl->parser->getOptions();
    return opts && opts->get_unsat_core;
}

void Solver::dumpUnsatCore(std::ostream& os) const {
    // SMT-LIB get-unsat-core response shape: a parenthesized list. We emit the
    // ORIGINAL assertions that form the core as SMT-LIB terms (Xolver gates each
    // assertion with an indicator; :named-name output is a future enhancement
    // needing the parser to expose its named-assertion map).
    os << "(";
    if (pImpl && pImpl->ir) {
        const auto& core = pImpl->lastUnsatCore_;
        for (size_t i = 0; i < core.size(); ++i) {
            os << (i ? " " : "") << dumpExprToSMT2(core[i].id(), *pImpl->ir);
        }
    }
    os << ")\n";
}

bool Solver::modelRequested() const {
    if (!pImpl || !pImpl->parser) return false;
    auto opts = pImpl->parser->getOptions();
    return opts && opts->get_model;
}

std::vector<Solver::ScriptResponseCommand> Solver::scriptResponseCommands() const {
    std::vector<ScriptResponseCommand> out;
    if (!pImpl || !pImpl->parser) return out;
    using K = ScriptResponseCommand::Kind;
    const auto& cmds = pImpl->parser->getScript().commands();
    for (size_t i = 0; i < cmds.size(); ++i) {
        const auto& cmd = cmds[i];
        switch (cmd.type) {
            case SOMTParser::CMD_TYPE::CT_ECHO:
                out.push_back({K::Echo, cmd.keyword, i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_INFO:
                out.push_back({K::GetInfo, cmd.keyword, i}); break;
            case SOMTParser::CMD_TYPE::CT_CHECK_SAT:
            case SOMTParser::CMD_TYPE::CT_CHECK_SAT_ASSUMING:
                out.push_back({K::CheckSat, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_VALUE:
                out.push_back({K::GetValue, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_MODEL:
                out.push_back({K::GetModel, "", i}); break;
            case SOMTParser::CMD_TYPE::CT_GET_ASSIGNMENT:
                out.push_back({K::GetAssignment, "", i}); break;
            default: break;
        }
    }
    return out;
}

bool Solver::modelMatchesOriginal() const {
    if (!pImpl || !pImpl->ir || !pImpl->lastModel_) return true;  // nothing to disprove
    ArithModelValidator::NumAssignment numAsg;
    ArithModelValidator::BoolAssignment boolAsg;
    for (const auto& [name, val] : pImpl->lastModel_->assignments) {
        if (val == "true")  { boolAsg[name] = true;  continue; }
        if (val == "false") { boolAsg[name] = false; continue; }
        try { numAsg[name] = mpq_class(val); }
        catch (...) { /* unparseable → leave unassigned (indeterminate) */ }
    }
    ArithModelValidator validator(*pImpl->ir, numAsg, boolAsg);
    // Only a DEFINITE violation counts as "does not match".
    return validator.validate(pImpl->originalAssertions_)
           != ArithModelValidator::Verdict::Violated;
}

namespace {
// Format a model value string (as stored by the theory model — e.g. "5",
// "-3", "3/2", "true") into an SMT-LIB term of the given sort.
std::string formatModelValue(SortKind kind, const std::string& raw) {
    if (kind == SortKind::Bool) {
        return (raw == "true" || raw == "1") ? "true" : "false";
    }
    // Numeric: split optional sign and optional p/q.
    std::string s = raw;
    bool neg = false;
    if (!s.empty() && s[0] == '-') { neg = true; s = s.substr(1); }
    auto slash = s.find('/');
    std::string body;
    if (slash != std::string::npos) {
        std::string num = s.substr(0, slash);
        std::string den = s.substr(slash + 1);
        if (kind == SortKind::Int) {
            // An Int model value should be integral; if a denominator slipped
            // through, fall back to the numerator (defensive — shouldn't happen).
            body = (den == "1") ? num : num;
        } else {
            body = (den == "1") ? (num + ".0") : ("(/ " + num + " " + den + ")");
        }
    } else {
        body = (kind == SortKind::Real) ? (s + ".0") : s;
    }
    return neg ? ("(- " + body + ")") : body;
}
} // namespace

std::string Solver::getValueResponse(size_t scriptIndex) const {
    if (!pImpl || !pImpl->parser || !pImpl->lastModel_) return {};
    const auto& cmds = pImpl->parser->getScript().commands();
    if (scriptIndex >= cmds.size()) return {};
    const auto& cmd = cmds[scriptIndex];
    if (cmd.type != SOMTParser::CMD_TYPE::CT_GET_VALUE) return {};
    const auto& model = *pImpl->lastModel_;
    std::string out = "(";
    for (const auto& t : cmd.value_terms) {
        if (!t) return {};
        std::string val;
        if (t->isVBool() || t->isVInt() || t->isVReal()) {
            auto it = model.assignments.find(t->getName());
            if (it == model.assignments.end()) return {};  // unassigned -> bail
            SortKind sk = t->isVBool() ? SortKind::Bool
                        : t->isVInt()  ? SortKind::Int
                                       : SortKind::Real;
            val = formatModelValue(sk, it->second);
        } else if (t->isConst()) {
            val = SOMTParser::dumpSMTLIB2(t);  // a literal evaluates to itself
        } else {
            return {};  // compound / unsupported term -> emit nothing (no wrong value)
        }
        out += "(" + SOMTParser::dumpSMTLIB2(t) + " " + val + ")";
    }
    out += ")";
    return out;
}

void Solver::dumpModel(std::ostream& os) const {
    // SMT-LIB 2.6 get-model response: a bare list of define-fun bindings,
    // one per user-declared 0-arity symbol. Values come from the last
    // theory model; unconstrained symbols get a sort-appropriate default.
    if (!pImpl) { os << "(\n)\n"; return; }

    const TheorySolver::TheoryModel* tm =
        pImpl->lastModel_ ? &*pImpl->lastModel_ : nullptr;

    // -----------------------------------------------------------------------
    // Array model token resolution (QF_AX + combination array logics).
    //
    // EufSolver::getModel() emits each array as an ArrayInterp over opaque
    // equality TOKENS for index/element values:
    //   "#n:<rational>" — a concrete number (combination logics: the bridged
    //                     select/index value flowing from the arith model);
    //   "#b:1"/"#b:0"   — a concrete bool;
    //   "@e..."/"@def..." — an opaque uninterpreted-sort element (QF_AX) or an
    //                     unconstrained index/element with no numeric pin.
    // The egraph compares these by EQUALITY ONLY, so the printed model must
    // assign each DISTINCT token a DISTINCT concrete value (preserving
    // disequalities) and each occurrence of the SAME token the SAME value
    // (preserving the asserted reads). We mint concrete values here:
    //   - numeric/bool tokens print as themselves;
    //   - opaque tokens in an Int/Real sort get a fresh integer (chosen to
    //     avoid colliding with any explicit numeric token in that array);
    //   - opaque tokens in an uninterpreted sort get an abstract constant
    //     "@<sort>!<n>" declared as a 0-arity symbol of that sort (z3-style,
    //     replayable). One namespace per uninterpreted sort.
    // This block computes tokenSmt(token, smtSort) -> printable SMT term and
    // collects the abstract-constant declarations to emit first.
    // -----------------------------------------------------------------------
    struct ArrayModelEmitter {
        // smtSort string -> kind classification.
        enum class SK { Int, Real, Bool, Uninterp };
        // Per-uninterpreted-sort: token -> abstract constant name.
        std::map<std::string, std::map<std::string, std::string>> uninterpConsts;
        // Per-uninterpreted-sort emission counter.
        std::map<std::string, int> uninterpCounter;
        // Int/Real opaque token -> chosen integer (global; Int values are
        // globally distinct so one namespace is fine), avoiding used numbers.
        std::map<std::string, std::string> numericOpaque;
        std::set<long long> usedNums;        // explicit numbers seen anywhere
        long long nextFreeNum = 0;

        static SK classify(const std::string& smtSort) {
            if (smtSort == "Int")  return SK::Int;
            if (smtSort == "Real") return SK::Real;
            if (smtSort == "Bool") return SK::Bool;
            return SK::Uninterp;
        }

        // Pre-scan: record every explicit numeric token so minted integers
        // never collide with a real value the formula constrained.
        void noteToken(const std::string& tok) {
            if (tok.rfind("#n:", 0) == 0) {
                try {
                    mpq_class q(tok.substr(3));
                    if (q.get_den() == 1 && q.get_num().fits_slong_p())
                        usedNums.insert(q.get_num().get_si());
                } catch (...) {}
            }
        }

        std::string freshNum() {
            while (usedNums.count(nextFreeNum)) ++nextFreeNum;
            long long v = nextFreeNum++;
            usedNums.insert(v);
            return std::to_string(v);
        }

        // Resolve a token to a printable SMT term of the given sort.
        std::string resolve(const std::string& tok, const std::string& smtSort) {
            SK k = classify(smtSort);
            if (tok.rfind("#b:", 0) == 0) return tok.substr(3) == "1" ? "true" : "false";
            if (tok.rfind("#n:", 0) == 0) {
                std::string body = tok.substr(3);
                return formatModelValue(k == SK::Real ? SortKind::Real : SortKind::Int, body);
            }
            // Opaque token.
            if (k == SK::Bool) return "false";  // unconstrained bool
            if (k == SK::Int || k == SK::Real) {
                auto it = numericOpaque.find(tok);
                std::string n;
                if (it != numericOpaque.end()) n = it->second;
                else { n = freshNum(); numericOpaque[tok] = n; }
                return formatModelValue(k == SK::Real ? SortKind::Real : SortKind::Int, n);
            }
            // Uninterpreted sort: abstract constant per token.
            auto& byTok = uninterpConsts[smtSort];
            auto it = byTok.find(tok);
            if (it != byTok.end()) return it->second;
            int idx = uninterpCounter[smtSort]++;
            std::string cname = "@" + smtSort + "!" + std::to_string(idx);
            byTok[tok] = cname;
            return cname;
        }
    } emit;

    // Build name -> declared array Sort (index/element SMT sort strings) for
    // every declared array variable, and pre-scan tokens for numeric collisions.
    struct ArrSorts { std::string idxSmt, elemSmt; };
    std::map<std::string, ArrSorts> arrSorts;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var || !var->isArray()) continue;
            auto s = var->getSort();
            if (!s) continue;
            auto is = s->getIndexSort(), es = s->getElemSort();
            if (!is || !es) continue;
            arrSorts[var->getName()] = {is->toString(), es->toString()};
        }
    }
    if (tm) {
        for (const auto& [aname, ai] : tm->arrayInterps) {
            emit.noteToken(ai.defaultVal);
            for (const auto& [ix, vl] : ai.entries) { emit.noteToken(ix); emit.noteToken(vl); }
        }
    }

    // Map each scalar (index/element) variable name to the SMT sort of any
    // array position it tokenizes into, so its opaque token resolves in the
    // SAME namespace the array entries use. We learn the sort from the parser
    // declaration of the scalar itself.
    auto scalarSmtSort = [&](const std::shared_ptr<SOMTParser::DAGNode>& v) -> std::string {
        if (v->isVBool()) return "Bool";
        if (v->isVInt())  return "Int";
        if (v->isVReal()) return "Real";
        auto s = v->getSort();
        return s ? s->toString() : "";
    };

    os << "(\n";

    // First emit array define-funs (so the scalar index/element values they
    // reference are resolved into emit's token maps before we print scalars,
    // keeping the two consistent). EVERY declared array variable must get a
    // define-fun (get-model completeness), even those absent from the theory
    // model (e.g. an array eliminated by read-over-write simplification, which
    // is then unconstrained → any const array is a valid witness).
    std::ostringstream arrayBuf;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var || !var->isArray()) continue;
            std::string name = var->getName();
            auto sortsIt = arrSorts.find(name);
            std::string idxSmt = sortsIt != arrSorts.end() ? sortsIt->second.idxSmt : "Int";
            std::string elemSmt = sortsIt != arrSorts.end() ? sortsIt->second.elemSmt : "Int";
            std::string arrSmt = "(Array " + idxSmt + " " + elemSmt + ")";

            std::string body;
            auto itAi = tm ? tm->arrayInterps.find(name)
                           : std::unordered_map<std::string,
                                 TheorySolver::TheoryModel::ArrayInterp>::const_iterator{};
            if (tm && itAi != tm->arrayInterps.end()) {
                const auto& ai = itAi->second;
                body = "((as const " + arrSmt + ") " +
                       emit.resolve(ai.defaultVal, elemSmt) + ")";
                std::string defv = emit.resolve(ai.defaultVal, elemSmt);
                for (const auto& [ix, vl] : ai.entries) {
                    // Skip entries that equal the default (no-op store).
                    std::string ixv = emit.resolve(ix, idxSmt);
                    std::string vlv = emit.resolve(vl, elemSmt);
                    if (vlv == defv) continue;
                    body = "(store " + body + " " + ixv + " " + vlv + ")";
                }
            } else {
                // Unconstrained array: a const array over a fresh element value.
                body = "((as const " + arrSmt + ") " +
                       emit.resolve("@unconstrained_arr_default:" + name, elemSmt) + ")";
            }
            arrayBuf << "  (define-fun " << name << " () " << arrSmt << " "
                     << body << ")\n";
        }
    }

    // Scalar variables (Int/Real/Bool AND uninterpreted index/element vars).
    std::ostringstream scalarBuf;
    if (pImpl->parser) {
        for (const auto& var : pImpl->parser->getDeclaredVariables()) {
            if (!var) continue;
            if (var->isArray()) continue;  // handled above
            std::string name = var->getName();
            std::string smtSort = scalarSmtSort(var);
            if (smtSort.empty()) continue;
            ArrayModelEmitter::SK kind = ArrayModelEmitter::classify(smtSort);

            // Algebraic values (irrational roots) live in the typed RealValue
            // channel; emit their exact root-of form directly.
            if (tm && kind == ArrayModelEmitter::SK::Real) {
                auto rvIt = tm->numericAssignments.find(name);
                if (rvIt != tm->numericAssignments.end() && rvIt->second.isAlgebraic()) {
                    scalarBuf << "  (define-fun " << name << " () Real "
                              << rvIt->second.toSmtLib2() << ")\n";
                    continue;
                }
            }

            std::string raw;
            if (tm) {
                auto it = tm->assignments.find(name);
                if (it != tm->assignments.end()) raw = it->second;
            }
            std::string valTerm;
            if (raw.empty()) {
                // Unconstrained.
                if (kind == ArrayModelEmitter::SK::Bool) valTerm = "false";
                else if (kind == ArrayModelEmitter::SK::Uninterp)
                    valTerm = emit.resolve("@unconstrained:" + name, smtSort);
                else valTerm = formatModelValue(
                    kind == ArrayModelEmitter::SK::Real ? SortKind::Real : SortKind::Int, "0");
            } else if (raw == "true" || raw == "false") {
                valTerm = raw;
            } else {
                // May be a plain number (arith model) or a token (EUF model).
                if (raw.rfind("#n:", 0) == 0 || raw.rfind("#b:", 0) == 0 ||
                    raw.rfind("@", 0) == 0) {
                    valTerm = emit.resolve(raw, smtSort);
                } else if (kind == ArrayModelEmitter::SK::Uninterp) {
                    valTerm = emit.resolve(raw, smtSort);
                } else {
                    valTerm = formatModelValue(
                        kind == ArrayModelEmitter::SK::Real ? SortKind::Real :
                        kind == ArrayModelEmitter::SK::Int  ? SortKind::Int  :
                        SortKind::Bool, raw);
                }
            }
            scalarBuf << "  (define-fun " << name << " () " << smtSort << " "
                      << valTerm << ")\n";
        }
    }

    // Emit abstract-constant declarations for uninterpreted-sort elements
    // FIRST (they are referenced by the array/scalar define-funs that follow).
    for (const auto& [sortName, byTok] : emit.uninterpConsts) {
        for (const auto& [tok, cname] : byTok) {
            os << "  (declare-fun " << cname << " () " << sortName << ")\n";
        }
    }
    os << arrayBuf.str();
    os << scalarBuf.str();

    // Uninterpreted function interpretations: a finite table emitted as a
    // nested ite over the asserted argument tuples, with a default for any
    // other input. Populated by the validated candidate search (QF_UF*).
    if (tm && !tm->functionInterps.empty()) {
        auto kindOf = [](const std::string& s) -> SortKind {
            if (s == "Int")  return SortKind::Int;
            if (s == "Bool") return SortKind::Bool;
            return SortKind::Real;
        };
        for (const auto& [fname, fi] : tm->functionInterps) {
            // Internal div/mod-by-zero carriers are re-expressed as `div`/`mod`
            // define-fun shadows below; never emit the __undef_* symbols, which
            // the model validator does not recognize.
            if (fname.rfind("__undef", 0) == 0) continue;
            os << "  (define-fun " << fname << " (";
            for (size_t i = 0; i < fi.argSorts.size(); ++i) {
                if (i) os << " ";
                os << "(x!" << i << " " << fi.argSorts[i] << ")";
            }
            SortKind retKind = kindOf(fi.retSort);
            os << ") " << fi.retSort << " ";
            std::string body =
                formatModelValue(retKind, fi.deflt.empty() ? "0" : fi.deflt);
            for (auto it = fi.entries.rbegin(); it != fi.entries.rend(); ++it) {
                std::string cond;
                if (it->args.size() == 1) {
                    cond = "(= x!0 " +
                           formatModelValue(kindOf(fi.argSorts[0]), it->args[0]) + ")";
                } else {
                    cond = "(and";
                    for (size_t i = 0; i < it->args.size(); ++i) {
                        cond += " (= x!" + std::to_string(i) + " " +
                                formatModelValue(kindOf(fi.argSorts[i]), it->args[i]) + ")";
                    }
                    cond += ")";
                }
                body = "(ite " + cond + " " +
                       formatModelValue(retKind, it->value) + " " + body + ")";
            }
            os << body << ")\n";
        }
    }

    // Partial theory functions (div/mod by zero): emit define-fun shadows that
    // give our chosen value at the undefined (divisor-0) inputs and otherwise
    // call the original theory function. The body may call the same-named
    // theory function — this is shadowing, not recursion (SMT-COMP 2026 model
    // format). The zero-branch is a nested-ite over the dividend a; any unlisted
    // zero-divisor input falls through to 0 (free choice for unconstrained
    // inputs).
    {
        const auto& pfm = pImpl->partialFuncModel_;
        auto zeroBranch = [](const std::map<mpq_class, mpq_class>& tbl) -> std::string {
            std::string body = "0";
            for (auto it = tbl.rbegin(); it != tbl.rend(); ++it) {
                body = "(ite (= a " + formatModelValue(SortKind::Int, it->first.get_str()) +
                       ") " + formatModelValue(SortKind::Int, it->second.get_str()) +
                       " " + body + ")";
            }
            return body;
        };
        if (!pfm.divZero.empty()) {
            os << "  (define-fun div ((a Int) (b Int)) Int (ite (= b 0) "
               << zeroBranch(pfm.divZero) << " (div a b)))\n";
        }
        if (!pfm.modZero.empty()) {
            os << "  (define-fun mod ((a Int) (b Int)) Int (ite (= b 0) "
               << zeroBranch(pfm.modZero) << " (mod a b)))\n";
        }
    }
    os << ")\n";
}
Proof Solver::getProof() const { return pImpl->lastProof_; }
Statistics Solver::getStatistics() const { return Statistics{}; }

std::string Solver::lastUnknownReason() const { return pImpl->lastUnknownReason_; }
std::string Solver::lastUnknownCode() const { return pImpl->lastUnknownCode_; }
std::string Solver::lastUnknownComponent() const { return pImpl->lastUnknownComponent_; }
std::string Solver::lastUnknownDetail() const { return pImpl->lastUnknownDetail_; }

#ifdef XOLVER_ENABLE_CASESTATS
void Solver::setDumpStatsPath(std::string_view path) {
    pImpl->dumpStatsPath_ = std::string(path);
}
#else
void Solver::setDumpStatsPath(std::string_view) {}
#endif

void Solver::dumpSMT2(std::ostream& os) {
    if (pImpl->parser && !pImpl->parser->getAssertions().empty()) {
        for (auto& a : pImpl->parser->getAssertions()) {
            os << SOMTParser::dumpSMTLIB2(a) << "\n";
        }
    } else if (pImpl->ir) {
        for (ExprId aid : pImpl->ir->assertions()) {
            os << dumpExprToSMT2(aid, *pImpl->ir) << "\n";
        }
    }
}

void Solver::dumpFeatures(std::ostream& os) const {
    if (!pImpl || !pImpl->ir) { os << "{}\n"; return; }
    const CoreIr& ir = *pImpl->ir;
    LogicFeatures f = LogicFeatureDetector(ir).detect();
    size_t nVars = 0;
    for (ExprId id = 0; id < static_cast<ExprId>(ir.size()); ++id)
        if (ir.get(id).kind == Kind::Variable) ++nVars;
    auto b = [](bool v) { return v ? "true" : "false"; };
    os << "{\"logic\":\"" << pImpl->logic << "\""
       << ",\"asserts\":" << ir.assertions().size()
       << ",\"vars\":" << nVars
       << ",\"nodes\":" << ir.size()
       << ",\"nonlinear\":" << b(f.hasNonlinear)
       << ",\"mixed_int_real\":" << b(f.hasMixedIntReal)
       << ",\"int\":" << b(f.hasInt)
       << ",\"real\":" << b(f.hasReal)
       << ",\"array\":" << b(f.hasArray)
       << ",\"uf\":" << b(f.hasUF)
       << ",\"bv\":" << b(f.hasBV)
       << ",\"datatype\":" << b(f.hasDatatype)
       << ",\"quantifier\":" << b(f.hasQuantifier)
       << "}\n";
}

} // namespace xolver
