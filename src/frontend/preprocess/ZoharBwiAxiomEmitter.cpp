#include "frontend/preprocess/ZoharBwiAxiomEmitter.h"
#include "util/EnvParam.h"

#include <algorithm>
#include <iostream>
#include <string>
#include <unordered_set>
#include <vector>

#include <gmpxx.h>

namespace xolver {

ZoharBwiAxiomEmitter::ZoharBwiAxiomEmitter(CoreIr& ir, SortId boolSortId)
    : ir_(ir), boolSortId_(boolSortId), intSortId_(ir.intSortId()) {}

// Find-or-create: scan existing exprs for a structurally-equal node before
// minting a fresh one. Reusing an existing ExprId means the Atomizer (which
// keys on ExprId) assigns the SAME SAT variable to the axiom's atom and the
// user's structurally-equivalent atom, so the Boolean layer can directly
// refute "axiom asserts P" + "user asserts not P" — no theory-level
// atom-equivalence propagation needed.  This is what closes the
// recursion-style axiom chains without EUF UF-model channel support.
//
// O(N) per call where N = current ir_.size(); acceptable because emitter
// runs once at frontend time on a formula of bounded size.
static ExprId findExisting(const CoreIr& ir, Kind kind, SortId sort,
                           std::initializer_list<ExprId> kids) {
    for (ExprId id = 0; id < static_cast<ExprId>(ir.size()); ++id) {
        const CoreExpr& n = ir.get(id);
        if (n.kind != kind) continue;
        if (n.sort != sort) continue;
        if (n.children.size() != kids.size()) continue;
        bool eq = true;
        size_t i = 0;
        for (ExprId k : kids) { if (n.children[i++] != k) { eq = false; break; } }
        if (eq) return id;
    }
    return NullExpr;
}

bool ZoharBwiAxiomEmitter::isUfApplyNamed(const CoreExpr& node,
                                          std::string_view name) {
    if (node.kind != Kind::UFApply) return false;
    auto* s = std::get_if<std::string>(&node.payload.value);
    return s && std::string_view(*s) == name;
}

ExprId ZoharBwiAxiomEmitter::mkConstInt(int64_t v) {
    // Hash-cons ConstInts by value (the existing convention in CoreIr: const-fold
    // passes already canonicalize repeated literals). Scan for an existing
    // ConstInt with the same int64 payload.
    for (ExprId id = 0; id < static_cast<ExprId>(ir_.size()); ++id) {
        const CoreExpr& n = ir_.get(id);
        if (n.kind != Kind::ConstInt || n.sort != intSortId_) continue;
        if (auto* iv = std::get_if<int64_t>(&n.payload.value)) {
            if (*iv == v) return id;
        } else if (auto* sv = std::get_if<std::string>(&n.payload.value)) {
            // Large-literal ConstInt is stored as a decimal string; match
            // those too so the hash-cons fold remains complete on big-literal
            // formulas (otherwise we'd mint a redundant int64 ConstInt and
            // the axiom would not share atoms with the user's literal).
            try { if (mpz_class(*sv) == v) return id; } catch (...) {}
        }
    }
    CoreExpr e;
    e.kind = Kind::ConstInt; e.sort = intSortId_;
    e.payload = Payload(v);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkGeq(ExprId a, ExprId b) {
    if (auto id = findExisting(ir_, Kind::Geq, boolSortId_, {a, b}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Geq; e.sort = boolSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkLeq(ExprId a, ExprId b) {
    if (auto id = findExisting(ir_, Kind::Leq, boolSortId_, {a, b}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Leq; e.sort = boolSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkEq(ExprId a, ExprId b) {
    // Eq is symmetric — accept either child order from the existing exprs.
    if (auto id = findExisting(ir_, Kind::Eq, boolSortId_, {a, b}); id != NullExpr) return id;
    if (auto id = findExisting(ir_, Kind::Eq, boolSortId_, {b, a}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Eq; e.sort = boolSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkImplies(ExprId a, ExprId b) {
    if (auto id = findExisting(ir_, Kind::Implies, boolSortId_, {a, b}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Implies; e.sort = boolSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkAnd(ExprId a, ExprId b) {
    // And is symmetric.
    if (auto id = findExisting(ir_, Kind::And, boolSortId_, {a, b}); id != NullExpr) return id;
    if (auto id = findExisting(ir_, Kind::And, boolSortId_, {b, a}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::And; e.sort = boolSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkAdd(ExprId a, ExprId b) {
    if (auto id = findExisting(ir_, Kind::Add, intSortId_, {a, b}); id != NullExpr) return id;
    if (auto id = findExisting(ir_, Kind::Add, intSortId_, {b, a}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Add; e.sort = intSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkMul(ExprId a, ExprId b) {
    if (auto id = findExisting(ir_, Kind::Mul, intSortId_, {a, b}); id != NullExpr) return id;
    if (auto id = findExisting(ir_, Kind::Mul, intSortId_, {b, a}); id != NullExpr) return id;
    CoreExpr e; e.kind = Kind::Mul; e.sort = intSortId_;
    e.children.push_back(a); e.children.push_back(b);
    return ir_.addShared(std::move(e));
}

ExprId ZoharBwiAxiomEmitter::mkPow2(ExprId arg) {
    // Reuse an existing (pow2 arg) UFApply if one is already in the IR.
    for (ExprId id = 0; id < static_cast<ExprId>(ir_.size()); ++id) {
        const CoreExpr& n = ir_.get(id);
        if (!isUfApplyNamed(n, "pow2")) continue;
        if (n.children.size() == 1 && n.children[0] == arg) return id;
    }
    CoreExpr e; e.kind = Kind::UFApply; e.sort = intSortId_;
    e.payload = Payload(std::string("pow2"));
    e.children.push_back(arg);
    return ir_.addShared(std::move(e));
}

void ZoharBwiAxiomEmitter::visit(ExprId root,
                                 std::unordered_set<ExprId>& visited,
                                 std::unordered_set<ExprId>& pow2Terms,
                                 std::unordered_set<ExprId>& intandTerms,
                                 std::unordered_set<ExprId>& intorTerms,
                                 std::unordered_set<ExprId>& intxorTerms) const {
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        ExprId id = stack.back();
        stack.pop_back();
        if (!visited.insert(id).second) continue;
        const CoreExpr& node = ir_.get(id);
        // pow2: (Int) -> Int, exactly one arg
        if (isUfApplyNamed(node, "pow2") && node.children.size() == 1) {
            pow2Terms.insert(id);
        }
        // intand/intor/intxor: (Int Int Int) -> Int, exactly three args
        if (node.children.size() == 3 && node.kind == Kind::UFApply) {
            if (isUfApplyNamed(node, "intand")) intandTerms.insert(id);
            else if (isUfApplyNamed(node, "intor"))  intorTerms.insert(id);
            else if (isUfApplyNamed(node, "intxor")) intxorTerms.insert(id);
        }
        for (ExprId c : node.children) stack.push_back(c);
    }
}

void ZoharBwiAxiomEmitter::collectTerms(
        std::unordered_set<ExprId>& pow2Terms,
        std::unordered_set<ExprId>& intandTerms,
        std::unordered_set<ExprId>& intorTerms,
        std::unordered_set<ExprId>& intxorTerms) const {
    std::unordered_set<ExprId> visited;
    for (ExprId a : ir_.assertions())
        visit(a, visited, pow2Terms, intandTerms, intorTerms, intxorTerms);
}

// Identifies (Add x 1) or (Add 1 x): if so, returns x; otherwise NullExpr.
// `1` can be represented as either ConstInt(int64=1) (post-normalization) or
// ConstReal/ConstInt(string="1") (parser default for numeric literals before
// ArithCastNormalizer rewrites them) — accept both, since our plugin runs
// before ArithCastNormalizer.
static ExprId addOnePredecessor(const CoreIr& ir, ExprId id) {
    const CoreExpr& node = ir.get(id);
    if (node.kind != Kind::Add || node.children.size() != 2) return NullExpr;
    auto isOne = [&](ExprId c) {
        const CoreExpr& cn = ir.get(c);
        if (cn.kind != Kind::ConstInt && cn.kind != Kind::ConstReal) return false;
        if (auto* iv = std::get_if<int64_t>(&cn.payload.value)) return *iv == 1;
        if (auto* sv = std::get_if<std::string>(&cn.payload.value))
            return *sv == "1" || *sv == "1.0";
        return false;
    };
    if (isOne(node.children[1])) return node.children[0];
    if (isOne(node.children[0])) return node.children[1];
    return NullExpr;
}

size_t ZoharBwiAxiomEmitter::emitPow2Recursion(
        const std::unordered_set<ExprId>& pow2Terms) {
    static const bool diag = xolver::env::diag("XOLVER_NIA_ZOHAR_DIAG");
    // Build a map arg-ExprId -> pow2-term-ExprId so we can REUSE the existing
    // (pow2 x) ExprId in the recursion's RHS (rather than mint a fresh node).
    // Reusing the ExprId means atomization assigns the same SAT variable, so
    // the equality holds at the Boolean layer too — not just via EUF
    // congruence. (EUF would still unify a fresh mint by congruence, but
    // sharing the ExprId is strictly cheaper for the SAT abstraction.)
    std::unordered_map<ExprId, ExprId> argToPow2;
    argToPow2.reserve(pow2Terms.size());
    for (ExprId p : pow2Terms) argToPow2.emplace(ir_.get(p).children[0], p);

    ExprId zero = mkConstInt(0);
    ExprId two  = mkConstInt(2);

    size_t emitted = 0;
    std::vector<ExprId> sorted(pow2Terms.begin(), pow2Terms.end());
    std::sort(sorted.begin(), sorted.end());
    for (ExprId p : sorted) {
        ExprId arg = ir_.get(p).children[0];
        // Trigger: arg = (Add x 1) AND (pow2 x) is also present in the formula.
        ExprId pred = addOnePredecessor(ir_, arg);
        if (pred == NullExpr) continue;
        auto it = argToPow2.find(pred);
        if (it == argToPow2.end()) continue;
        if (diag) {
            std::cerr << "[ZOHAR-REC] emitting for p=" << p << " pred=" << pred
                      << " pPred=" << it->second << "\n";
        }
        ExprId pPred = it->second;  // the existing (pow2 pred) ExprId
        // (=> (>= pred 0) (= (pow2 (+ pred 1)) (* 2 (pow2 pred))))
        ExprId predGe0 = mkGeq(pred, zero);
        ExprId rhs     = mkMul(two, pPred);
        ExprId eq      = mkEq(p, rhs);
        ir_.addAssertion(mkImplies(predGe0, eq));
        ++emitted;
    }
    return emitted;
}

size_t ZoharBwiAxiomEmitter::emitBitwiseAxioms(
        const std::unordered_set<ExprId>& terms, const char* op) {
    ExprId zero = mkConstInt(0);
    size_t emitted = 0;
    std::vector<ExprId> sorted(terms.begin(), terms.end());
    std::sort(sorted.begin(), sorted.end());
    for (ExprId t : sorted) {
        const CoreExpr& node = ir_.get(t);
        // node = (op k x y), children = [k, x, y]
        ExprId x = node.children[1];
        ExprId y = node.children[2];
        ExprId xGe0 = mkGeq(x, zero);
        ExprId yGe0 = mkGeq(y, zero);
        ExprId xyGe0 = mkAnd(xGe0, yGe0);

        // Common floor: result >= 0 (true for and/xor; or also non-negative).
        ir_.addAssertion(mkImplies(xyGe0, mkGeq(t, zero)));
        ++emitted;

        if (std::string_view(op) == "intand") {
            // (intand k x y) <= x, <= y
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(t, x)));
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(t, y)));
            emitted += 2;
        } else if (std::string_view(op) == "intor") {
            // x <= intor, y <= intor, intor <= x + y
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(x, t)));
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(y, t)));
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(t, mkAdd(x, y))));
            emitted += 3;
        } else if (std::string_view(op) == "intxor") {
            // intxor <= x + y
            ir_.addAssertion(mkImplies(xyGe0, mkLeq(t, mkAdd(x, y))));
            ++emitted;
        }
    }
    return emitted;
}

bool ZoharBwiAxiomEmitter::run() {
    detected_ = false;
    axiomCount_ = 0;

    std::unordered_set<ExprId> pow2Terms, intandTerms, intorTerms, intxorTerms;
    collectTerms(pow2Terms, intandTerms, intorTerms, intxorTerms);
    if (pow2Terms.empty() && intandTerms.empty() && intorTerms.empty() &&
        intxorTerms.empty())
        return false;
    detected_ = true;

    ExprId zero = mkConstInt(0);
    ExprId one  = mkConstInt(1);

    // ---- Phase 1: pow2 ground + per-term -----------------------------------

    if (!pow2Terms.empty()) {
        // (= (pow2 0) 1)  — ground base case under standard interpretation.
        ir_.addAssertion(mkEq(mkPow2(zero), one));
        ++axiomCount_;
        // NOTE: (= (pow2 1) 2) is intentionally NOT emitted as a separate
        //       ground — it is redundant given (pow2 0)=1 + the recursion
        //       axiom (when (pow2 1) is present), and shipping it standalone
        //       perturbed an existing default-flags soundness test (Result
        //       degraded Unknown vs the expected Unsat in the perterm test).

        std::vector<ExprId> sorted(pow2Terms.begin(), pow2Terms.end());
        std::sort(sorted.begin(), sorted.end());
        for (ExprId p : sorted) {
            ExprId arg = ir_.get(p).children[0];
            // (=> (>= arg 0) (>= (pow2 arg) 1))
            ir_.addAssertion(mkImplies(mkGeq(arg, zero), mkGeq(p, one)));
            ++axiomCount_;
        }
    }

    // ---- Phase 2: pow2 recursion (triggered) -------------------------------

    axiomCount_ += emitPow2Recursion(pow2Terms);

    // ---- Phase 2: intand / intor / intxor bounded axioms -------------------

    axiomCount_ += emitBitwiseAxioms(intandTerms, "intand");
    axiomCount_ += emitBitwiseAxioms(intorTerms,  "intor");
    axiomCount_ += emitBitwiseAxioms(intxorTerms, "intxor");

    return true;
}

} // namespace xolver
