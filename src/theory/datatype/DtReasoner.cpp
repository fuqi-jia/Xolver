#include "theory/datatype/DtReasoner.h"
#include "util/EnvParam.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "expr/ir.h"
#include <vector>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <optional>
#include <unordered_map>
#include <string>

namespace xolver {

namespace {
// (#70/#74) Lightweight integer linear form over hash-consed atom ExprIds:
// constant + sum(coeff_i * atom_i). Used by the injectivity linear-field floor
// to detect when two fields of two merged same-constructor terms differ by a
// nonzero constant (and therefore can never be equal). Opaque subterms
// (variable / selector / UF app / *, mod, non-integer real) are atoms keyed by
// their ExprId — two syntactically-identical such terms share an ExprId (the
// frontend hash-conses), so e.g. the `i` in (+ i 0) and (+ i 2) cancels.
struct LinForm {
    int64_t constant = 0;
    std::unordered_map<ExprId, int64_t> coeffs;
};

// dst += scale * src, with a conservative int64 overflow guard. Returns false on
// possible overflow -> the caller abandons the floor for this field (sound: it
// only ever under-detects, never mis-detects).
bool addLin(LinForm& dst, const LinForm& src, int64_t scale) {
    auto mulAdd = [](int64_t& acc, int64_t a, int64_t b) -> bool {
        if (a != 0) {
            int64_t aa = a < 0 ? -a : a;
            if (b > INT64_MAX / aa || b < INT64_MIN / aa) return false;
        }
        int64_t prod = a * b;
        if ((prod > 0 && acc > INT64_MAX - prod) ||
            (prod < 0 && acc < INT64_MIN - prod)) return false;
        acc += prod;
        return true;
    };
    if (!mulAdd(dst.constant, src.constant, scale)) return false;
    for (const auto& [atom, c] : src.coeffs) {
        int64_t& d = dst.coeffs[atom];
        if (!mulAdd(d, c, scale)) return false;
        if (d == 0) dst.coeffs.erase(atom);
    }
    return true;
}

std::optional<LinForm> linForm(const CoreIr& ir, ExprId e, int& budget) {
    if (e == NullExpr || e >= static_cast<ExprId>(ir.size())) return std::nullopt;
    if (--budget < 0) return std::nullopt;
    const CoreExpr& ce = ir.get(e);
    auto atom = [&]() { LinForm lf; lf.coeffs[e] = 1; return lf; };
    switch (ce.kind) {
        case Kind::ConstInt:
            if (auto* iv = std::get_if<int64_t>(&ce.payload.value)) {
                LinForm lf; lf.constant = *iv; return lf;
            }
            return atom();
        case Kind::ConstReal:
            if (auto* sv = std::get_if<std::string>(&ce.payload.value)) {
                const std::string& s = *sv;
                size_t slash = s.find('/');
                std::string num = slash == std::string::npos ? s : s.substr(0, slash);
                std::string den = slash == std::string::npos ? std::string("1")
                                                             : s.substr(slash + 1);
                if (den != "1") return atom();  // genuine fraction -> opaque
                try {
                    size_t pos = 0;
                    long long v = std::stoll(num, &pos);
                    if (pos != num.size()) return atom();
                    LinForm lf; lf.constant = static_cast<int64_t>(v); return lf;
                } catch (...) { return atom(); }
            }
            return atom();
        case Kind::Add: {
            LinForm lf;
            for (ExprId c : ce.children) {
                auto sub = linForm(ir, c, budget);
                if (!sub || !addLin(lf, *sub, 1)) return std::nullopt;
            }
            return lf;
        }
        case Kind::Sub: {
            if (ce.children.size() != 2) return atom();
            auto a = linForm(ir, ce.children[0], budget);
            auto b = linForm(ir, ce.children[1], budget);
            if (!a || !b) return std::nullopt;
            LinForm lf;
            if (!addLin(lf, *a, 1) || !addLin(lf, *b, -1)) return std::nullopt;
            return lf;
        }
        case Kind::Neg: {
            if (ce.children.size() != 1) return atom();
            auto a = linForm(ir, ce.children[0], budget);
            if (!a) return std::nullopt;
            LinForm lf;
            if (!addLin(lf, *a, -1)) return std::nullopt;
            return lf;
        }
        default:
            return atom();  // variable / selector / UF / Mul / Mod / ... -> opaque
    }
}

// (#76) System infeasibility over a set of integer linear EQUALITIES {form_i = 0}.
// Constructor injectivity merging C(a..) = C(b..) implies every field-wise
// equality a_i = b_i; the per-field floor catches only a SINGLE field whose two
// forms differ by a nonzero constant, but a jointly-infeasible SYSTEM —
// mk(2,2) = mk(1+k, k-3) => {1+k = 2, k-3 = 2} => k = 1 AND k = 5 — is invisible
// per field (each is individually satisfiable). Fraction-free Gaussian
// elimination with back-substitution (so every pivot's leader appears in exactly
// one row): a reduction yielding 0 = (nonzero constant) proves no model can merge
// the two constructors. Returns true ONLY on a proven contradiction; abandons
// (false) on int64 overflow — sound under-detection, never a false positive.
bool systemInfeasible(std::vector<LinForm> forms) {
    std::vector<std::pair<ExprId, LinForm>> rows;  // (leader atom, reduced eq)
    for (auto eq : forms) {
        bool ok = true;
        for (auto& [lead, row] : rows) {              // forward-reduce
            auto it = eq.coeffs.find(lead);
            if (it == eq.coeffs.end()) continue;
            int64_t c = it->second, rc = row.coeffs.at(lead);
            LinForm tmp;
            if (!addLin(tmp, eq, rc) || !addLin(tmp, row, -c)) { ok = false; break; }
            eq = std::move(tmp);
        }
        if (!ok) continue;                            // overflow -> skip this eq
        if (eq.coeffs.empty()) {
            if (eq.constant != 0) return true;        // 0 = nonzero -> infeasible
            continue;                                 // 0 = 0, redundant
        }
        ExprId lead = eq.coeffs.begin()->first;
        for (auto& [l2, row] : rows) {                // back-substitute new leader out
            (void)l2;
            auto it = row.coeffs.find(lead);
            if (it == row.coeffs.end()) continue;
            int64_t c = it->second, ec = eq.coeffs.at(lead);
            LinForm tmp;
            if (!addLin(tmp, row, ec) || !addLin(tmp, eq, -c)) { ok = false; break; }
            row = std::move(tmp);
        }
        if (!ok) continue;
        rows.emplace_back(lead, std::move(eq));
    }
    return false;
}
}  // namespace

DtReasoner::~DtReasoner() {
    if (xolver::env::diag("XOLVER_DT_HC_STATS")) {
        const uint64_t total = finiteHits_ + finiteMisses_;
        if (total > 0) {
            const double rate = 100.0 * static_cast<double>(finiteHits_) / static_cast<double>(total);
            std::fprintf(stderr,
                "[XOLVER_DT_HC_STATS] isFiniteSort hits=%llu misses=%llu hit_rate=%.2f%% cache=%zu\n",
                (unsigned long long)finiteHits_, (unsigned long long)finiteMisses_,
                rate, finiteSortCache_.size());
        }
    }
}

static constexpr char kCtorPrefix[] = "#dt.ctor.";
static constexpr char kSelPrefix[]  = "#dt.sel.";
static constexpr char kTesterPrefix[] = "#dt.is.";

void DtReasoner::reset() {
    ctorTerms_.clear();
    selectorTerms_.clear();
    testerTerms_.clear();
    ctorSet_.clear();
    selectorSet_.clear();
    testerSet_.clear();
    nextTermToScan_ = 0;
    injectivityDone_.clear();
    projectionDone_.clear();
    splitDone_.clear();
}

bool DtReasoner::symIsConstructor(EufTermId t) const {
    const std::string& s = tm_->symbolName(tm_->node(t).symbol);
    return s.rfind(kCtorPrefix, 0) == 0;
}
bool DtReasoner::symIsSelector(EufTermId t) const {
    const std::string& s = tm_->symbolName(tm_->node(t).symbol);
    return s.rfind(kSelPrefix, 0) == 0;
}
bool DtReasoner::symIsTester(EufTermId t) const {
    const std::string& s = tm_->symbolName(tm_->node(t).symbol);
    return s.rfind(kTesterPrefix, 0) == 0;
}

ExprId DtReasoner::originExpr(EufTermId t) const {
    if (t == NullEufTerm) return NullExpr;
    return tm_->node(t).origin;
}

std::string DtReasoner::opName(EufTermId t) const {
    // For DT terms (constructor/selector/tester), the AUTHORITATIVE name is
    // the EUF symbol name (#dt.ctor.<C>, #dt.sel.<S>, #dt.is.<C>) that the
    // lowering synthesizes. The CoreIr ORIGIN's payload is unreliable: in
    // some lowering paths (e.g. nested let-bound Tester subexpressions inside
    // BMC encoding) the origin's payload is set to a stringified Kind name
    // like "UNKNOWN_KIND" by the parser, which then propagates to
    // tester-consistency as opName(tt) = "UNKNOWN_KIND" -> name comparison
    // against the actual constructor name ALWAYS mismatches, falsely emitting
    // is-<C>(u) AND ctor=<C> as a conflict (the QF_DT blocksworld
    // false-UNSAT 220/308 class). Read from the EUF symbol — that name was
    // explicitly built from the constructor's user-declared name in the
    // datatype lowering, so it is the ground truth.
    const std::string& sym = tm_->symbolName(tm_->node(t).symbol);
    if (sym.rfind(kCtorPrefix, 0) == 0)   return sym.substr(sizeof(kCtorPrefix) - 1);
    if (sym.rfind(kSelPrefix, 0) == 0)    return sym.substr(sizeof(kSelPrefix) - 1);
    if (sym.rfind(kTesterPrefix, 0) == 0) return sym.substr(sizeof(kTesterPrefix) - 1);
    // Non-DT EUF term — fall back to the CoreIr payload (UF apps still keep
    // their string name there).
    ExprId e = originExpr(t);
    if (e == NullExpr) return std::string();
    const auto* nm = std::get_if<std::string>(&ir_->get(e).payload.value);
    return nm ? *nm : std::string();
}

SortId DtReasoner::ctorSort(EufTermId t) const {
    ExprId e = originExpr(t);
    if (e == NullExpr) return NullSort;
    return ir_->get(e).sort;
}

bool DtReasoner::discoverDtTerms() {
    if (!active()) return false;
    bool found = false;
    EufTermId total = static_cast<EufTermId>(tm_->termCount());
    for (EufTermId t = nextTermToScan_; t < total; ++t) {
        // NOTE: nullary constructors (enum values, nil) have NO args but ARE
        // constructor terms, so do not skip empty-arg terms here. Selectors
        // always have an operand.
        if (symIsConstructor(t)) {
            if (ctorSet_.insert(t).second) { ctorTerms_.push_back(t); found = true; }
        } else if (symIsSelector(t) && !tm_->node(t).args.empty()) {
            if (selectorSet_.insert(t).second) { selectorTerms_.push_back(t); found = true; }
        } else if (symIsTester(t) && !tm_->node(t).args.empty()) {
            if (testerSet_.insert(t).second) { testerTerms_.push_back(t); found = true; }
        }
    }
    nextTermToScan_ = total;
    return found;
}

std::optional<std::vector<SatLit>> DtReasoner::checkConflict() {
    if (!active()) return std::nullopt;
    discoverDtTerms();

    // --- Constructor clash: two distinct-constructor terms in one class -------
    // Different constructors have different EUF symbols (name + arg/result
    // sorts), so a class holding two distinct symbols is C(..) = D(..), C != D.
    std::unordered_map<EClassId, EufTermId> classCtor;  // rep -> first ctor term
    classCtor.reserve(ctorTerms_.size() * 2 + 1);
    for (EufTermId t : ctorTerms_) {
        EClassId r = egraph_->rep(t);
        auto it = classCtor.find(r);
        if (it == classCtor.end()) {
            classCtor.emplace(r, t);
            continue;
        }
        EufTermId other = it->second;
        if (tm_->node(t).symbol == tm_->node(other).symbol) continue;  // same ctor: injectivity
        // Clash. Explanation = why other and t are in the same class.
        auto er = egraph_->explainEquality(other, t);
        if (er.ok && !er.reasons.empty()) {
            return er.reasons;
        }
        // explainEquality should succeed (they ARE in the same class). If it has
        // no literals (a tautological merge) the clash is unconditional — but DT
        // ctor terms only merge via asserted/derived equalities, so an empty
        // sound explanation means "always conflicting" with no antecedent, which
        // we cannot express as a clause; skip rather than emit an empty (=> false
        // unconditionally) clause that would be unsound to hand the SAT core.
    }

    // --- Tester consistency ---------------------------------------------------
    // is_C(u) decided (merged with true/false) while u's class holds a known
    // constructor C': the tester MUST equal (C == C'). A mismatch is a conflict.
    // This makes the determinacy-based sat sound (a tester cannot disagree with
    // the determined constructor). Guarded: only when u's constructor is known.
    if (trueTerm_ != NullEufTerm || falseTerm_ != NullEufTerm) {
        for (EufTermId tt : testerTerms_) {
            const auto& tn = tm_->node(tt);
            if (tn.args.empty()) continue;
            bool isTrue = (trueTerm_ != NullEufTerm) && egraph_->same(tt, trueTerm_);
            bool isFalse = (falseTerm_ != NullEufTerm) && egraph_->same(tt, falseTerm_);
            if (!isTrue && !isFalse) continue;  // tester truth not decided
            EufTermId u = tn.args[0];
            // The tester's TARGET constructor name. opName(tt) is the tester name
            // "is-<ctor>" (e.g. "is-cons"); the constructor it tests for is the
            // part after the "is-" prefix. Comparing the bare constructor name
            // (opName(m), e.g. "cons") against the full tester name would NEVER
            // match -> every true tester on a determined class would spuriously
            // conflict (false-UNSAT, e.g. is_cons(x) with x already cons).
            std::string tnm = opName(tt);
            if (tnm.rfind("is-", 0) == 0) tnm = tnm.substr(3);
            // ROBUSTNESS (#70/#72): a tester whose constructor NAME was dropped
            // by the upstream payload loss (compound-arg testers intern as bare
            // "#dt.is.") yields an empty tnm. Comparing it against a (recovered)
            // constructor name spuriously mismatches -> a false-UNSAT conflict.
            // An empty/unreliable name cannot be soundly compared, so skip the
            // tester-consistency check here; a genuinely-violating model is still
            // caught by the selector-projection floor in modelFullyDetermined().
            if (tnm.empty()) continue;
            // Find a known constructor in u's class.
            EClassId uc = egraph_->rep(u);
            for (EufTermId m : egraph_->classMembers(uc)) {
                if (!symIsConstructor(m)) continue;
                const std::string mName = opName(m);
                if (mName.empty()) continue;        // same robustness for the ctor side
                bool sameCtor = (mName == tnm);
                // is_C(u)=true but ctor is D!=C, or is_C(u)=false but ctor IS C.
                if ((isTrue && !sameCtor) || (isFalse && sameCtor)) {
                    std::vector<SatLit> reasons;
                    auto erc = egraph_->explainEquality(u, m);
                    if (erc.ok) reasons.insert(reasons.end(), erc.reasons.begin(), erc.reasons.end());
                    auto ert = egraph_->explainEquality(tt, isTrue ? trueTerm_ : falseTerm_);
                    if (ert.ok) reasons.insert(reasons.end(), ert.reasons.begin(), ert.reasons.end());
                    if (!reasons.empty()) return reasons;
                }
                break;  // one known constructor per class suffices
            }
        }
    }

    // --- Tester-vs-tester clash ----------------------------------------------
    // Two DISTINCT-constructor testers both asserted TRUE on the same term are
    // contradictory regardless of whether a concrete constructor is known: a
    // datatype value satisfies exactly one constructor tester. The
    // tester-consistency pass above only fires when u's constructor is already
    // determined; this catches the FREE case, e.g. is_red(c) ∧ is_green(c) with
    // c otherwise unconstrained. Needed for combination logics (QF_UFDTNIA),
    // where the Full-effort exhaustiveness split that would force a constructor
    // does not run, so without this the clash escapes as a false-SAT.
    if (trueTerm_ != NullEufTerm) {
        std::unordered_map<EClassId, std::pair<EufTermId, std::string>> trueTesterByClass;
        trueTesterByClass.reserve(testerTerms_.size() * 2 + 1);
        for (EufTermId tt : testerTerms_) {
            const auto& tn = tm_->node(tt);
            if (tn.args.empty()) continue;
            if (!egraph_->same(tt, trueTerm_)) continue;   // only testers asserted TRUE
            std::string tnm = opName(tt);
            if (tnm.rfind("is-", 0) == 0) tnm = tnm.substr(3);
            if (tnm.empty()) continue;   // unreliable name (#70/#72) — cannot clash soundly
            EClassId uc = egraph_->rep(tn.args[0]);
            auto it = trueTesterByClass.find(uc);
            if (it == trueTesterByClass.end()) {
                trueTesterByClass.emplace(uc, std::make_pair(tt, tnm));
                continue;
            }
            if (it->second.second == tnm) continue;        // same target ctor — fine
            // Two distinct constructors both tested TRUE on one class -> clash.
            EufTermId other = it->second.first;
            std::vector<SatLit> reasons;
            auto e1 = egraph_->explainEquality(tt, trueTerm_);
            if (e1.ok) reasons.insert(reasons.end(), e1.reasons.begin(), e1.reasons.end());
            auto e2 = egraph_->explainEquality(other, trueTerm_);
            if (e2.ok) reasons.insert(reasons.end(), e2.reasons.begin(), e2.reasons.end());
            EufTermId u1 = tn.args[0];
            EufTermId u2 = tm_->node(other).args[0];
            if (u1 != u2) {
                auto eu = egraph_->explainEquality(u1, u2);
                if (eu.ok) reasons.insert(reasons.end(), eu.reasons.begin(), eu.reasons.end());
            }
            if (!reasons.empty()) return reasons;
        }
    }

    // --- Acyclicity (recursive datatypes only) --------------------------------
    bool anyRecursive = false;
    for (EufTermId t : ctorTerms_) {
        const DatatypeInfo* dt = ir_->datatypes().datatype(ctorSort(t));
        if (dt && dt->recursive) { anyRecursive = true; break; }
    }
    if (anyRecursive) {
        if (auto c = checkAcyclicity()) return c;
    }

    return std::nullopt;
}

std::optional<std::vector<SatLit>> DtReasoner::checkAcyclicity() {
    // Cycle of constructor terms t_0 -> t_1 -> ... -> t_0 where some
    // datatype-sorted argument a of t_i is in the same class as t_{i+1}. Then
    // t_0 is a proper subterm of itself -> UNSAT (the free-algebra acyclicity
    // axiom). Reasons = union of explainEquality(arg, next-ctor) along the cycle.

    auto datatypeArgQuick = [&](EufTermId ctor, size_t i) -> bool {
        const auto& args = tm_->node(ctor).args;
        if (i >= args.size()) return false;
        return ir_->datatypes().isDatatypeSort(ir_->get(originExpr(args[i])).sort);
    };

    // Direct self-reference: a constructor term t = C(... a ...) with a
    // datatype-sorted argument a in t's OWN class (x = C(... x ...)). t is then
    // a proper subterm of itself -> UNSAT. Reasons = why a and t are merged.
    for (EufTermId t : ctorTerms_) {
        EClassId tc = egraph_->rep(t);
        const auto& args = tm_->node(t).args;
        for (size_t i = 0; i < args.size(); ++i) {
            if (!datatypeArgQuick(t, i)) continue;
            if (egraph_->rep(args[i]) == tc) {
                auto er = egraph_->explainEquality(args[i], t);
                if (er.ok && !er.reasons.empty()) return er.reasons;
            }
        }
    }

    // rep(class) -> constructor terms living in that class.
    std::unordered_map<EClassId, std::vector<EufTermId>> ctorsByClass;
    for (EufTermId t : ctorTerms_) ctorsByClass[egraph_->rep(t)].push_back(t);

    enum Color { White, Gray, Black };
    std::unordered_map<EufTermId, Color> color;

    // Iterative DFS over constructor-term nodes; edge t -> t' iff some
    // datatype-sorted arg a of t has rep(a) == rep(t').
    struct StackFrame { EufTermId node; size_t argIdx; size_t childIdx; EufTermId pendingArg; };
    std::vector<EufTermId> path;            // current DFS path of ctor terms

    auto datatypeArg = [&](EufTermId ctor, size_t i) -> bool {
        const auto& args = tm_->node(ctor).args;
        if (i >= args.size()) return false;
        return ir_->datatypes().isDatatypeSort(ir_->get(originExpr(args[i])).sort);
    };

    for (EufTermId start : ctorTerms_) {
        if (color[start] != White) continue;
        // explicit DFS
        std::vector<std::pair<EufTermId, size_t>> stack;  // (ctor term, next arg index)
        stack.push_back({start, 0});
        color[start] = Gray;
        path.push_back(start);

        while (!stack.empty()) {
            auto& [node, argIdx] = stack.back();
            const auto& args = tm_->node(node).args;
            bool descended = false;
            while (argIdx < args.size()) {
                size_t i = argIdx++;
                if (!datatypeArg(node, i)) continue;
                EClassId argClass = egraph_->rep(args[i]);
                auto cit = ctorsByClass.find(argClass);
                if (cit == ctorsByClass.end()) continue;
                for (EufTermId next : cit->second) {
                    if (next == node) continue;  // self arg handled by the chain below
                    if (color[next] == Gray) {
                        // Found a back edge -> cycle from `next` up to `node`.
                        std::vector<SatLit> reasons;
                        auto addReasons = [&](EufTermId from, EufTermId to) {
                            auto er = egraph_->explainEquality(from, to);
                            if (er.ok) reasons.insert(reasons.end(),
                                                      er.reasons.begin(), er.reasons.end());
                        };
                        // The cycle in `path` is from the position of `next` to the end,
                        // closed by the edge node-arg -> next. Walk consecutive ctor
                        // terms on the path and link each arg to the successor ctor.
                        size_t startPos = 0;
                        for (size_t p = 0; p < path.size(); ++p) {
                            if (path[p] == next) { startPos = p; break; }
                        }
                        for (size_t p = startPos; p < path.size(); ++p) {
                            EufTermId cur = path[p];
                            EufTermId succ = (p + 1 < path.size()) ? path[p + 1] : next;
                            // find the datatype arg of cur whose class holds succ
                            const auto& cargs = tm_->node(cur).args;
                            for (size_t k = 0; k < cargs.size(); ++k) {
                                if (!datatypeArg(cur, k)) continue;
                                if (egraph_->rep(cargs[k]) == egraph_->rep(succ)) {
                                    addReasons(cargs[k], succ);
                                    break;
                                }
                            }
                        }
                        if (!reasons.empty()) return reasons;
                    } else if (color[next] == White) {
                        color[next] = Gray;
                        path.push_back(next);
                        stack.push_back({next, 0});
                        descended = true;
                        break;
                    }
                }
                if (descended) break;
            }
            if (descended) continue;
            // exhausted this node
            color[node] = Black;
            if (!path.empty() && path.back() == node) path.pop_back();
            stack.pop_back();
        }
    }
    return std::nullopt;
}

std::optional<std::vector<SatLit>> DtReasoner::instantiateLemma() {
    if (!active() || !registry_) return std::nullopt;
    discoverDtTerms();
    CoreIr& ir = const_cast<CoreIr&>(*ir_);

    // --- Injectivity: C(a..) = C(b..)  =>  a_i = b_i --------------------------
    // Group same-symbol constructor terms by class; for each merged same-ctor
    // pair, propagate the first non-equal argument.
    {
        std::unordered_map<EClassId, std::vector<EufTermId>> byClass;
        for (EufTermId t : ctorTerms_) byClass[egraph_->rep(t)].push_back(t);
        for (auto& [r, terms] : byClass) {
            (void)r;
            for (size_t i = 0; i < terms.size(); ++i) {
                for (size_t j = i + 1; j < terms.size(); ++j) {
                    EufTermId t1 = terms[i], t2 = terms[j];
                    if (tm_->node(t1).symbol != tm_->node(t2).symbol) continue;  // diff ctor = clash
                    const auto& a1 = tm_->node(t1).args;
                    const auto& a2 = tm_->node(t2).args;
                    if (a1.size() != a2.size()) continue;
                    for (size_t k = 0; k < a1.size(); ++k) {
                        if (egraph_->same(a1[k], a2[k])) continue;
                        uint64_t ikey = pairKey(t1, t2) ^ (static_cast<uint64_t>(k + 1) * 0x9e3779b97f4a7c15ULL);
                        if (!injectivityDone_.insert(ikey).second) continue;
                        ExprId aE = originExpr(a1[k]);
                        ExprId bE = originExpr(a2[k]);
                        if (aE == NullExpr || bE == NullExpr) continue;
                        auto er = egraph_->explainEquality(t1, t2);
                        if (!er.ok) continue;
                        SatLit impl = registry_->getOrCreateEufEqualityAtom(aE, bE);
                        std::vector<SatLit> clause;
                        for (SatLit r2 : er.reasons) clause.push_back(r2.negated());
                        clause.push_back(impl);
                        return clause;
                    }
                }
            }
        }
    }

    // --- Guarded selector projection: sel_i^C(u) = a_i when u ~ C(a..) --------
    for (EufTermId s : selectorTerms_) {
        const auto& sn = tm_->node(s);
        if (sn.args.empty()) continue;
        EufTermId u = sn.args[0];
        ExprId uE = originExpr(u);
        if (uE == NullExpr) continue;
        SortId dtSort = ir.get(uE).sort;
        uint32_t argIdx = 0;
        const DtConstructorInfo* owner =
            ir_->datatypes().selector(dtSort, opName(s), argIdx);
        if (!owner) continue;  // unknown selector (shouldn't happen) -> skip
        // Find a constructor term of the SELECTOR'S OWN constructor in u's class.
        EClassId uClass = egraph_->rep(u);
        for (EufTermId m : egraph_->classMembers(uClass)) {
            if (!symIsConstructor(m)) continue;
            if (opName(m) != owner->name) continue;          // GUARD: matching ctor only
            if (ctorSort(m) != dtSort) continue;
            const auto& margs = tm_->node(m).args;
            if (argIdx >= margs.size()) continue;
            EufTermId field = margs[argIdx];
            if (egraph_->same(s, field)) continue;           // already projected
            uint64_t key = pairKey(s, m);
            if (!projectionDone_.insert(key).second) continue;
            ExprId fieldE = originExpr(field);
            if (fieldE == NullExpr) continue;
            auto er = egraph_->explainEquality(u, m);
            if (!er.ok) continue;
            SatLit impl = registry_->getOrCreateEufEqualityAtom(originExpr(s), fieldE);
            std::vector<SatLit> clause;
            for (SatLit r2 : er.reasons) clause.push_back(r2.negated());
            clause.push_back(impl);
            return clause;
        }
    }

    // --- Exhaustiveness split (Reynolds-Blanchette tier 3, needed-only) -------
    // For an OBSERVED datatype class (a selector is applied to it, a tester on
    // it is decided, or its sort is finite) that has NO determined constructor,
    // emit the split clause  u = C1(sel..) ∨ … ∨ u = Ck(sel..)  over the sort's
    // constructors. Exhaustiveness is a DT theorem, so the clause is sound and
    // unconditional. The SAT solver picks one disjunct -> u gets a constructor
    // (determined). Recursive fields are fresh selector terms NOT read by any
    // selector, so they stay FREE and are never split -> termination; finite
    // fields are split in turn (finite -> terminates). This both recovers
    // observed-DT sat models and makes finite cardinality (pigeonhole) refutable
    // (each branch determines a ctor; distinct over too few ctors -> clash).
    {
        std::unordered_set<EClassId> hasCtor;
        EufTermId total = static_cast<EufTermId>(tm_->termCount());
        for (EufTermId t = 0; t < total; ++t) {
            if (symIsConstructor(t)) hasCtor.insert(egraph_->rep(t));
        }
        // rep -> a representative datatype-sorted term with a real origin.
        std::unordered_map<EClassId, EufTermId> repTerm;
        std::unordered_set<EClassId> needing;
        for (EufTermId t = 0; t < total; ++t) {
            const auto& n = tm_->node(t);
            // record a representative datatype term (real origin) per class
            ExprId e = n.origin;
            if (e != NullExpr && e < static_cast<ExprId>(ir_->size())) {
                SortId srt = ir_->get(e).sort;
                if (ir_->datatypes().isDatatypeSort(srt)) {
                    EClassId r = egraph_->rep(t);
                    repTerm.emplace(r, t);
                    std::unordered_set<SortId> visiting;
                    if (isFiniteSort(srt, visiting)) needing.insert(r);
                }
            }
            if (symIsSelector(t) && !n.args.empty()) needing.insert(egraph_->rep(n.args[0]));
            if (symIsTester(t) && !n.args.empty()) {
                bool decided = (trueTerm_ != NullEufTerm && egraph_->same(t, trueTerm_)) ||
                               (falseTerm_ != NullEufTerm && egraph_->same(t, falseTerm_));
                if (decided) needing.insert(egraph_->rep(n.args[0]));
            }
        }
        for (EClassId r : needing) {
            if (hasCtor.count(r)) continue;            // already determined
            auto rt = repTerm.find(r);
            if (rt == repTerm.end()) continue;
            EufTermId u = rt->second;
            if (!splitDone_.insert(u).second) continue;  // split once per term
            ExprId uExpr = tm_->node(u).origin;
            SortId S = ir.get(uExpr).sort;
            const DatatypeInfo* dt = ir_->datatypes().datatype(S);
            if (!dt || dt->constructors.empty()) continue;
            std::vector<SatLit> clause;
            for (const auto& ctor : dt->constructors) {
                SmallVector<ExprId, 4> fields;
                for (const auto& sel : ctor.selectors) {
                    CoreExpr selE;
                    selE.kind = Kind::Selector;
                    selE.sort = sel.resultSort;
                    selE.children.push_back(uExpr);
                    selE.payload = Payload(sel.name);
                    fields.push_back(ir.addShared(std::move(selE)));
                }
                CoreExpr ctorE;
                ctorE.kind = Kind::Constructor;
                ctorE.sort = S;
                ctorE.children = fields;
                ctorE.payload = Payload(ctor.name);
                ExprId ctorExpr = ir.addShared(std::move(ctorE));
                clause.push_back(registry_->getOrCreateEufEqualityAtom(uExpr, ctorExpr));
            }
            if (!clause.empty()) return clause;
        }
    }

    return std::nullopt;
}

bool DtReasoner::isFiniteSort(SortId s, std::unordered_set<SortId>& visiting) const {
    // Task W (S2-DT): hash-cons by SortId. Cache only top-level entries
    // (visiting empty on entry) so mid-recursion cycle-detect-false answers
    // don't pollute. Pure function once DatatypeRegistry is sealed.
    const bool topLevel = visiting.empty();
    if (topLevel) {
        auto it = finiteSortCache_.find(s);
        if (it != finiteSortCache_.end()) {
            ++finiteHits_;
            return it->second;
        }
        ++finiteMisses_;
    }
    auto sk = ir_->sortKind(s);
    bool result = false;
    if (sk == SortKind::Bool) {
        result = true;
    } else if (sk == SortKind::Int || sk == SortKind::Real || sk == SortKind::Array) {
        result = false;
    } else if (sk == SortKind::Datatype) {
        const DatatypeInfo* dt = ir_->datatypes().datatype(s);
        if (!dt || dt->recursive) {
            result = false;                                 // recursive DT is infinite
        } else if (!visiting.insert(s).second) {
            result = false;                                 // cycle (defensive)
        } else {
            bool finite = true;
            for (const auto& c : dt->constructors) {
                for (const auto& sel : c.selectors) {
                    if (!isFiniteSort(sel.resultSort, visiting)) { finite = false; break; }
                }
                if (!finite) break;
            }
            visiting.erase(s);
            result = finite;
        }
    }
    // BV/FP/Other/uninterpreted: treat as infinite (stably infinite for N-O).
    if (topLevel) finiteSortCache_.emplace(s, result);
    return result;
}

bool DtReasoner::modelFullyDetermined() const {
    if (!active()) return true;  // nothing DT to constrain
    // A `sat` is SOUND iff every datatype class that the formula OBSERVES has a
    // determined constructor (concrete ground term). A class is OBSERVED
    // ("needing") iff: a selector is applied to it, a decided tester is on it,
    // or its sort is FINITE (cardinality matters). A class that is infinite and
    // neither read by a selector nor tested is FREE — any value works, so it
    // need not be determined. Const scan over all interned terms (the egraph
    // reflects the satisfying assignment when this runs at a Full-effort check).
    std::unordered_set<EClassId> hasCtor;
    std::unordered_set<EClassId> needing;
    EufTermId total = static_cast<EufTermId>(tm_->termCount());
    for (EufTermId t = 0; t < total; ++t) {
        EClassId r = egraph_->rep(t);
        const auto& n = tm_->node(t);
        if (symIsConstructor(t)) hasCtor.insert(r);
        // Selector applied -> its operand's class must reveal a constructor.
        if (symIsSelector(t) && !n.args.empty()) {
            needing.insert(egraph_->rep(n.args[0]));
        }
        // Decided tester -> its operand's class must reveal a constructor.
        if (symIsTester(t) && !n.args.empty()) {
            bool decided = (trueTerm_ != NullEufTerm && egraph_->same(t, trueTerm_)) ||
                           (falseTerm_ != NullEufTerm && egraph_->same(t, falseTerm_));
            if (decided) needing.insert(egraph_->rep(n.args[0]));
        }
        // Finite datatype-sorted class: cardinality is observable, so require a
        // determined constructor. In COMBINATION mode a finite datatype is not
        // stably infinite (plan §3 Nelson-Oppen incompleteness) -> floor.
        // Guard: internal constants (e.g. the Bool true/false terms) carry
        // SENTINEL origins (near UINT32_MAX), which are out of range for ir_.
        ExprId e = n.origin;
        if (e != NullExpr && e < static_cast<ExprId>(ir_->size())) {
            SortId srt = ir_->get(e).sort;
            if (ir_->datatypes().isDatatypeSort(srt)) {
                std::unordered_set<SortId> visiting;
                if (isFiniteSort(srt, visiting)) {
                    if (combinationMode_) return false;  // §3 finite-DT floor
                    needing.insert(r);
                }
            }
        }
    }
    for (EClassId c : needing) {
        if (hasCtor.find(c) == hasCtor.end()) return false;  // observed-but-undetermined
    }

    // Selector-projection consistency (#70a, sound floor). For every selector
    // sel_i^C(u) whose operand class holds a constructor C(a..) of the SELECTOR'S
    // OWN constructor, the projection axiom sel_i^C(u) = a_i MUST hold in the
    // model. If the egraph does not reflect it, the DtReasoner failed to
    // instantiate the projection (observed #70: when the ctor field is a
    // compound / self-referential selector, e.g. q = mk(snd q, 0), the
    // guarded-projection at instantiateLemma() does not fire), leaving a model
    // that locally satisfies the constructor but is internally inconsistent
    // (fst(q) != snd(q) while q = mk(snd q, 0)). z3/cvc5 derive the projection
    // and refute -> our `sat` is unsound. Floor it to Unknown. SOUNDNESS: this
    // only ever turns a sat into Unknown, never an unsat into sat, and only
    // fires for the well-defined case (selector applied to its OWN ctor — the
    // wrong-ctor case is underspecified per SMT-LIB and is NOT checked).
    for (EufTermId s = 0; s < total; ++s) {
        if (!symIsSelector(s)) continue;
        const auto& sn = tm_->node(s);
        if (sn.args.empty()) continue;
        EufTermId u = sn.args[0];
        ExprId uE = originExpr(u);
        if (uE == NullExpr || uE >= static_cast<ExprId>(ir_->size())) continue;
        SortId dtSort = ir_->get(uE).sort;
        uint32_t argIdx = 0;
        const DtConstructorInfo* owner =
            ir_->datatypes().selector(dtSort, opName(s), argIdx);
        if (!owner) continue;
        EClassId uClass = egraph_->rep(u);
        for (EufTermId m : egraph_->classMembers(uClass)) {
            if (!symIsConstructor(m)) continue;
            // Match the selector's OWN constructor by name. A constructor whose
            // name is EMPTY is MALFORMED (the parser dropped the ctor name for
            // some terms — e.g. mk(snd q, 0) interns as bare "#dt.ctor." — which
            // is exactly what makes the projection at instantiateLemma() SKIP it
            // and leave the false-sat #70). Treat an empty-name constructor of
            // the right sort as a possible match so this floor still fires: this
            // is conservative (sat->unknown only) and only ever affects the
            // already-buggy empty-name case, never a genuine named-ctor sat.
            const std::string mName = opName(m);
            if (!mName.empty() && mName != owner->name) continue;
            if (ctorSort(m) != dtSort) continue;
            const auto& margs = tm_->node(m).args;
            if (argIdx >= margs.size()) continue;
            if (!egraph_->same(s, margs[argIdx])) return false;  // projection unapplied -> floor

            // (#70/#74) Even when the projection holds in EUF, an ARITH-sorted
            // field that is a COMPOUND term (e.g. mk((+ a 1), 0)) is unsound to
            // accept: EUF merges sel_i^C(u) with the field term, but the field's
            // arith VALUE is not coupled to the selector across the EUF/arith
            // boundary (the constructor field is not purified into a shared
            // leaf), so the arith theory can assign sel and the field different
            // values and we never see the conflict. z3/cvc5 derive the
            // projection through arithmetic and refute (e.g. (+ a 1) != (fst q)
            // while q = mk((+ a 1), 0) is UNSAT, not sat). We do not
            // independently re-validate that arith coupling, so floor to
            // Unknown. SOUNDNESS: sat->unknown only; fires solely for a selector
            // applied to its OWN constructor whose field is a compound arith
            // expression — exactly the uncoupled case. A bare variable/constant
            // field is already a shared leaf (coupled) and is NOT floored.
            ExprId fieldE = originExpr(margs[argIdx]);
            if (fieldE != NullExpr && fieldE < static_cast<ExprId>(ir_->size())) {
                const auto& fe = ir_->get(fieldE);
                bool arithSorted = (fe.sort == ir_->intSortId() ||
                                    fe.sort == ir_->realSortId());
                bool compoundArith = arithSorted && !fe.isLeaf() &&
                                     fe.kind != Kind::UFApply &&
                                     fe.kind != Kind::Selector;
                if (compoundArith) return false;  // uncoupled arith field -> floor
            }
        }
    }
    // (#70/#74) Injectivity constant-clash floor. Two same-constructor terms in
    // one class imply field-wise equality a_i = b_i (constructor injectivity).
    // When those equalities force two DISTINCT interpreted constants to be equal
    // — directly mk(i,2) = mk(1,1) => 2 = 1, or transitively through a shared
    // operand mk(-1,1) = mk(k,k) => -1 = k = 1 — the model is UNSAT. EUF merges
    // the constructors, but the implied field equalities over arith CONSTANTS
    // (which are not registered shared terms) never reach arithmetic, so the
    // contradiction is invisible and the combination reports a false sat. Detect
    // it structurally: per merged same-ctor pair, union the field operands by
    // their egraph rep and floor if a union class accumulates >= 2 distinct
    // constant values. SOUNDNESS: sat->unknown only — a genuine model can never
    // equate two distinct constants — and it is polarity-free (a floor, never a
    // conflict clause). Cost is tiny (few ctor terms/class, 2 fields each).
    auto constKeyOf = [&](EufTermId op) -> std::string {
        ExprId oe = originExpr(op);
        if (oe == NullExpr || oe >= static_cast<ExprId>(ir_->size())) return {};
        const auto& oce = ir_->get(oe);
        if (oce.kind == Kind::ConstInt) {
            if (auto* iv = std::get_if<int64_t>(&oce.payload.value))
                return "i:" + std::to_string(*iv);
        } else if (oce.kind == Kind::ConstReal) {
            if (auto* sv = std::get_if<std::string>(&oce.payload.value))
                return "r:" + *sv;
        }
        return {};
    };
    std::unordered_map<EClassId, std::vector<EufTermId>> ctorByClass;
    for (EufTermId t = 0; t < total; ++t)
        if (symIsConstructor(t)) ctorByClass[egraph_->rep(t)].push_back(t);
    for (auto& [cr, terms] : ctorByClass) {
        (void)cr;
        for (size_t i = 0; i < terms.size(); ++i) {
            for (size_t j = i + 1; j < terms.size(); ++j) {
                EufTermId t1 = terms[i], t2 = terms[j];
                if (tm_->node(t1).symbol != tm_->node(t2).symbol) continue;  // diff ctor = clash, not inj
                const auto& a1 = tm_->node(t1).args;
                const auto& a2 = tm_->node(t2).args;
                if (a1.size() != a2.size()) continue;
                // Iterative union-find over operand egraph reps for this pair.
                std::unordered_map<EClassId, EClassId> parent;
                auto find = [&](EClassId x) {
                    while (true) {
                        auto it = parent.find(x);
                        if (it == parent.end() || it->second == x) return x;
                        it->second = parent[it->second];  // path halving
                        x = it->second;
                    }
                };
                auto uni = [&](EClassId x, EClassId y) {
                    if (!parent.count(x)) parent[x] = x;
                    if (!parent.count(y)) parent[y] = y;
                    parent[find(x)] = find(y);
                };
                std::vector<LinForm> fieldEqs;  // (#76) field difference forms
                for (size_t k = 0; k < a1.size(); ++k) {
                    uni(egraph_->rep(a1[k]), egraph_->rep(a2[k]));
                    // Linear-field floor: if the two fields' integer linear forms
                    // differ by a NONZERO CONSTANT (all atom coefficients cancel),
                    // the fields can never be equal, so two merged same-ctor terms
                    // cannot be equal -> unsat. Catches injectivity over linear
                    // arith fields, e.g. mk(j,(+ i 0)) = mk(_,(+ i 2)) => 0 = 2
                    // (the i cancels). SOUND: a genuine model never merges two
                    // constructors whose fields differ by a constant.
                    int b1 = 64, b2 = 64;
                    auto la = linForm(*ir_, originExpr(a1[k]), b1);
                    auto lb = linForm(*ir_, originExpr(a2[k]), b2);
                    if (la && lb) {
                        LinForm d = *la;
                        if (addLin(d, *lb, -1)) {
                            if (d.coeffs.empty() && d.constant != 0)
                                return false;  // single field differs by const -> floor
                            fieldEqs.push_back(std::move(d));  // for the system check
                        }
                    }
                }
                // (#76) System floor: the per-field check above misses a jointly
                // infeasible SYSTEM (mk(2,2) = mk(1+k,k-3) => k=1 AND k=5). Run
                // Gaussian elimination over all field equalities {a_i - b_i = 0};
                // a derived 0 = nonzero proves the merge impossible -> floor.
                if (fieldEqs.size() >= 2 && systemInfeasible(std::move(fieldEqs)))
                    return false;
                // Collect, per union class, the distinct constant value among the
                // operands; a second distinct constant in the same class -> floor.
                std::unordered_map<EClassId, std::string> classConst;
                bool clash = false;
                auto consider = [&](EufTermId op) {
                    std::string key = constKeyOf(op);
                    if (key.empty()) return;
                    EClassId c = find(egraph_->rep(op));
                    auto it = classConst.find(c);
                    if (it == classConst.end()) classConst.emplace(c, key);
                    else if (it->second != key) clash = true;
                };
                for (size_t k = 0; k < a1.size() && !clash; ++k) {
                    consider(a1[k]);
                    consider(a2[k]);
                }
                if (clash) return false;  // injectivity forces distinct consts equal -> floor
            }
        }
    }

    // Note on selector-owner ownership: SMT-LIB datatype semantics treat
    // (sel x) when x is in a wrong-ctor class as UNDERSPECIFIED (any value),
    // not as a conflict. So a "selector applied to wrong ctor" check is NOT
    // a soundness gate — z3 agrees `(head nil) = red` is sat. The QF_DT
    // blocksworld bmc_4 false-SAT residual is not from selector ownership
    // but from BMC transition encoding (ITE-chain over (is-stack X)) where
    // xolver's model accepts a state that violates an ITE constraint we
    // don't independently re-validate. Proper fix requires a per-assertion
    // re-validator (analog of ArithModelValidator) for QF_DT — out of
    // single-edit scope.
    return true;
}

} // namespace xolver
