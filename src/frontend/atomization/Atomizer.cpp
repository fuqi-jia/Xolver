#include "frontend/atomization/Atomizer.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace xolver {

Atomizer::Atomizer(SatSolver& sat) : sat_(sat) {}

SatLit Atomizer::atomize(ExprId root, const CoreIr& ir) {
    // Pre-atomize nested subformulas bottom-up so the recursive atomizeRec below
    // resolves every deep child from the memo (no deep native recursion).
    preAtomizeIterative(root, ir);
    return atomizeRec(root, ir);
}

void Atomizer::preAtomizeIterative(ExprId root, const CoreIr& ir) {
    // Two-visit post-order over boolean-sorted children only: those are exactly
    // the sub-formulas atomizeRec recurses into (And/Or/Not/Implies/Xor, bool
    // Eq/Distinct, bool-term-in-formula-position). Arithmetic/EUF operand terms
    // are NOT boolean-sorted, so they are left for atomizeRec's atom handling.
    // Processing children before parents means atomizeRec(parent) finds every
    // nested SatLit already in memo_ and never recurses deeply.
    struct Frame { ExprId eid; bool processed; };
    std::vector<Frame> stack;
    stack.push_back({root, false});
    while (!stack.empty()) {
        Frame& fr = stack.back();
        ExprId eid = fr.eid;
        if (eid == NullExpr || memo_.find(eid) != memo_.end()) { stack.pop_back(); continue; }
        const CoreExpr& e = ir.get(eid);
        if (!fr.processed) {
            fr.processed = true;
            for (ExprId c : e.children) {
                if (c != NullExpr && memo_.find(c) == memo_.end() &&
                    ir.get(c).sort == boolSortId_) {
                    stack.push_back({c, false});
                }
            }
            continue;
        }
        stack.pop_back();
        // All boolean-sorted children memoized → atomizeRec emits this node's
        // clauses reading children from memo_, recursing at most one level.
        atomizeRec(eid, ir);
    }
}

SatVar Atomizer::freshVar() {
    SatVar v = sat_.newVar();
    return v;
}

// PG-CNF polarity bits: 1 = positive, 2 = negative, 3 = both.
static inline uint8_t flipPol(uint8_t p) { return p == 3 ? 3 : (p == 1 ? 2 : 1); }

void Atomizer::computePolarities(const std::vector<ExprId>& roots, const CoreIr& ir) {
    if (!pgEnabled_) return;
    pol_.clear();
    // Iterative DFS (formulas can be deep); union the polarity of each node.
    std::vector<std::pair<ExprId, uint8_t>> stack;
    for (ExprId r : roots) stack.push_back({r, 1});  // asserted => positive
    while (!stack.empty()) {
        auto [eid, p] = stack.back();
        stack.pop_back();
        if (eid == NullExpr || eid == TrueSentinelExpr || eid == FalseSentinelExpr) continue;
        if (eid >= ir.size()) continue;
        uint8_t cur = pol_[eid];
        if ((cur & p) == p) continue;  // these polarity bits already propagated
        pol_[eid] = static_cast<uint8_t>(cur | p);
        const CoreExpr& e = ir.get(eid);
        switch (e.kind) {
            case Kind::Not:
                if (!e.children.empty()) stack.push_back({e.children[0], flipPol(p)});
                break;
            case Kind::And:
            case Kind::Or:
                for (ExprId c : e.children) stack.push_back({c, p});
                break;
            case Kind::Implies:
                if (e.children.size() == 2) {
                    stack.push_back({e.children[0], flipPol(p)});  // antecedent flips
                    stack.push_back({e.children[1], p});           // consequent keeps
                }
                break;
            default:
                // Non-monotone (Xor / bool Eq / Distinct) or a theory atom /
                // leaf: any boolean operand occurs in BOTH polarities, and
                // theory-atom operands are terms (polarity irrelevant). Mark
                // both so no defining clause is ever dropped.
                for (ExprId c : e.children) stack.push_back({c, 3});
                break;
        }
    }
}

std::pair<bool, bool> Atomizer::pgDirs(ExprId eid) const {
    if (!pgEnabled_) return {true, true};
    auto it = pol_.find(eid);
    if (it == pol_.end() || it->second == 0) return {true, true};  // defensive
    return {(it->second & 1) != 0, (it->second & 2) != 0};
}

SatLit Atomizer::registerDynamicAtom(ExprId expr, TheoryId theory) {
    auto it = memo_.find(expr);
    if (it != memo_.end()) return it->second;

    SatVar v = freshVar();
    SatLit lit = SatLit::positive(v);
    atoms_.push_back({v, expr, true, theory});
    memo_[expr] = lit;
    return lit;
}

bool Atomizer::isFormulaPositionTerm(Kind k) {
    // A datatype tester ((_ is C) x) is a Bool-sorted DT term that can appear in
    // formula position; route it through BoolTermAsFormula so it is interned into
    // the shared e-graph as a Tester term ("#dt.is.<C>") and the DtReasoner's
    // tester-consistency check sees it. Without this, a Kind::Tester atom gets a
    // fresh opaque Bool SAT var and the DT layer never constrains it -> the
    // QF_DT tester-on-constructor false-SAT class (is_C(D ...) with C!=D left
    // unrefuted). (Before the parser fix tagged it Tester it was a UFApply, which
    // also routes here but only as an opaque application.)
    return k == Kind::Variable || k == Kind::UFApply || k == Kind::Tester;
}

bool Atomizer::areAllChildrenBool(const CoreExpr& e, const CoreIr& ir) const {
    for (ExprId cid : e.children) {
        if (ir.get(cid).sort != boolSortId_) {
            return false;
        }
    }
    return true;
}

bool Atomizer::isProvablyBool(ExprId eid, const CoreIr& ir) const {
    const auto& e = ir.get(eid);
    if (e.sort == boolSortId_) return true;
    auto sk = ir.sortKind(e.sort);
    if (sk && *sk == SortKind::Bool) return true;
    // Boolean-producing operators are Bool regardless of sort registration.
    switch (e.kind) {
        case Kind::Not: case Kind::And: case Kind::Or:
        case Kind::Implies: case Kind::Xor: case Kind::ConstBool:
        case Kind::Eq: case Kind::Distinct:
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
        case Kind::IsInt: case Kind::Forall: case Kind::Exists:
            return true;
        default:
            return false;
    }
}

SatLit Atomizer::encodeBoolEq(ExprId eid, const CoreIr& ir) {
    const auto& e = ir.get(eid);
    assert(e.children.size() >= 2);

    SatVar andVar = freshVar();
    std::vector<SatLit> eqLits;
    for (size_t i = 0; i + 1 < e.children.size(); ++i) {
        SatLit li = atomizeRec(e.children[i], ir);
        SatLit ri = atomizeRec(e.children[i + 1], ir);
        SatVar eqVar = freshVar();
        // eqVar ↔ (li ↔ ri):
        sat_.addClause({SatLit::negative(eqVar), li.negated(), ri});
        sat_.addClause({SatLit::negative(eqVar), li, ri.negated()});
        sat_.addClause({SatLit::positive(eqVar), li, ri});
        sat_.addClause({SatLit::positive(eqVar), li.negated(), ri.negated()});
        eqLits.push_back(SatLit::positive(eqVar));
    }

    // andVar ↔ ∧ eqLits
    for (SatLit el : eqLits) {
        sat_.addClause({SatLit::negative(andVar), el});
    }
    std::vector<SatLit> clause;
    clause.push_back(SatLit::positive(andVar));
    for (SatLit el : eqLits) {
        clause.push_back(el.negated());
    }
    sat_.addClause(clause);

    return SatLit::positive(andVar);
}

SatLit Atomizer::encodeBoolDistinct(ExprId eid, const CoreIr& ir) {
    const auto& e = ir.get(eid);

    if (e.children.size() <= 1) {
        SatVar tv = freshVar();
        sat_.addClause({SatLit::positive(tv)});
        return SatLit::positive(tv);
    }

    if (e.children.size() == 2) {
        SatLit l = atomizeRec(e.children[0], ir);
        SatLit r = atomizeRec(e.children[1], ir);
        // XOR: l ≠ r
        SatVar xorVar = freshVar();
        sat_.addClause({SatLit::negative(xorVar), l, r});
        sat_.addClause({SatLit::negative(xorVar), l.negated(), r.negated()});
        sat_.addClause({SatLit::positive(xorVar), l.negated(), r});
        sat_.addClause({SatLit::positive(xorVar), l, r.negated()});
        return SatLit::positive(xorVar);
    }

    // n >= 3: impossible in Bool domain
    SatVar fv = freshVar();
    sat_.addClause({SatLit::negative(fv)});
    return SatLit::positive(fv);
}

// True if the expression tree contains a UF application OR an array operator
// (select/store/const-array). In combination logics these are the operators
// that must be routed to the EUF solver (which owns the shared egraph and the
// array reasoner); a pure-arith atom over shared index terms instead routes to
// the arith theory / shared-equality mechanism.
// iter-100 perf: ExprId-level memoization. Without caching, DAG-shared
// subtrees were re-walked on every Eq/Distinct routing decision. For
// combination-logic formulas with massive DAG sharing (Dartagnan-class:
// 5 root assertions, 17K+ distinct sub-expressions), the same sub-
// expression could be DFS-walked many times across routing calls.
// Two-color memo on ExprId:
//   present-and-true  → known has-UF/array
//   present-but-false → known clean (UF/array-free) subtree
// Cache is per-atomizer-call by ExprId; ExprIds are hash-cons stable
// for the duration of a single solve so the memo is referentially sound.
static bool containsArrayOrUf(ExprId root, const CoreIr& ir,
                              std::unordered_map<uint32_t, bool>& memo) {
    auto memoIt = memo.find(root);
    if (memoIt != memo.end()) return memoIt->second;

    // Local visited set so the iterative DFS doesn't re-push already-seen
    // children within THIS top-level call (cheap shared-subterm prune).
    std::unordered_set<uint32_t> visited;
    std::vector<ExprId> stack{root};
    while (!stack.empty()) {
        ExprId cur = stack.back();
        stack.pop_back();
        if (!visited.insert(cur).second) continue;

        // Inner cache hit? Propagate eagerly.
        auto inner = memo.find(cur);
        if (inner != memo.end()) {
            if (inner->second) {
                memo[root] = true;
                return true;
            }
            continue;  // known clean — don't re-walk children
        }

        const auto& e = ir.get(cur);
        if (e.kind == Kind::UFApply || e.kind == Kind::Select ||
            e.kind == Kind::Store || e.kind == Kind::ConstArray ||
            // Datatype operators are also EUF-owned (DtReasoner on the
            // shared egraph), so an atom mentioning one routes to EUF.
            e.kind == Kind::Constructor || e.kind == Kind::Selector ||
            e.kind == Kind::Tester) {
            memo[cur] = true;
            memo[root] = true;
            return true;
        }
        for (ExprId child : e.children) stack.push_back(child);
    }

    // All reachable subterms walked, no UF/array. Cache result for every
    // visited ExprId so future calls short-circuit.
    for (uint32_t v : visited) memo.emplace(v, false);
    return false;
}

SatLit Atomizer::atomizeRec(ExprId eid, const CoreIr& ir) {
    if (eid == NullExpr) return SatLit{0, true};

    auto it = memo_.find(eid);
    if (it != memo_.end()) return it->second;

    const CoreExpr& e = ir.get(eid);
    SatLit result{0, true};

    // Bool-valued terms in formula position under QF_UF:
    // p(a), q (Bool var), etc. → (= term true)
    if (defaultTheory_ == TheoryId::EUF &&
        e.sort == boolSortId_ &&
        isFormulaPositionTerm(e.kind)) {
        result = eufExtractor_.getOrCreateAtom(
            EufAtomPayload{eid, TrueSentinelExpr, Relation::Eq, EufAtomKind::BoolTermAsFormula}, eid,
            memo_,
            [this]() { return freshVar(); },
            [this](SatVar v, ExprId oe, bool isT, TheoryId t) { atoms_.push_back({v, oe, isT, t}); });
        memo_[eid] = result;
        return result;
    }

    switch (e.kind) {
        case Kind::Variable: {
            SatVar v = freshVar();
            result = SatLit::positive(v);
            atoms_.push_back({v, eid, false, TheoryId::Bool});
            // Expose the Bool var's SatVar to theory solvers by name
            // (e.g. NIA Farkas-Or needs to pin boolpur_K Tseitin proxies
            // matching its chosen Or branch so SAT-CDCL converges).
            if (registry_) {
                if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                    registry_->registerBoolVariable(*s, v);
                }
            }
            break;
        }
        case Kind::ConstBool: {
            bool val = std::get<bool>(e.payload.value);
            SatVar v = freshVar();
            if (val) {
                sat_.addClause({SatLit::positive(v)});
            } else {
                sat_.addClause({SatLit::negative(v)});
            }
            result = SatLit::positive(v);
            break;
        }
        case Kind::Not: {
            SatLit child = atomizeRec(e.children[0], ir);
            result = child.negated();
            break;
        }
        case Kind::And: {
            // x ↔ ⋀cᵢ.  PG: pos-dir = x→⋀cᵢ  {(¬x∨cᵢ)};  neg-dir = ⋀cᵢ→x {(x∨⋁¬cᵢ)}.
            auto [needPos, needNeg] = pgDirs(eid);
            SatVar x = freshVar();
            if (needPos) {
                for (ExprId cid : e.children) {
                    SatLit c = atomizeRec(cid, ir);
                    sat_.addClause({SatLit::negative(x), c});
                }
            }
            if (needNeg) {
                std::vector<SatLit> clause;
                clause.push_back(SatLit::positive(x));
                for (ExprId cid : e.children) {
                    SatLit c = atomizeRec(cid, ir);
                    clause.push_back(c.negated());
                }
                sat_.addClause(clause);
            }
            result = SatLit::positive(x);
            break;
        }
        case Kind::Or: {
            // x ↔ ⋁cᵢ.  PG: pos-dir = x→⋁cᵢ {(¬x∨⋁cᵢ)};  neg-dir = ⋁cᵢ→x {(x∨¬cᵢ)}.
            auto [needPos, needNeg] = pgDirs(eid);
            SatVar x = freshVar();
            if (needNeg) {
                for (ExprId cid : e.children) {
                    SatLit c = atomizeRec(cid, ir);
                    sat_.addClause({SatLit::positive(x), c.negated()});
                }
            }
            if (needPos) {
                std::vector<SatLit> clause;
                clause.push_back(SatLit::negative(x));
                for (ExprId cid : e.children) {
                    SatLit c = atomizeRec(cid, ir);
                    clause.push_back(c);
                }
                sat_.addClause(clause);
            }
            result = SatLit::positive(x);
            break;
        }
        case Kind::Implies: {
            // x ↔ (¬a ∨ b).  PG: pos-dir = x→(¬a∨b) {(¬x∨¬a∨b)};
            //                    neg-dir = (¬a∨b)→x {(x∨a),(x∨¬b)}.
            assert(e.children.size() == 2);
            auto [needPos, needNeg] = pgDirs(eid);
            SatLit a = atomizeRec(e.children[0], ir);
            SatLit b = atomizeRec(e.children[1], ir);
            SatVar x = freshVar();
            if (needNeg) {
                sat_.addClause({SatLit::positive(x), a});
                sat_.addClause({SatLit::positive(x), b.negated()});
            }
            if (needPos) {
                sat_.addClause({SatLit::negative(x), a.negated(), b});
            }
            result = SatLit::positive(x);
            break;
        }
        case Kind::Xor: {
            assert(e.children.size() == 2);
            SatLit a = atomizeRec(e.children[0], ir);
            SatLit b = atomizeRec(e.children[1], ir);
            SatVar x = freshVar();
            // x ↔ (a ⊕ b)
            sat_.addClause({SatLit::negative(x), a.negated(), b.negated()});
            sat_.addClause({SatLit::negative(x), a, b});
            sat_.addClause({SatLit::positive(x), a.negated(), b});
            sat_.addClause({SatLit::positive(x), a, b.negated()});
            result = SatLit::positive(x);
            break;
        }
        case Kind::Ite: {
            assert(!"ITE should have been lowered by CoreIteLowerer before atomization");
            // Fallback: old Tseitin encoding (should never reach here).
            SatLit c = atomizeRec(e.children[0], ir);
            SatLit t = atomizeRec(e.children[1], ir);
            SatLit f = atomizeRec(e.children[2], ir);
            SatVar x = freshVar();
            sat_.addClause({SatLit::negative(x), c.negated(), t});
            sat_.addClause({SatLit::negative(x), c, f});
            sat_.addClause({SatLit::positive(x), c.negated(), t.negated()});
            sat_.addClause({SatLit::positive(x), c, f.negated()});
            result = SatLit::positive(x);
            break;
        }
        default: {
            SatVar v = freshVar();
            result = SatLit::positive(v);
            bool isTheory = (e.kind == Kind::Eq || e.kind == Kind::Distinct ||
                             e.kind == Kind::Lt || e.kind == Kind::Leq ||
                             e.kind == Kind::Gt || e.kind == Kind::Geq);

            if (isTheory && registry_) {
                // Bool equalities/distincts are propositional regardless of target theory.
                // Eq/Distinct operands share a sort, so if ANY operand is provably
                // Boolean the whole atom is Boolean — this catches cases where a
                // declared Bool variable carries an unregistered SortId (so the
                // strict all-children check would miss it).
                if ((e.kind == Kind::Eq || e.kind == Kind::Distinct) &&
                    e.children.size() >= 2 &&
                    (areAllChildrenBool(e, ir) || isProvablyBool(e.children[0], ir) ||
                     isProvablyBool(e.children[1], ir))) {
                    if (e.kind == Kind::Eq) {
                        result = encodeBoolEq(eid, ir);
                    } else {
                        result = encodeBoolDistinct(eid, ir);
                    }
                    memo_[eid] = result;
                    return result;
                }

                TheoryId targetTheory = defaultTheory_;
                if (defaultTheory_ == TheoryId::Combination) {
                    bool isEqOrDistinct = (e.kind == Kind::Eq || e.kind == Kind::Distinct);
                    bool bothShared = false;
                    if (isEqOrDistinct && e.children.size() == 2 && sharedTermRegistry_) {
                        bothShared = sharedTermRegistry_->hasTerm(e.children[0]) &&
                                     sharedTermRegistry_->hasTerm(e.children[1]);
                    }
                    if (bothShared) {
                        auto optA = sharedTermRegistry_->findByExprId(e.children[0]);
                        auto optB = sharedTermRegistry_->findByExprId(e.children[1]);
                        if (optA && optB) {
                            SatLit eqLit = registry_->getOrCreateSharedEqualityAtom(*optA, *optB);
                            result = (e.kind == Kind::Distinct) ? eqLit.negated() : eqLit;
                            memo_[eid] = result;
                            return result;
                        }
                    }
                    // Route to EUF if the atom mentions a UF application OR an
                    // array operator (select/store/const-array): EUF owns the
                    // shared egraph and the array reasoner. Pure-arith atoms
                    // over shared (index/bridge) terms route to the arith
                    // theory; equalities whose operands are both shared terms
                    // were already handled above via the shared-eq mechanism.
                    bool hasArrayOrUf = containsArrayOrUf(eid, ir, containsArrayOrUfMemo_);
                    if (hasArrayOrUf) {
                        targetTheory = TheoryId::EUF;
                    } else {
                        targetTheory = combinationArithTheory_;
                    }
                }

                if (targetTheory == TheoryId::EUF) {
                    if (e.kind == Kind::Eq || e.kind == Kind::Distinct) {
                        if (e.children.size() == 2) {
                            Relation rel = (e.kind == Kind::Eq) ? Relation::Eq : Relation::Neq;
                            ExprId lhs = e.children[0];
                            ExprId rhs = e.children[1];
                            result = eufExtractor_.getOrCreateAtom(
                                EufAtomPayload{lhs, rhs, rel}, eid,
                                memo_,
                                [this]() { return freshVar(); },
                                [this](SatVar v, ExprId oe, bool isT, TheoryId t) { atoms_.push_back({v, oe, isT, t}); });
                        } else if (e.children.size() > 2) {
                            result = (e.kind == Kind::Eq)
                                ? eufExtractor_.atomizeNaryEq(eid, ir, memo_,
                                    [this]() { return freshVar(); },
                                    [this](const std::vector<SatLit>& c) { sat_.addClause(c); },
                                    [this, &ir](ExprId ce) { return atomizeRec(ce, ir); })
                                : eufExtractor_.atomizeNaryDistinct(eid, ir, memo_,
                                    [this]() { return freshVar(); },
                                    [this](const std::vector<SatLit>& c) { sat_.addClause(c); },
                                    [this, &ir](ExprId ce) { return atomizeRec(ce, ir); });
                            memo_[eid] = result;
                            return result;
                        } else if (e.kind == Kind::Distinct && e.children.size() <= 1) {
                            // distinct with 0/1 args is vacuously true
                            SatVar tv = freshVar();
                            sat_.addClause({SatLit::positive(tv)});
                            result = SatLit::positive(tv);
                        } else {
                            std::cerr << "[ATOM] unsupported EUF kind=" << (int)e.kind << " children=" << e.children.size() << "\n";
                            registry_->setUnsupportedTheorySeen();
                        }
                    } else {
                        std::cerr << "[ATOM] unsupported EUF non-eq kind=" << (int)e.kind << "\n";
                        registry_->setUnsupportedTheorySeen();
                    }
                } else {
                    // LRA / LIA / NRA / NIA / NIRA path
                    bool handled = arithExtractor_.extractAndRegister(eid, ir, v, targetTheory);
                    if (!handled) {
                        registry_->setUnsupportedTheorySeen();
                    }
                }
            } else {
                atoms_.push_back({v, eid, isTheory, TheoryId::Bool});
            }
            break;
        }
    }

    memo_[eid] = result;
    return result;
}

} // namespace xolver
