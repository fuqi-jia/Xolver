#include "frontend/atomization/Atomizer.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include <cassert>
#include <algorithm>
#include <iostream>

namespace nlcolver {

Atomizer::Atomizer(SatSolver& sat) : sat_(sat) {}

SatLit Atomizer::atomize(ExprId root, const CoreIr& ir) {
    return atomizeRec(root, ir);
}

SatVar Atomizer::freshVar() {
    SatVar v = sat_.newVar();
    return v;
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
    return k == Kind::Variable || k == Kind::UFApply;
}

bool Atomizer::areAllChildrenBool(const CoreExpr& e, const CoreIr& ir) const {
    for (ExprId cid : e.children) {
        if (ir.get(cid).sort != boolSortId_) {
            return false;
        }
    }
    return true;
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

static bool containsUfApply(ExprId eid, const CoreIr& ir) {
    const auto& e = ir.get(eid);
    if (e.kind == Kind::UFApply) return true;
    for (ExprId child : e.children) {
        if (containsUfApply(child, ir)) return true;
    }
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
            SatVar x = freshVar();
            for (ExprId cid : e.children) {
                SatLit c = atomizeRec(cid, ir);
                sat_.addClause({SatLit::negative(x), c});
            }
            std::vector<SatLit> clause;
            clause.push_back(SatLit::positive(x));
            for (ExprId cid : e.children) {
                SatLit c = atomizeRec(cid, ir);
                clause.push_back(c.negated());
            }
            sat_.addClause(clause);
            result = SatLit::positive(x);
            break;
        }
        case Kind::Or: {
            SatVar x = freshVar();
            for (ExprId cid : e.children) {
                SatLit c = atomizeRec(cid, ir);
                sat_.addClause({SatLit::positive(x), c.negated()});
            }
            std::vector<SatLit> clause;
            clause.push_back(SatLit::negative(x));
            for (ExprId cid : e.children) {
                SatLit c = atomizeRec(cid, ir);
                clause.push_back(c);
            }
            sat_.addClause(clause);
            result = SatLit::positive(x);
            break;
        }
        case Kind::Implies: {
            assert(e.children.size() == 2);
            SatLit a = atomizeRec(e.children[0], ir);
            SatLit b = atomizeRec(e.children[1], ir);
            SatVar x = freshVar();
            sat_.addClause({SatLit::positive(x), a});
            sat_.addClause({SatLit::positive(x), b.negated()});
            sat_.addClause({SatLit::negative(x), a.negated(), b});
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
                // Bool equalities/distincts are propositional regardless of target theory
                if ((e.kind == Kind::Eq || e.kind == Kind::Distinct) &&
                    e.children.size() >= 2 && areAllChildrenBool(e, ir)) {
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
                        std::cerr << "[ATOM] combo-check eid=" << eid << " kind=" << (int)e.kind
                                  << " c0=" << e.children[0] << " c1=" << e.children[1]
                                  << " bothShared=" << bothShared << "\n";
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
                    bool hasUf = containsUfApply(eid, ir);
                    std::cerr << "[ATOM] combination eid=" << eid << " kind=" << (int)e.kind
                              << " hasUf=" << hasUf << "\n";
                    if (hasUf) {
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
                        std::cerr << "[ATOM] unsupported kind=" << (int)e.kind << " theory=" << (int)targetTheory << "\n";
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

} // namespace nlcolver
