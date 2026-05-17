#include "sat/Atomizer.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/combination/SharedTermRegistry.h"
#include "theory/arith/linear/LinearExpr.h"
#include "theory/euf/EufTypes.h"
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

SatLit Atomizer::getOrCreateEufAtom(EufAtomPayload payload, ExprId originExpr) {
    // Canonicalize payload in-place
    if (payload.lhs > payload.rhs) {
        std::swap(payload.lhs, payload.rhs);
    }

    EufAtomKey key{payload.lhs, payload.rhs, payload.rel, payload.kind};
    auto it = eufAtomDedup_.find(key);
    if (it != eufAtomDedup_.end()) {
        memo_[originExpr] = it->second;
        return it->second;
    }

    SatVar v = freshVar();
    SatLit lit = SatLit::positive(v);
    atoms_.push_back({v, originExpr, true, TheoryId::EUF});
    eufAtomDedup_[key] = lit;
    memo_[originExpr] = lit;

    if (registry_) {
        registry_->registerParsedTheoryAtom(v, originExpr, TheoryId::EUF, payload);
    }

    return lit;
}

SatLit Atomizer::atomizeNaryEufEq(ExprId eid, const CoreIr& ir) {
    const auto& e = ir.get(eid);

    // Bool equality: encode propositionally
    if (defaultTheory_ == TheoryId::EUF && areAllChildrenBool(e, ir)) {
        return encodeBoolEq(eid, ir);
    }

    SatVar andVar = freshVar();
    std::vector<SatLit> pairwiseLits;

    for (size_t i = 0; i + 1 < e.children.size(); ++i) {
        ExprId lhs = e.children[i];
        ExprId rhs = e.children[i + 1];
        ExprId synthExpr = synthExprAlloc_.next();
        SatLit plit = getOrCreateEufAtom(
            EufAtomPayload{lhs, rhs, Relation::Eq}, synthExpr);
        pairwiseLits.push_back(plit);
    }

    // Tseitin: andVar → each pairwise
    for (SatLit pl : pairwiseLits) {
        sat_.addClause({SatLit::negative(andVar), pl});
    }
    // Tseitin: any pairwise → andVar
    std::vector<SatLit> clause;
    clause.push_back(SatLit::positive(andVar));
    for (SatLit pl : pairwiseLits) {
        clause.push_back(pl.negated());
    }
    sat_.addClause(clause);

    return SatLit::positive(andVar);
}

SatLit Atomizer::atomizeNaryEufDistinct(ExprId eid, const CoreIr& ir) {
    const auto& e = ir.get(eid);

    // Bool distinct: encode propositionally
    if (defaultTheory_ == TheoryId::EUF && areAllChildrenBool(e, ir)) {
        return encodeBoolDistinct(eid, ir);
    }

    if (e.children.size() <= 1) {
        // vacuously true
        SatVar tv = freshVar();
        sat_.addClause({SatLit::positive(tv)});
        return SatLit::positive(tv);
    }

    SatVar andVar = freshVar();
    std::vector<SatLit> pairwiseLits;

    for (size_t i = 0; i < e.children.size(); ++i) {
        for (size_t j = i + 1; j < e.children.size(); ++j) {
            ExprId lhs = e.children[i];
            ExprId rhs = e.children[j];
            ExprId synthExpr = synthExprAlloc_.next();
            SatLit plit = getOrCreateEufAtom(
                EufAtomPayload{lhs, rhs, Relation::Neq}, synthExpr);
            pairwiseLits.push_back(plit);
        }
    }

    // Tseitin AND encoding
    for (SatLit pl : pairwiseLits) {
        sat_.addClause({SatLit::negative(andVar), pl});
    }
    std::vector<SatLit> clause;
    clause.push_back(SatLit::positive(andVar));
    for (SatLit pl : pairwiseLits) {
        clause.push_back(pl.negated());
    }
    sat_.addClause(clause);

    return SatLit::positive(andVar);
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
        // eqVar ↔ (li ↔ ri)
        // eqVar → (li ↔ ri):
        sat_.addClause({SatLit::negative(eqVar), li.negated(), ri});
        sat_.addClause({SatLit::negative(eqVar), li, ri.negated()});
        // (li ↔ ri) → eqVar:
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
        // xorVar → (l XOR r)
        sat_.addClause({SatLit::negative(xorVar), l, r});
        sat_.addClause({SatLit::negative(xorVar), l.negated(), r.negated()});
        // (l XOR r) → xorVar
        sat_.addClause({SatLit::positive(xorVar), l.negated(), r});
        sat_.addClause({SatLit::positive(xorVar), l, r.negated()});
        return SatLit::positive(xorVar);
    }

    // n >= 3: impossible in Bool domain
    SatVar fv = freshVar();
    sat_.addClause({SatLit::negative(fv)});
    return SatLit::positive(fv);
}

bool Atomizer::isFormulaPositionTerm(Kind k) {
    return k == Kind::Variable || k == Kind::UFApply;
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
        result = getOrCreateEufAtom(
            EufAtomPayload{eid, TrueSentinelExpr, Relation::Eq, EufAtomKind::BoolTermAsFormula}, eid);
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
            sat_.addClause({SatLit::positive(v)});
            if (!val) {
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

                if (targetTheory == TheoryId::NRA || targetTheory == TheoryId::NIA ||
                    targetTheory == TheoryId::NIRA) {
                    // For NIRA, try linear extraction first so linear constraints
                    // are registered as LinearAtomPayload (usable by LIRA engine).
                    if (targetTheory == TheoryId::NIRA) {
                        std::unordered_map<std::string, mpq_class> coeffs;
                        mpq_class rhs;
                        Relation rel;
                        if (extractLinearConstraint(eid, ir, coeffs, rhs, rel)) {
                            LinearFormKey lhs;
                            for (auto& [name, coeff] : coeffs) {
                                if (coeff != 0) {
                                    lhs.terms.push_back({name, coeff});
                                }
                            }
                            std::sort(lhs.terms.begin(), lhs.terms.end(),
                                      [](auto& a, auto& b) { return a.first < b.first; });
                            registry_->registerParsedTheoryAtom(
                                v, eid, targetTheory, LinearAtomPayload{lhs, rel, rhs});
                        } else if (polyKernel_ && extractPolynomialConstraint(eid, ir, v, targetTheory)) {
                            // registered inside extractPolynomialConstraint
                        } else {
                            std::cerr << "[ATOM] unsupported NIRA kind=" << (int)e.kind << "\n";
                            registry_->setUnsupportedTheorySeen();
                        }
                    } else {
                        if (polyKernel_ && extractPolynomialConstraint(eid, ir, v, targetTheory)) {
                            // registered inside extractPolynomialConstraint
                        } else {
                            std::cerr << "[ATOM] unsupported NRA/NIA/NIRA kind=" << (int)e.kind << "\n";
                            registry_->setUnsupportedTheorySeen();
                        }
                    }
                } else if (targetTheory == TheoryId::EUF) {
                    if (e.kind == Kind::Eq || e.kind == Kind::Distinct) {
                        if (e.children.size() == 2) {
                            // Check if both sides are Bool: encode propositionally
                            if (areAllChildrenBool(e, ir)) {
                                if (e.kind == Kind::Eq) {
                                    result = encodeBoolEq(eid, ir);
                                } else {
                                    result = encodeBoolDistinct(eid, ir);
                                }
                                memo_[eid] = result;
                                return result;
                            }
                            Relation rel = (e.kind == Kind::Eq) ? Relation::Eq : Relation::Neq;
                            ExprId lhs = e.children[0];
                            ExprId rhs = e.children[1];
                            result = getOrCreateEufAtom(
                                EufAtomPayload{lhs, rhs, rel}, eid);
                        } else if (e.children.size() > 2) {
                            result = (e.kind == Kind::Eq)
                                ? atomizeNaryEufEq(eid, ir)
                                : atomizeNaryEufDistinct(eid, ir);
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
                    // Existing LRA/LIA path.
                    std::unordered_map<std::string, mpq_class> coeffs;
                    mpq_class rhs;
                    Relation rel;
                    if (extractLinearConstraint(eid, ir, coeffs, rhs, rel)) {
                        LinearFormKey lhs;
                        for (auto& [name, coeff] : coeffs) {
                            if (coeff != 0) {
                                lhs.terms.push_back({name, coeff});
                            }
                        }
                        std::sort(lhs.terms.begin(), lhs.terms.end(),
                                  [](auto& a, auto& b) { return a.first < b.first; });
                        registry_->registerParsedTheoryAtom(
                            v, eid, targetTheory, LinearAtomPayload{lhs, rel, rhs});
                    } else {
                        std::cerr << "[ATOM] unsupported LRA kind=" << (int)e.kind << "\n";
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

bool Atomizer::extractPolynomialConstraint(ExprId eid, const CoreIr& ir, SatVar v, TheoryId theory) {
    const auto& e = ir.get(eid);
    if (e.children.size() != 2) return false;

    Relation rel;
    switch (e.kind) {
        case Kind::Eq:       rel = Relation::Eq;  break;
        case Kind::Distinct: rel = Relation::Neq; break;
        case Kind::Lt:       rel = Relation::Lt;  break;
        case Kind::Leq:      rel = Relation::Leq; break;
        case Kind::Gt:       rel = Relation::Gt;  break;
        case Kind::Geq:      rel = Relation::Geq; break;
        default: return false;
    }

    auto cc = polyConverter_->convertConstraint(e.children[0], e.children[1], rel, ir);
    switch (cc.status) {
        case PolyConstraintStatus::Tautology:
            // Always true: add unit clause asserting the literal
            sat_.addClause({SatLit::positive(v)});
            return true;
        case PolyConstraintStatus::Conflict:
            // Always false: add unit clause negating the literal
            sat_.addClause({SatLit::negative(v)});
            return true;
        case PolyConstraintStatus::Constraint:
            registry_->registerParsedTheoryAtom(
                v, eid, theory,
                PolynomialAtomPayload{cc.diff, rel, mpq_class(0)});
            return true;
        default:
            return false;
    }
}

} // namespace nlcolver
