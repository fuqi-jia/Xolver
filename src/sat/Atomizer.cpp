#include "sat/Atomizer.h"
#include "theory/TheoryAtomRegistry.h"
#include "theory/arith/linear/LinearExpr.h"
#include <cassert>
#include <algorithm>

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

SatLit Atomizer::atomizeRec(ExprId eid, const CoreIr& ir) {
    if (eid == NullExpr) return SatLit{0, true};

    auto it = memo_.find(eid);
    if (it != memo_.end()) return it->second;

    const CoreExpr& e = ir.get(eid);
    SatLit result{0, true};

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
        default: {
            SatVar v = freshVar();
            result = SatLit::positive(v);
            bool isTheory = (e.kind == Kind::Eq || e.kind == Kind::Distinct ||
                             e.kind == Kind::Lt || e.kind == Kind::Leq ||
                             e.kind == Kind::Gt || e.kind == Kind::Geq);

            if (isTheory && registry_) {
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
                        v, eid, defaultTheory_, LinearAtomPayload{lhs, rel, rhs});
                } else {
                    // Non-arithmetic Eq/Distinct or unsupported theory atom
                    registry_->setUnsupportedTheorySeen();
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
