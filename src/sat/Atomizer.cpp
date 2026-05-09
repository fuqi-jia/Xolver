#include "sat/Atomizer.h"
#include <cassert>

namespace nlcolver {

Atomizer::Atomizer(SatSolver& sat) : sat_(sat) {}

SatLit Atomizer::atomize(ExprId root, const CoreIr& ir) {
    return atomizeRec(root, ir);
}

SatVar Atomizer::freshVar() {
    SatVar v = sat_.newVar();
    return v;
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
            // Store in payload; true/false handled by checking payload directly.
            bool val = std::get<bool>(e.payload.value);
            SatVar v = freshVar();
            sat_.addClause({SatLit::positive(v)});
            if (!val) {
                // Force false: add both positive and negative → conflict
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
            // Tseitin: x ↔ a ∧ b
            // CNF: (¬x ∨ a), (¬x ∨ b), (x ∨ ¬a ∨ ¬b)
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
            // Tseitin: x ↔ a ∨ b
            // CNF: (x ∨ ¬a), (x ∨ ¬b), (¬x ∨ a ∨ b)
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
            // Implies a b = Or (Not a) b
            SatVar x = freshVar();
            sat_.addClause({SatLit::positive(x), a});
            sat_.addClause({SatLit::positive(x), b.negated()});
            sat_.addClause({SatLit::negative(x), a.negated(), b});
            result = SatLit::positive(x);
            break;
        }
        default: {
            // Theory atom or unknown: allocate a SAT variable.
            SatVar v = freshVar();
            result = SatLit::positive(v);
            // Mark as theory atom (heuristic: arithmetic comparisons).
            bool isTheory = (e.kind == Kind::Eq || e.kind == Kind::Distinct ||
                             e.kind == Kind::Lt || e.kind == Kind::Leq ||
                             e.kind == Kind::Gt || e.kind == Kind::Geq);
            atoms_.push_back({v, eid, isTheory, TheoryId::Bool}); // theory id refined later
            break;
        }
    }

    memo_[eid] = result;
    return result;
}

} // namespace nlcolver
