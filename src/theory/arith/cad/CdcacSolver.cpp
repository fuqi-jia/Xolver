#include "theory/arith/cad/CdcacSolver.h"
#include "expr/payload.h"

namespace nlcolver {

CdcacSolver::CdcacSolver(std::unique_ptr<PolynomialKernel> kernel)
    : kernel_(std::move(kernel)),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)) {}

void CdcacSolver::push() {}
void CdcacSolver::pop(uint32_t) {}

void CdcacSolver::reset() {
    constraints_.clear();
    allVars_.clear();
    lastConflict_ = std::nullopt;
}

void CdcacSolver::collectVars(ExprId eid, const CoreIr& ir) {
    const CoreExpr& e = ir.get(eid);
    if (e.kind == Kind::Variable) {
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            allVars_.insert(*s);
        }
    }
    for (ExprId child : e.children) {
        collectVars(child, ir);
    }
}

void CdcacSolver::assertLit(const TheoryAtom& atom, bool value, const CoreIr& ir) {
    collectVars(atom.exprId, ir);
    const CoreExpr& e = ir.get(atom.exprId);
    if (e.children.size() != 2) return;

    Relation rel;
    switch (e.kind) {
        case Kind::Eq:  rel = Relation::Eq;  break;
        case Kind::Lt:  rel = Relation::Lt;  break;
        case Kind::Leq: rel = Relation::Leq; break;
        case Kind::Gt:  rel = Relation::Gt;  break;
        case Kind::Geq: rel = Relation::Geq; break;
        default: return;
    }

    if (!value) {
        switch (rel) {
            case Relation::Eq:  return; // neq unsupported in MVP
            case Relation::Lt:  rel = Relation::Geq; break;
            case Relation::Leq: rel = Relation::Gt;  break;
            case Relation::Gt:  rel = Relation::Leq; break;
            case Relation::Geq: rel = Relation::Lt;  break;
        }
    }

    PolyId lhs = converter_->convert(e.children[0], ir);
    PolyId rhs = converter_->convert(e.children[1], ir);
    if (lhs == NullPoly || rhs == NullPoly) return;

    PolyId diff = kernel_->sub(lhs, rhs);
    constraints_.push_back({atom.satVar, diff, rel});
}

static bool evalConstraint(int sgn, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return sgn == 0;
        case Relation::Lt:  return sgn < 0;
        case Relation::Leq: return sgn <= 0;
        case Relation::Gt:  return sgn > 0;
        case Relation::Geq: return sgn >= 0;
        default: return false;
    }
}

bool CdcacSolver::evaluateAtSample(
        const std::vector<PolyConstraint>& constraints,
        const std::unordered_map<std::string, mpq_class>& sample) {
    for (const auto& c : constraints) {
        int s = kernel_->sgn(c.poly, sample);
        if (!evalConstraint(s, c.rel)) return false;
    }
    return true;
}

TheoryCheckResult CdcacSolver::trySolve(const CoreIr& /*ir*/) {
    if (constraints_.empty()) return TheoryCheckResult::consistent();

    std::vector<std::string> vars(allVars_.begin(), allVars_.end());

    // MVP sample strategy: try a small grid of rational values.
    const mpq_class candidates[] = {mpq_class(0), mpq_class(1), mpq_class(-1),
                                     mpq_class(2), mpq_class(-2),
                                     mpq_class(1,2), mpq_class(-1,2)};

    if (vars.size() == 1) {
        for (const auto& val : candidates) {
            std::unordered_map<std::string, mpq_class> sample;
            sample[vars[0]] = val;
            if (evaluateAtSample(constraints_, sample)) {
                return TheoryCheckResult::consistent();
            }
        }
    } else if (vars.size() == 2) {
        for (const auto& v1 : candidates) {
            for (const auto& v2 : candidates) {
                std::unordered_map<std::string, mpq_class> sample;
                sample[vars[0]] = v1;
                sample[vars[1]] = v2;
                if (evaluateAtSample(constraints_, sample)) {
                    return TheoryCheckResult::consistent();
                }
            }
        }
    }

    // No sample found → build naive conflict (all constraints).
    TheoryConflict conflict;
    for (const auto& c : constraints_) {
        conflict.clause.push_back(SatLit::negative(c.satVar));
    }
    return TheoryCheckResult::mkConflict(std::move(conflict));
}

TheoryCheckResult CdcacSolver::check(const CoreIr& ir) {
    return trySolve(ir);
}

} // namespace nlcolver
