#include "frontend/atomization/ArithAtomExtractor.h"
#include "theory/core/TheoryAtomRegistry.h"
#include <algorithm>
#include <iostream>

namespace nlcolver {

void ArithAtomExtractor::setPolynomialKernel(PolynomialKernel* kernel) {
    polyKernel_ = kernel;
    if (kernel) {
        polyConverter_ = std::make_unique<PolynomialConverter>(*kernel);
    } else {
        polyConverter_.reset();
    }
}

bool ArithAtomExtractor::extractAndRegister(ExprId eid, const CoreIr& ir, SatVar v, TheoryId targetTheory) {
    const auto& e = ir.get(eid);

    // Defensive: integer div/mod should have been lowered before atomization.
    if (e.kind == Kind::Mod && e.sort == ir.intSortId()) {
        std::cerr << "[ATOM] integer mod leaked into extractor (should have been lowered)\n";
        if (registry_) registry_->setUnsupportedTheorySeen();
        return false;
    }
    if (e.kind == Kind::Div && e.sort == ir.intSortId()) {
        std::cerr << "[ATOM] integer div leaked into extractor (should have been lowered)\n";
        if (registry_) registry_->setUnsupportedTheorySeen();
        return false;
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
                if (registry_) {
                    registry_->registerParsedTheoryAtom(
                        v, eid, targetTheory, LinearAtomPayload{lhs, rel, rhs});
                }
                return true;
            } else if (polyKernel_ && extractPolynomialConstraint(eid, ir, v, targetTheory)) {
                return true;
            } else {
                std::cerr << "[ATOM] unsupported NIRA kind=" << (int)e.kind << "\n";
                if (registry_) registry_->setUnsupportedTheorySeen();
            }
        } else {
            if (polyKernel_ && extractPolynomialConstraint(eid, ir, v, targetTheory)) {
                return true;
            } else {
                std::cerr << "[ATOM] unsupported NRA/NIA kind=" << (int)e.kind << "\n";
                if (registry_) registry_->setUnsupportedTheorySeen();
            }
        }
        return false;
    }

    // LRA / LIA path
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
        if (registry_) {
            registry_->registerParsedTheoryAtom(
                v, eid, targetTheory, LinearAtomPayload{lhs, rel, rhs});
        }
        return true;
    }

    return false;
}

bool ArithAtomExtractor::extractPolynomialConstraint(ExprId eid, const CoreIr& ir, SatVar v, TheoryId theory) {
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
            return true;  // caller handles tautology
        case PolyConstraintStatus::Conflict:
            return true;  // caller handles conflict
        case PolyConstraintStatus::Constraint:
            if (registry_) {
                registry_->registerParsedTheoryAtom(
                    v, eid, theory,
                    PolynomialAtomPayload{cc.diff, rel, mpq_class(0)});
            }
            return true;
        default:
            return false;
    }
}

} // namespace nlcolver
