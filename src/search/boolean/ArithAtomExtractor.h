#pragma once

#include "ir/NativeTerms.h"
#include "algebra/linear/LinearExpr.h"
#include "algebra/poly/PolynomialKernel.h"
#include "algebra/poly/PolynomialConverter.h"
#include "algebra/poly/PolynomialConstraint.h"
#include "contracts/SatSolver.h"
#include <map>
#include <memory>
#include <unordered_map>

namespace xolver {

class TheoryAtomRegistry;

/**
 * ArithAtomExtractor: extracts arithmetic theory atoms from TermExpr.
 *
 * Handles linear constraints (LRA/LIA) and polynomial constraints (NRA/NIA/NIRA).
 */
class ArithAtomExtractor {
public:
    void setRegistry(TheoryAtomRegistry* registry) { registry_ = registry; }
    void setPolynomialKernel(PolynomialKernel* kernel);

    // Try to extract and register an arithmetic theory atom for the given expression.
    // Returns true if the expression was handled as an arithmetic atom.
    // The caller is responsible for creating the SAT variable and adding it to atoms_.
    bool extractAndRegister(ExprId eid, const NativeTerms& ir, SatVar v, TheoryId targetTheory);

private:
    bool extractPolynomialConstraint(ExprId eid, const NativeTerms& ir, SatVar v, TheoryId theory);

    TheoryAtomRegistry* registry_ = nullptr;
    PolynomialKernel* polyKernel_ = nullptr;
    std::unique_ptr<PolynomialConverter> polyConverter_;
    std::map<PolynomialConstraintKey, SatLit> polynomialLiterals_;
};

} // namespace xolver
