#pragma once

#include "expr/ir.h"
#include <vector>
#include <unordered_set>

namespace xolver {

/**
 * Detected logic features from a CoreIr problem.
 * Used to route to the correct solver plan and detect
 * mismatches between declared logic and actual formula content.
 */
struct LogicFeatures {
    bool hasBool = false;
    bool hasInt = false;
    bool hasReal = false;
    bool hasUF = false;
    bool hasBV = false;
    bool hasQuantifier = false;
    bool hasArray = false;
    bool hasFP = false;
    bool hasIntVar = false;          // Int-sort variable (not constant)
    bool hasRealVar = false;         // Real-sort variable (not constant)
    bool hasNonlinear = false;       // Mul of two non-constants, Pow, etc.
    bool hasMixedIntReal = false;    // Both Int and Real variables appear
    bool hasInterpretedArithmetic = false; // Add, Mul, Lt, etc. on arithmetic sorts
    bool hasDatatype = false;        // Constructor/Selector/Tester or DT-sort var
    bool hasUnsupported = false;     // Anything we cannot soundly handle

    bool isEmpty() const {
        return !hasBool && !hasInt && !hasReal && !hasUF && !hasBV &&
               !hasQuantifier && !hasArray && !hasFP && !hasNonlinear &&
               !hasMixedIntReal && !hasInterpretedArithmetic && !hasDatatype &&
               !hasUnsupported;
    }
};

/**
 * Scan CoreIr to detect features relevant for solver routing.
 *
 * Rules:
 * - hasBool      : ConstBool, Not, And, Or, Implies, Xor, or Bool-sort Variable
 * - hasInt       : Int-sort Variable/Constant, Mod, Abs
 * - hasReal      : Real-sort Variable/Constant
 * - hasUF        : UFApply
 * - hasBV        : BvNot, BvAnd, BvOr, BvAdd, BvMul, or BV-sort Variable
 * - hasQuantifier: Forall, Exists
 * - hasArray     : Array-sort Variable
 * - hasFP        : ConstFP, or FP-sort Variable
 * - hasNonlinear : Mul where both operands are non-constant,
 *                  or Pow, or Div on non-linear expressions
 * - hasMixedIntReal: both hasInt and hasReal in same problem
 * - hasUnsupported: anything beyond current solver capabilities (e.g., quantifiers)
 */
class LogicFeatureDetector {
public:
    explicit LogicFeatureDetector(const CoreIr& ir);

    LogicFeatures detect() const;

private:
    const CoreIr& ir_;

    void scanExpr(ExprId id, LogicFeatures& f, std::unordered_set<ExprId>& visited) const;
    bool isNonConstantExpr(ExprId id, const std::unordered_set<ExprId>& visited) const;
};

} // namespace xolver
