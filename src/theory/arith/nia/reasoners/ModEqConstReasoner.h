#pragma once

#include "expr/ir.h"
#include "theory/arith/nia/NiaTypes.h"
#include "theory/arith/nia/core/DomainStore.h"
#include "theory/arith/nia/reasoners/ModEqConstFact.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include <gmpxx.h>
#include <string>
#include <vector>

namespace xolver {

// Track A Phase 1.2 — sound rule-based reasoner over ModEqConstFact list.
//
// Semantics under SMT-LIB Int: for `(mod x y) = c`:
//   y > 0:  c >= 0, y >= c+1, y | (x-c)
//   y < 0:  c >= 0, |y| >= c+1, y | (x-c)
//   y = 0:  mod0(x,y) = c (EUF; left to the EUF combination path)
//
// This Phase 1.2 implements:
//   Rule 1: c < 0 and y is non-zero (by bounds) → Conflict (no positive
//           or negative branch can satisfy `c >= 0`).
//   Rule 2: y >= 1 (provable) → require y >= c+1. If domain.upper < c+1
//           Conflict; if domain.lower < c+1 narrow it.
//   Rule 3: y <= -1 (provable) → require y <= -c-1. If domain.lower > -c-1
//           Conflict; if domain.upper > -c-1 narrow it.
//
// Restricted to facts whose y-expr is Kind::Variable (the LCTES shape).
// More complex y-expressions are skipped (fall back to legacy q*y path).
//
// Soundness invariants:
//   - Conflict reason set = fact's atom reason + the bound reasons that
//     produced the narrowing. Every literal in the clause is currently
//     true on the SAT trail or implied by an active bound.
//   - DomainUpdated reasons attach the fact's atom reason + the prior
//     bound reason that's being tightened.
//   - No rule introduces y*q or any new nonlinear term.
class ModEqConstReasoner {
public:
    // ir may be nullptr at construction time; setCoreIr-style callers can
    // wire it later via setCoreIr(). When ir is null, run() returns NoChange.
    ModEqConstReasoner(PolynomialKernel& kernel, const CoreIr* ir);

    void setCoreIr(const CoreIr* ir) { ir_ = ir; }

    // Process every fact in `facts` against `domains`. Returns the first
    // Conflict found, or DomainUpdated if any narrowing occurred, or
    // NoChange. Sound to call multiple times — re-running is idempotent
    // once all bounds are tightened.
    NiaReasoningResult run(const ModEqConstFactList& facts,
                           DomainStore& domains);

private:
    PolynomialKernel& kernel_;
    const CoreIr* ir_;

    // Extract a variable name from an ExprId if it is a Kind::Variable;
    // returns empty string otherwise (caller skips the fact).
    std::string varNameOf(ExprId eid) const;

    // Apply rules 1-3 to one fact at the current bounds. The `factReason`
    // is propagated into every Conflict/DomainUpdated emitted.
    NiaReasoningResult checkFact(const ModEqConstFact& fact,
                                  DomainStore& domains);
};

}  // namespace xolver
