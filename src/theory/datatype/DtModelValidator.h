#pragma once

#include "expr/ir.h"
#include "expr/Datatype.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include <gmpxx.h>
#include <vector>
#include <string>
#include <unordered_map>

namespace xolver {

/**
 * DtModelValidator — independent end-to-end DT model check.
 *
 * Re-evaluates original assertions (pre-lowering ExprIds) at sat time using
 * the LIVE e-graph as the model. Each datatype-sorted expression's value is
 * its EUF equivalence class; selectors and testers are resolved via the
 * constructor present in the operand's class. Boolean combinators (And/Or/
 * Not/Implies/Ite/Eq/Distinct) are evaluated structurally.
 *
 * Semantics (SMT-LIB strict):
 *   - Selector on wrong-ctor or undetermined-ctor class → Indeterminate
 *     (NOT a conflict — SMT-LIB says it's underspecified, any value OK).
 *     This is critical: any "selector-owner check" that treats it as
 *     violation is semantically wrong and would over-reject sat cases like
 *     `(head nil) = red` (which is sat per z3).
 *   - Eq/Distinct over DT values: equal iff same e-class; distinct iff
 *     classes hold distinct constructors. Else Indeterminate.
 *   - Tester (is-C x): True iff x's class has C; False iff x's class has
 *     some other ctor; Indeterminate iff x's class has no ctor.
 *
 * Verdict semantics (conservative):
 *   - Satisfied : every assertion evaluates to true.
 *   - Violated  : some assertion evaluates DEFINITELY to false.
 *   - Indeterminate : at least one assertion can't be fully evaluated and
 *     none was definitely false. Caller treats Indeterminate as "can't
 *     disprove" — never as a violation.
 *
 * Sound floor pattern: if Violated, downgrade Sat → Unknown.
 */
class DtModelValidator {
public:
    enum class Verdict { Satisfied, Violated, Indeterminate };

    DtModelValidator(const CoreIr& ir,
                     const EufTermManager& tm,
                     const IncrementalEGraph& egraph,
                     const DatatypeRegistry& dts)
        : ir_(ir), tm_(tm), egraph_(egraph), dts_(dts) {}

    /** Validate the given assertion roots (original-formula ExprIds). */
    Verdict validate(const std::vector<ExprId>& assertions);

private:
    enum class Kind3 {
        Bool,            // boolean value
        DtClass,         // datatype value identified by EUF e-class
        Number,          // numeric value (treated as opaque for DT logic)
        Indeterminate    // cannot evaluate
    };
    struct R {
        Kind3 kind = Kind3::Indeterminate;
        bool b = false;
        EClassId cls = static_cast<EClassId>(-1);
        std::string numStr;  // numeric literal as string (for Eq across numbers)
    };

    R eval(ExprId e);

    // Resolve the constructor name of an e-class, if determined. Empty if not.
    std::string constructorOfClass(EClassId c) const;
    // Find the constructor term in a class whose ctor name is C, if any.
    EufTermId constructorTermInClass(EClassId c, const std::string& ctorName) const;
    // Datatype sort of an e-class (any member's origin sort), NullSort if none.
    SortId classDatatypeSort(EClassId c) const;
    // Strip "#dt.ctor."/"#dt.sel."/"#dt.is." prefix from an EUF symbol name.
    static std::string stripDtPrefix(const std::string& sym);

    const CoreIr& ir_;
    const EufTermManager& tm_;
    const IncrementalEGraph& egraph_;
    const DatatypeRegistry& dts_;

    // Memo table for eval to keep DAG evaluation linear in subterm count.
    std::unordered_map<ExprId, R> memo_;
};

} // namespace xolver
