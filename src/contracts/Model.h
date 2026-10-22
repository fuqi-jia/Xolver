#pragma once
#include "base/RealValue.h"
#include <string>
#include <unordered_map>
#include <vector>
#include <memory>

namespace xolver {
namespace sl { struct Interpretation; }
struct TheoryModel {
    std::shared_ptr<const sl::Interpretation> separation;
    // variable name -> value string (e.g. "x" -> "42", "y" -> "3/4").
    // Legacy channel; carries both numeric and boolean values as strings.
    std::unordered_map<std::string, std::string> assignments;
    // Typed numeric channel (RealValue unification, Phase 1). Solvers that
    // have migrated populate this; consumers prefer it for arithmetic
    // variables and fall back to `assignments` otherwise. Lets NRA export
    // exact algebraic models (e.g. √2) instead of a lossy string.
    std::unordered_map<std::string, RealValue> numericAssignments;

    // Interpretation of an uninterpreted function symbol as a finite
    // table plus a default. Each entry maps a concrete argument tuple to
    // a value; arguments not in the table take `deflt`. Populated by the
    // validated candidate search for QF_UF* model output (get-model).
    struct FuncEntry {
        std::vector<std::string> args;  // one value string per argument
        std::string value;
    };
    struct FuncInterp {
        std::vector<std::string> argSorts;  // "Int"/"Real"/"Bool" per arg
        std::string retSort;
        std::vector<FuncEntry> entries;
        std::string deflt;                  // value for unlisted tuples
    };
    std::unordered_map<std::string, FuncInterp> functionInterps;

    // Interpretation of an array variable: a default element plus a finite
    // set of (index, element) overrides. Equal arrays share one interp.
    // `defaultVal` is the value at any index not listed in `entries`.
    // Index/element values are opaque tokens that compare by equality
    // (e.g. eclass-rep markers like "@arr_e7"), since QF_AX indices and
    // elements may be uninterpreted-sort. Populated by EufSolver::getModel.
    struct ArrayInterp {
        std::string indexSort;
        std::string elemSort;
        std::string defaultVal;
        std::vector<std::pair<std::string, std::string>> entries; // (index, value)
    };
    std::unordered_map<std::string, ArrayInterp> arrayInterps;
    // First-class array values used in UF tables, keyed by value handles.
    // Handles identify records, not array equality: consumers compare the
    // default and stores extensionally. Separate from variable-name bindings.
    std::unordered_map<std::string, ArrayInterp> arrayValues;
};
} // namespace xolver
