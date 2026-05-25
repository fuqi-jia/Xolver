#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "expr/types.h"
#include <cstdint>
#include <vector>

namespace nlcolver {

// Lazard projection — provenance + incompleteness types (shared with the
// closure; see LAZARD.md [H7]). The Lazard projection set for eliminating v
// over a primitive squarefree basis {f} is:
//   per f (deg_v f >= 1): LeadingCoefficient_v(f), TrailingCoefficient_v(f),
//                          Discriminant_v(f) = res_v(f, f');
//   per input p:          non-constant Content_v(p);
//   per distinct pair:    Resultant_v(f_i, f_j).
// (This is the Lazard set — leading/trailing coeffs + discriminants + pairwise
// resultants — NOT Collins' full coefficient list + PSC chain.)

enum class LazardProjectionOpKind : uint8_t {
    Input,                 // an original constraint polynomial
    Content,               // content_v(parent1)
    SquarefreeFactor,      // squarefreePart_v(primitivePart_v(parent1))
    LeadingCoefficient,    // lc_v(parent1)   [parent1 is a SquarefreeFactor]
    TrailingCoefficient,   // tc_v(parent1)
    Discriminant,          // res_v(parent1, parent1')   (psc_0 of (f, f'))
    Resultant,             // res_v(parent1, parent2)     (psc_0 of (f, g))
};

enum class LazardIncompleteReason : uint8_t {
    None,
    ProjectionKernelFailure,    // squarefree/content exact gcd unsupported
    ProjectionBudgetExceeded,   // a Sylvester submatrix / registry exceeded budget
    // NOTE: valuation / tower / root-isolation reasons are reserved by
    // LAZARD.md [H7] for steps B-D and intentionally not used by projection.
};

struct LazardProjectionConfig {
    int maxMatrixDim = 9;       // Sylvester submatrix dimension cap (psc budget)
    LazardProjectionConfig() = default;
};

// Provenance of a closure entry (LAZARD.md [H7]): the op that produced it and
// the interned-entry indices of its parents (-1 if absent). The entry's own
// index is its "output", so it is not duplicated here. eliminatedVar is the
// variable whose projection produced this poly (NullVar for an Input).
struct LazardProjectionSource {
    LazardProjectionOpKind op = LazardProjectionOpKind::Input;
    int parent1 = -1;
    int parent2 = -1;
    VarId eliminatedVar = NullVar;
};

// One generated projection polynomial with its provenance parents (by value;
// the closure resolves them to interned entry indices). Output polynomials are
// in lower variables (do not contain v); the SquarefreeFactor items remain in v
// (they are the current-level boundary polynomials).
struct LazardItem {
    RationalPolynomial poly;
    LazardProjectionOpKind op = LazardProjectionOpKind::Input;
    RationalPolynomial parent1;
    RationalPolynomial parent2;
    bool hasParent1 = false;
    bool hasParent2 = false;
};

struct LazardOpResult {
    bool complete = true;
    LazardIncompleteReason reason = LazardIncompleteReason::None;
    std::vector<LazardItem> items;   // in emission order; parents precede dependents
};

// Single Lazard elimination step over E (polynomials with mainVar == v).
// `incomplete` (complete == false) means an exact squarefree/gcd step or a psc
// submatrix exceeded budget — caller MUST treat the closure as incomplete.
LazardOpResult lazardProjectStep(const std::vector<RationalPolynomial>& E, VarId v,
                                 const LazardProjectionConfig& cfg = LazardProjectionConfig());

}  // namespace nlcolver
