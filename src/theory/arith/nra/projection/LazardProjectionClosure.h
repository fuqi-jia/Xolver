#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/projection/LazardProjectionOperator.h"
#include "expr/types.h"
#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

namespace nlcolver {

// ---------------------------------------------------------------------------
// LazardProjectionClosure — the Lazard projection of a constraint set, composed
// ONCE per solve (projection is sample-independent), top variable down. For each
// level k it produces the boundary polynomials (in x_0..x_k) that the Lazard
// lifter will valuation-evaluate. Every entry carries a LazardProjectionSource
// so the step-E replay validator can reconstruct it ([H7]).
//
// Operator (per LAZARD.md): squarefree primitive basis + leading/trailing
// coefficients + discriminants + pairwise resultants — NOT Collins' full
// coefficient list + PSC chain.
//
// SOUNDNESS CONTRACT: if build() returns a reason != None the closure is
// INCOMPLETE and no UNSAT may rest on it (caller => Unknown). A zero
// resultant/discriminant (common/repeated factor) is SKIPPED, not bailed (the
// shared factor's roots are roots of the source polynomials, already boundaries).
// closureId keys a cache that must NOT be reused across a different active set.
// ---------------------------------------------------------------------------

using ProjectionClosureId = uint32_t;

class LazardProjectionClosure {
public:
    struct Entry {
        RationalPolynomial poly;
        int mainVarLevel = -1;        // index in varOrder; -1 if constant
        LazardProjectionSource source;
    };

    struct Config {
        int maxMatrixDim = 9;
        size_t maxPolys = 8000;
        ProjectionClosureId closureId = 0;   // fingerprint of active set + order + mode
        Config() = default;
    };

    LazardIncompleteReason build(
        const std::vector<RationalPolynomial>& constraints,
        const std::vector<VarId>& varOrder, const Config& cfg);
    LazardIncompleteReason build(
        const std::vector<RationalPolynomial>& constraints,
        const std::vector<VarId>& varOrder) {
        return build(constraints, varOrder, Config());
    }

    bool complete() const { return reason_ == LazardIncompleteReason::None; }
    LazardIncompleteReason reason() const { return reason_; }
    ProjectionClosureId closureId() const { return cfg_.closureId; }

    const std::vector<Entry>& entries() const { return entries_; }
    const std::vector<int>& levelPolys(int k) const;

private:
    std::vector<Entry> entries_;
    std::vector<std::vector<int>> levelPolys_;
    std::vector<VarId> varOrder_;
    Config cfg_;
    LazardIncompleteReason reason_ = LazardIncompleteReason::None;
    std::unordered_map<std::string, int> dedup_;
    std::vector<int> emptyLevel_;

    int mainVarLevelOf(const RationalPolynomial& p) const;
    static std::string canonicalKey(RationalPolynomial p);   // up-to-unit normalized key
    int intern(const RationalPolynomial& p, const LazardProjectionSource& src);
    int lookupIndex(const RationalPolynomial& p) const;      // -1 if not interned
    void projectLevel(const std::vector<int>& inputIds, VarId elimVar);
};

}  // namespace nlcolver
