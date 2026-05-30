#pragma once

#include "theory/arith/nra/nla/NlaCutTypes.h"
#include "theory/arith/poly/PolynomialKernel.h"

#include <vector>

namespace xolver {
namespace nla {

// NlaCutGenerator: produces NLA cuts from interval state.
//
// Phase A scope (this commit): single prototype — monotonicity-product
// cuts for non-negative intervals. Other kinds (Tangent, Horner,
// Proportional) ship in Phase B.
//
// Design: the generator is stateless — each call takes the inputs it
// needs and returns a vector of cuts. The caller (eventually a hook in
// CDCAC + a parallel NIA-side adapter) is responsible for collecting
// interval state from the active trail and feeding it in.
//
// Soundness role: every cut returned by a generator method must satisfy
// the NlaCut soundness invariant — under every assignment satisfying its
// `reasons`, `poly rel 0` holds. The grid certificate in the test suite
// pins this for each cut shape.
class NlaCutGenerator {
public:
    explicit NlaCutGenerator(PolynomialKernel& kernel);

    // Monotonicity product cut for `x * y` from two intervals where the
    // lower bounds are known to be non-negative. Returns up to two cuts:
    //   - lo cut:  x*y - lo_x * lo_y >= 0   (lower bound on the product)
    //   - hi cut:  hi_x * hi_y - x*y >= 0   (upper bound on the product)
    //
    // Requirements (cut omitted if violated):
    //   - lo_x present AND lo_x >= 0  ⇒ enables lo cut
    //   - hi_x present AND hi_y present ⇒ enables hi cut (lo_x, lo_y both
    //     must be >= 0 too, so the corner-point upper bound is achieved at
    //     (hi_x, hi_y); without lo_x >= 0 the product can be more negative)
    //
    // Sound for integer or rational variables. Bounds rounded to mpq.
    //
    // Reason set: union of xInt.reasons and yInt.reasons (deduped).
    std::vector<NlaCut> monotonicityProduct(const VarInterval& xInt,
                                            const VarInterval& yInt);

    // Monotonicity square cut for `x * x` from a single interval. When
    // lo >= 0, the square is monotonic on [lo, hi]; when hi <= 0 it is
    // monotonic decreasing. When 0 ∈ [lo, hi], the minimum is 0.
    // Returns up to two cuts:
    //   - lo cut:  x*x - (min over interval)^2 >= 0   (when computable)
    //   - hi cut:  max(lo^2, hi^2) - x*x >= 0         (always, if both
    //                                                  bounds present)
    std::vector<NlaCut> monotonicitySquare(const VarInterval& xInt);

private:
    PolynomialKernel& kernel_;
};

} // namespace nla
} // namespace xolver
