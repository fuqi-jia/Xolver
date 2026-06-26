#pragma once

#include "theory/arith/nia/reasoners/OmegaTest.h"   // reuse omega::Constraint (sparse int linear)
#include <vector>

namespace xolver::modular {

enum class Result { Unsat, SatOrUnknown };

// Sound integer-infeasibility test via a SMALL-PRIME SCHEDULE.
//
// Over the EQUALITY subset of `cs` (each `Σ aᵢxᵢ + c == 0`), reduce the linear
// system A·x = b modulo each prime in {2,3,5,7,11,…} and run Gaussian elimination
// over GF(p). If the reduced system is INCONSISTENT mod any p (a pivot-free row
// with a nonzero right-hand side), then no integer solution exists ⇒ `Unsat`.
//
// SOUNDNESS: any integer solution of A·x = b reduces to a solution over GF(p), so
// GF(p)-infeasible ⟹ Z-infeasible. Inequalities are IGNORED (they don't reduce
// soundly mod p); using only the equality subset is sound because a subset being
// infeasible already proves the whole conjunction infeasible. We only ever assert
// `Unsat`; an incomplete check just returns `SatOrUnknown` more often.
//
// This catches SYSTEM-LEVEL obstructions the per-equation gcd test misses — e.g.
// x+y=0 ∧ x−y=1 forces 2x=1, which is infeasible mod 2 but whose individual
// equations each have coefficient-gcd 1. It is cheap (small dense GF(p) elimination)
// so it can run at Standard effort as an early refutation. `numPrimes` caps the
// schedule; oversized systems (many vars/rows) bail to SatOrUnknown (still sound).
Result decide(const std::vector<omega::Constraint>& cs, int numPrimes = 16);

}  // namespace xolver::modular
