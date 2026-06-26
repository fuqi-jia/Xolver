#pragma once

#include <gmpxx.h>
#include <map>
#include <vector>

namespace xolver {
namespace omega {

// A linear-INTEGER constraint over integer variables: (Σ coeffs[v]·x_v + constant) rel 0.
// Sparse: only nonzero coefficients are stored; variable indices are arbitrary
// non-negative ints (the engine mints fresh ones above the input max for equality
// elimination). All coefficients/constant are exact integers (mpz_class).
struct Constraint {
    std::map<int, mpz_class> coeffs;       // var index -> nonzero coefficient
    mpz_class constant;                    // additive constant c
    enum Rel { Eq, Geq, Leq } rel = Geq;   // (Σ + c)  ==/>=/<=  0
};

enum class Result { Unsat, SatOrUnknown };

// SOUND integer-feasibility test for the CONJUNCTION of `cs` (Pugh's Omega test).
// Returns Unsat ONLY when the system provably has no integer solution; otherwise
// SatOrUnknown (no claim — the caller falls through to its complete engine).
// **Never asserts Sat**, so an incomplete implementation is still sound.
//
// Caller contract (for soundness):
//   - every variable ranges over the INTEGERS (no reals);
//   - Neq constraints are DROPPED before calling (dropping a constraint only
//     enlarges the solution set, so a proven Unsat still holds for the full system);
//   - nonlinear monomials are abstracted to FRESH free integer variables (a
//     relaxation; relaxed-Unsat ⟹ original-Unsat).
// `cs` is taken by value (the engine mutates it during elimination).
Result decide(std::vector<Constraint> cs);

}  // namespace omega
}  // namespace xolver
