#pragma once

// Exact linear algebra over Z (Smith Normal Form) and Q (Gaussian elimination)
// for Capability 5's two cores.

#include <gmpxx.h>
#include <vector>

namespace xolver {

using IntMatrix = std::vector<std::vector<mpz_class>>;
using RatMatrix = std::vector<std::vector<mpq_class>>;

// Smith Normal Form of an integer m×n matrix A:
//   U · A · V = D,  U ∈ GL_m(Z), V ∈ GL_n(Z), D diagonal, non-negative entries
//   with the divisibility chain d_1 | d_2 | …  (full Smith form).
struct SmithNormalForm {
    IntMatrix U;   // m×m, unimodular
    IntMatrix V;   // n×n, unimodular
    IntMatrix D;   // m×n, diagonal
    int rank = 0;  // number of non-zero diagonal entries
    int m = 0, n = 0;
};

// Compute the Smith Normal Form of A (A is copied).  A may be empty (m or n 0).
SmithNormalForm smithNormalForm(const IntMatrix& A);

// Matrix · vector over Z.
std::vector<mpz_class> matVec(const IntMatrix& M, const std::vector<mpz_class>& v);

} // namespace xolver
