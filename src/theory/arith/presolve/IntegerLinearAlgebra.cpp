#include "theory/arith/presolve/IntegerLinearAlgebra.h"

#include <algorithm>

namespace zolver {

namespace {

IntMatrix identity(int k) {
    IntMatrix I(k, std::vector<mpz_class>(k, mpz_class(0)));
    for (int i = 0; i < k; ++i) I[i][i] = 1;
    return I;
}

// row operations on (D, transform) where transform tracks the left factor U.
void rowSwap(IntMatrix& D, IntMatrix& U, int a, int b) {
    if (a == b) return;
    std::swap(D[a], D[b]);
    std::swap(U[a], U[b]);
}
// row_a += f * row_b   (in both D and U)
void rowAddMul(IntMatrix& D, IntMatrix& U, int a, int b, const mpz_class& f) {
    if (f == 0) return;
    int n = static_cast<int>(D[a].size());
    for (int k = 0; k < n; ++k) D[a][k] += f * D[b][k];
    int mm = static_cast<int>(U[a].size());
    for (int k = 0; k < mm; ++k) U[a][k] += f * U[b][k];
}
void rowNegate(IntMatrix& D, IntMatrix& U, int a) {
    for (auto& x : D[a]) x = -x;
    for (auto& x : U[a]) x = -x;
}

// col operations on (D, transform) where transform tracks the right factor V.
void colSwap(IntMatrix& D, IntMatrix& V, int a, int b) {
    if (a == b) return;
    int m = static_cast<int>(D.size());
    for (int i = 0; i < m; ++i) std::swap(D[i][a], D[i][b]);
    int nn = static_cast<int>(V.size());
    for (int i = 0; i < nn; ++i) std::swap(V[i][a], V[i][b]);
}
// col_a += f * col_b   (in both D and V)
void colAddMul(IntMatrix& D, IntMatrix& V, int a, int b, const mpz_class& f) {
    if (f == 0) return;
    int m = static_cast<int>(D.size());
    for (int i = 0; i < m; ++i) D[i][a] += f * D[i][b];
    int nn = static_cast<int>(V.size());
    for (int i = 0; i < nn; ++i) V[i][a] += f * V[i][b];
}

mpz_class fdiv(const mpz_class& a, const mpz_class& b) {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return q;
}

}  // namespace

SmithNormalForm smithNormalForm(const IntMatrix& A) {
    SmithNormalForm r;
    r.m = static_cast<int>(A.size());
    r.n = r.m ? static_cast<int>(A[0].size()) : 0;
    r.D = A;
    r.U = identity(r.m);
    r.V = identity(r.n);
    const int m = r.m, n = r.n;
    IntMatrix& D = r.D;
    IntMatrix& U = r.U;
    IntMatrix& V = r.V;

    int t = 0;
    while (t < m && t < n) {
        // Find any non-zero entry in the submatrix D[t..][t..]; pick minimal abs.
        int pi = -1, pj = -1;
        mpz_class best;
        for (int i = t; i < m; ++i) {
            for (int j = t; j < n; ++j) {
                if (D[i][j] != 0) {
                    mpz_class a = abs(D[i][j]);
                    if (pi < 0 || a < best) { best = a; pi = i; pj = j; }
                }
            }
        }
        if (pi < 0) break;  // submatrix all zero — done
        rowSwap(D, U, t, pi);
        colSwap(D, V, t, pj);

        // Clear column t and row t by repeated Euclidean reduction.
        bool clean = false;
        while (!clean) {
            clean = true;
            // Column t: reduce entries below/above the pivot.
            for (int i = 0; i < m; ++i) {
                if (i == t || D[i][t] == 0) continue;
                mpz_class q = fdiv(D[i][t], D[t][t]);
                rowAddMul(D, U, i, t, -q);
                if (D[i][t] != 0) {        // remainder nonzero: promote, restart
                    rowSwap(D, U, t, i);
                    clean = false;
                }
            }
            // Row t: reduce entries left/right of the pivot.
            for (int j = 0; j < n; ++j) {
                if (j == t || D[t][j] == 0) continue;
                mpz_class q = fdiv(D[t][j], D[t][t]);
                colAddMul(D, V, j, t, -q);
                if (D[t][j] != 0) {
                    colSwap(D, V, t, j);
                    clean = false;
                }
            }
        }
        if (D[t][t] < 0) rowNegate(D, U, t);
        ++t;
    }
    r.rank = 0;
    for (int i = 0; i < m && i < n; ++i) if (D[i][i] != 0) ++r.rank;

    // Enforce the Smith divisibility chain d_i | d_{i+1} on the diagonal.
    // (Not required for solving, but yields the canonical form.)
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i + 1 < m && i + 1 < n; ++i) {
            if (D[i][i] == 0 || D[i + 1][i + 1] == 0) continue;
            if (D[i + 1][i + 1] % D[i][i] != 0) {
                // col_i += col_{i+1}, then re-diagonalize the 2×2 block.
                colAddMul(D, V, i, i + 1, mpz_class(1));
                // reduce this 2×2 block (rows/cols i, i+1) to diagonal again
                bool clean = false;
                while (!clean) {
                    clean = true;
                    for (int rr = i; rr <= i + 1; ++rr) {
                        if (rr == i || D[rr][i] == 0) continue;
                        mpz_class q = fdiv(D[rr][i], D[i][i]);
                        rowAddMul(D, U, rr, i, -q);
                        if (D[rr][i] != 0) { rowSwap(D, U, i, rr); clean = false; }
                    }
                    for (int cc = i; cc <= i + 1; ++cc) {
                        if (cc == i || D[i][cc] == 0) continue;
                        mpz_class q = fdiv(D[i][cc], D[i][i]);
                        colAddMul(D, V, cc, i, -q);
                        if (D[i][cc] != 0) { colSwap(D, V, i, cc); clean = false; }
                    }
                }
                if (D[i][i] < 0) rowNegate(D, U, i);
                if (i + 1 < m && i + 1 < n && D[i + 1][i + 1] < 0) rowNegate(D, U, i + 1);
                changed = true;
            }
        }
    }
    return r;
}

std::vector<mpz_class> matVec(const IntMatrix& M, const std::vector<mpz_class>& v) {
    std::vector<mpz_class> out(M.size(), mpz_class(0));
    for (size_t i = 0; i < M.size(); ++i) {
        mpz_class acc = 0;
        for (size_t j = 0; j < M[i].size() && j < v.size(); ++j) acc += M[i][j] * v[j];
        out[i] = acc;
    }
    return out;
}

} // namespace zolver
