#include "theory/arith/nra/projection/SubresultantChain.h"

#include "theory/arith/poly/PolynomialKernel.h"

#include <cstdlib>
#include <utility>

namespace zolver {

namespace {
// ZOLVER_NRA_LIBPOLY_PSC: route principalSubresultantCoefficients through the
// libpoly psc chain instead of the O(n!) determinant. Default OFF; read once.
// Same idiom as ZOLVER_NRA_VARORDER_SIMPLEX in CdcacSolver.cpp.
bool libpolyPscEnabled() {
    static const bool kEnabled = [] {
        const char* e = std::getenv("ZOLVER_NRA_LIBPOLY_PSC");
        return e && (e[0]=='1'||e[0]=='t'||e[0]=='T'||e[0]=='y'||e[0]=='Y');
    }();
    return kEnabled;
}

// Recursive cofactor determinant over RationalPolynomial entries. Exact and
// simple; exponential, so callers bound the dimension via maxMatrixDim.
RationalPolynomial determinant(std::vector<std::vector<RationalPolynomial>> M) {
    int n = static_cast<int>(M.size());
    if (n == 0) return RationalPolynomial::fromConstant(mpq_class(1));
    if (n == 1) return M[0][0];
    if (n == 2) return M[0][0] * M[1][1] - M[0][1] * M[1][0];

    RationalPolynomial det = RationalPolynomial::fromConstant(mpq_class(0));
    for (int col = 0; col < n; ++col) {
        std::vector<std::vector<RationalPolynomial>> minor;
        minor.reserve(n - 1);
        for (int row = 1; row < n; ++row) {
            std::vector<RationalPolynomial> minorRow;
            minorRow.reserve(n - 1);
            for (int c = 0; c < n; ++c) {
                if (c == col) continue;
                minorRow.push_back(M[row][c]);
            }
            minor.push_back(std::move(minorRow));
        }
        RationalPolynomial md = determinant(std::move(minor));
        mpq_class sign = (col % 2 == 0) ? mpq_class(1) : mpq_class(-1);
        det += M[0][col] * md * RationalPolynomial::fromConstant(sign);
    }
    return det;
}

// Coefficient (a RationalPolynomial in the other variables) of v^deg in the
// shifted polynomial v^shift * f, where `coef[i]` = coeff of v^i in f.
RationalPolynomial shiftedCoeff(const std::vector<RationalPolynomial>& coef,
                                int shift, int deg) {
    int idx = deg - shift;
    if (idx < 0 || idx >= static_cast<int>(coef.size())) {
        return RationalPolynomial::fromConstant(mpq_class(0));
    }
    return coef[idx];
}

} // namespace

PscChainResult principalSubresultantCoefficients(
    const RationalPolynomial& pIn,
    const RationalPolynomial& qIn,
    VarId v,
    int maxMatrixDim,
    PolynomialKernel* kernel,
    bool forcePsc) {

    PscChainResult out;

    int dp = pIn.degree(v);
    int dq = qIn.degree(v);

    // A side with degree < 1 in v has no subresultant chain (the coefficient-
    // extraction step of the projection handles its coefficients separately).
    if (dp < 1 || dq < 1) return out;

    // ----- libpoly psc path (ZOLVER_NRA_LIBPOLY_PSC, default OFF) -----------
    // Verdict-preserving perf path: route through libpoly's lp_polynomial_psc
    // (no matrix-dim bound, so budgetExceeded is never set — the recovery
    // source). CAD-equivalent to the determinant up to a nonzero rational scale
    // per entry (proven by the differential oracle in test_nra_libpoly_psc).
    // Only taken when a kernel is supplied AND the flag is ON; otherwise the
    // determinant path below runs unchanged.
    if (kernel != nullptr && (forcePsc || libpolyPscEnabled())) {
        // RP -> PolyId via the proven toPrimitiveInteger conversion (clears
        // denominators; a nonzero positive rational scale is benign for CAD).
        auto pNorm = pIn.toPrimitiveInteger(*kernel);
        auto qNorm = qIn.toPrimitiveInteger(*kernel);
        if (pNorm.ok() && qNorm.ok()) {
            std::vector<PolyId> chain = kernel->pscChain(pNorm.poly, qNorm.poly, v);
            out.budgetExceeded = false;   // no matrix-dim bound on this path
            out.psc.reserve(chain.size());
            bool conversionOk = true;
            for (PolyId id : chain) {
                auto rpOpt = RationalPolynomial::fromPolyId(id, *kernel);
                if (!rpOpt) { conversionOk = false; break; }
                rpOpt->normalize();
                out.psc.push_back(std::move(*rpOpt));
            }
            if (conversionOk) return out;
            // A conversion failed — fall through to the determinant reference.
            out.psc.clear();
            out.budgetExceeded = false;
        }
        // toPrimitiveInteger failed — fall through to the determinant path.
    }

    // Ensure deg_v(p) >= deg_v(q); sign is irrelevant for projection.
    const RationalPolynomial& p = (dp >= dq) ? pIn : qIn;
    const RationalPolynomial& q = (dp >= dq) ? qIn : pIn;
    int m = (dp >= dq) ? dp : dq;
    int n = (dp >= dq) ? dq : dp;

    std::vector<RationalPolynomial> pc = p.coefficients(v);   // size m+1
    std::vector<RationalPolynomial> qc = q.coefficients(v);   // size n+1

    out.psc.reserve(static_cast<size_t>(n));
    for (int j = 0; j < n; ++j) {
        int size = m + n - 2 * j;          // square dimension of M_{j,j}
        if (size > maxMatrixDim) {
            out.budgetExceeded = true;
            continue;
        }
        int topDeg = m + n - 1 - j;         // highest monomial degree (column 0)

        // Rows: v^k * p for k = n-1-j .. 0, then v^k * q for k = m-1-j .. 0.
        std::vector<std::vector<RationalPolynomial>> M;
        M.reserve(static_cast<size_t>(size));
        auto addRows = [&](const std::vector<RationalPolynomial>& coef, int maxShift) {
            for (int k = maxShift; k >= 0; --k) {
                std::vector<RationalPolynomial> row;
                row.reserve(static_cast<size_t>(size));
                for (int t = 0; t < size; ++t) {
                    row.push_back(shiftedCoeff(coef, k, topDeg - t));
                }
                M.push_back(std::move(row));
            }
        };
        addRows(pc, n - 1 - j);   // (n-j) rows
        addRows(qc, m - 1 - j);   // (m-j) rows

        RationalPolynomial d = determinant(std::move(M));
        d.normalize();
        out.psc.push_back(std::move(d));
    }

    return out;
}

} // namespace zolver
