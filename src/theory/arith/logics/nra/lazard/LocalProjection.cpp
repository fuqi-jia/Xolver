#include "theory/arith/logics/nra/lazard/LocalProjection.h"
#include "theory/arith/logics/nra/preprocess/DegeneracyResolver.h"
#include <algorithm>
#include <unordered_set>

namespace xolver {

// ============================================================================
// Determinant of a matrix of RationalPolynomial (recursive cofactor expansion)
// ============================================================================

static RationalPolynomial determinant(std::vector<std::vector<RationalPolynomial>> M) {
    int n = static_cast<int>(M.size());
    if (n == 0) return RationalPolynomial::fromConstant(mpq_class(1));
    if (n == 1) return M[0][0];
    if (n == 2) {
        return M[0][0] * M[1][1] - M[0][1] * M[1][0];
    }

    RationalPolynomial det = RationalPolynomial::fromConstant(mpq_class(0));
    for (int col = 0; col < n; ++col) {
        // Build minor
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
        RationalPolynomial minorDet = determinant(std::move(minor));
        mpq_class sign = (col % 2 == 0) ? mpq_class(1) : mpq_class(-1);
        det += M[0][col] * minorDet * RationalPolynomial::fromConstant(sign);
    }
    return det;
}

// ============================================================================
// Resultant via Sylvester matrix
// ============================================================================

RationalPolynomial resultant(
    const RationalPolynomial& p,
    const RationalPolynomial& q,
    VarId v) {

    int m = p.degree(v);
    int n = q.degree(v);

    if (m < 0 || n < 0) {
        // One or both are zero polynomials
        return RationalPolynomial::fromConstant(mpq_class(0));
    }
    if (m == 0 && n == 0) {
        // Both are constants w.r.t. v
        return RationalPolynomial::fromConstant(mpq_class(1));
    }
    if (m == 0) {
        // p is constant w.r.t. v: resultant = p^n
        return p.pow(static_cast<uint32_t>(n));
    }
    if (n == 0) {
        // q is constant w.r.t. v: resultant = q^m
        return q.pow(static_cast<uint32_t>(m));
    }

    auto pCoeffs = p.coefficients(v);
    auto qCoeffs = q.coefficients(v);

    // Ensure sizes are m+1 and n+1
    if (static_cast<int>(pCoeffs.size()) != m + 1) {
        pCoeffs.resize(m + 1);
    }
    if (static_cast<int>(qCoeffs.size()) != n + 1) {
        qCoeffs.resize(n + 1);
    }

    // Build Sylvester matrix of size (m+n) x (m+n)
    // coefficients() returns [a_0, a_1, ..., a_m] where a_i = coeff of v^i
    // Sylvester matrix needs [a_m, a_{m-1}, ..., a_0] across columns
    int sz = m + n;
    std::vector<std::vector<RationalPolynomial>> M(sz, std::vector<RationalPolynomial>(sz));

    // First n rows: coefficients of p (high-to-low degree), shifted right by row index
    for (int row = 0; row < n; ++row) {
        for (int col = 0; col < sz; ++col) {
            int deg = col - row;  // which coefficient of p, counting from high degree
            int coeffIdx = m - deg;  // index in pCoeffs (0 = constant, m = leading)
            if (coeffIdx >= 0 && coeffIdx <= m) {
                M[row][col] = pCoeffs[coeffIdx];
            } else {
                M[row][col] = RationalPolynomial::fromConstant(mpq_class(0));
            }
        }
    }

    // Last m rows: coefficients of q (high-to-low degree), shifted right by row index
    for (int row = 0; row < m; ++row) {
        for (int col = 0; col < sz; ++col) {
            int deg = col - row;
            int coeffIdx = n - deg;
            if (coeffIdx >= 0 && coeffIdx <= n) {
                M[n + row][col] = qCoeffs[coeffIdx];
            } else {
                M[n + row][col] = RationalPolynomial::fromConstant(mpq_class(0));
            }
        }
    }

    return determinant(std::move(M));
}

// ============================================================================
// Local Projection Engine
// ============================================================================

static std::string polyKeyString(const RationalPolynomial& p) {
    // Simple key: iterate terms and build a string
    std::string key;
    for (const auto& [mon, coeff] : p.terms()) {
        key += coeff.get_str() + ":";
        for (const auto& [v, e] : mon) {
            key += std::to_string(v) + "^" + std::to_string(e) + ";";
        }
        key += "|";
    }
    return key;
}

std::vector<ReasonedPolynomial> LocalProjectionEngine::normalizeAndDedup(
    const std::vector<ReasonedPolynomial>& input) {
    std::vector<ReasonedPolynomial> result;
    std::unordered_set<std::string> seen;
    for (const auto& rp : input) {
        if (rp.poly.isZero()) continue;
        std::string key = polyKeyString(rp.poly);
        if (seen.insert(key).second) {
            result.push_back(rp);
        }
    }
    return result;
}

LocalProjectionResult LocalProjectionEngine::project(
    const std::vector<ReasonedPolynomial>& input,
    VarId eliminateVar) {

    LocalProjectionResult result;
    auto deduped = normalizeAndDedup(input);

    for (const auto& rp : deduped) {
        const auto& p = rp.poly;

        if (p.isZero()) {
            result.hasDegeneracy = true;
            continue;
        }

        // Polynomial does NOT contain eliminateVar: carry down to parent level
        if (!p.contains(eliminateVar)) {
            if (!p.isConstant()) {
                result.polys.push_back(rp);
            }
            continue;
        }

        // Contains eliminateVar: do Collins-style projection
        // 1. Coefficients (excluding leading, which is handled by discriminant)
        auto coeffs = p.coefficients(eliminateVar);
        for (size_t i = 0; i < coeffs.size(); ++i) {
            if (!coeffs[i].isZero() && !coeffs[i].isConstant()) {
                result.polys.push_back({
                    coeffs[i],
                    PolyRole::ProjectionPolynomial,
                    rp.reasons
                });
            }
        }

        // 2. Discriminant = resultant(p, p', eliminateVar)
        auto dp = p.derivative(eliminateVar);
        if (!dp.isZero()) {
            auto disc = resultant(p, dp, eliminateVar);
            if (disc.isZero()) {
                // V2-5: try to resolve self-degeneracy
                DegeneracyResolver resolver;
                auto resolution = resolver.resolveSelfDegeneracy(rp, eliminateVar);
                if (resolution.hasUnresolvedDegeneracy) {
                    result.hasDegeneracy = true;
                    result.degeneracyReason = resolution.reason;
                } else if (!resolution.replacementPolys.empty()) {
                    // Use squarefree replacement
                    result.polys.insert(result.polys.end(),
                        resolution.replacementPolys.begin(),
                        resolution.replacementPolys.end());
                }
                // If resolution produced no replacement (already constant gcd),
                // continue without adding discriminant
            } else if (!disc.isConstant()) {
                result.polys.push_back({
                    disc,
                    PolyRole::ProjectionPolynomial,
                    rp.reasons
                });
            }
        }
    }

    // 3. Pairwise resultants
    for (size_t i = 0; i < deduped.size(); ++i) {
        for (size_t j = i + 1; j < deduped.size(); ++j) {
            const auto& pi = deduped[i].poly;
            const auto& pj = deduped[j].poly;

            if (polyKeyString(pi) == polyKeyString(pj)) continue;
            if (!pi.contains(eliminateVar) || !pj.contains(eliminateVar)) continue;

            auto r = resultant(pi, pj, eliminateVar);
            if (r.isZero()) {
                // V2-5: try to resolve pair-degeneracy
                DegeneracyResolver resolver;
                auto resolution = resolver.resolvePairDegeneracy(
                    deduped[i], deduped[j], eliminateVar);
                if (resolution.hasUnresolvedDegeneracy) {
                    result.hasDegeneracy = true;
                    result.degeneracyReason = resolution.reason;
                } else if (!resolution.replacementPolys.empty()) {
                    result.polys.insert(result.polys.end(),
                        resolution.replacementPolys.begin(),
                        resolution.replacementPolys.end());
                }
            } else if (!r.isConstant()) {
                // Merge reasons
                std::vector<SatLit> mergedReasons = deduped[i].reasons;
                mergedReasons.insert(mergedReasons.end(),
                    deduped[j].reasons.begin(), deduped[j].reasons.end());
                // Deduplicate reasons
                std::sort(mergedReasons.begin(), mergedReasons.end(),
                    [](SatLit a, SatLit b) {
                        if (a.var != b.var) return a.var < b.var;
                        return a.sign < b.sign;
                    });
                mergedReasons.erase(std::unique(mergedReasons.begin(), mergedReasons.end(),
                    [](SatLit a, SatLit b) {
                        return a.var == b.var && a.sign == b.sign;
                    }), mergedReasons.end());

                result.polys.push_back({
                    r,
                    PolyRole::ProjectionPolynomial,
                    mergedReasons
                });
            }
        }
    }

    // Final dedup
    result.polys = normalizeAndDedup(result.polys);
    return result;
}

} // namespace xolver
