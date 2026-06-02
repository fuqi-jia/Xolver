#include "theory/arith/nia/farkas/FarkasOrBranchSolver.h"

#include <algorithm>
#include <functional>
#include <numeric>
#include <set>
#include <unordered_set>

namespace xolver::farkas {

namespace {

// Helper: get var name from an ExprId or nullopt.
std::optional<std::string> varName(const CoreIr& ir, ExprId id) {
    const auto& e = ir.get(id);
    if (e.kind != Kind::Variable) return std::nullopt;
    if (auto* s = std::get_if<std::string>(&e.payload.value)) return *s;
    return std::nullopt;
}

// Parse integer constant (ConstInt or ConstReal-with-integer-string).
std::optional<mpq_class> constAsRational(const CoreIr& ir, ExprId id) {
    const auto& e = ir.get(id);
    if (e.kind == Kind::ConstInt || e.kind == Kind::ConstReal) {
        if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
            return mpq_class(static_cast<long>(*i));
        }
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            try { return mpq_class(*s); } catch (...) {}
        }
    }
    if (e.kind == Kind::Neg && e.children.size() == 1) {
        if (auto v = constAsRational(ir, e.children[0])) return -(*v);
    }
    return std::nullopt;
}

// Try to compute the integer-valued constant of a polynomial sub-expression
// under bounded-var substitutions B. Returns nullopt if the sub-expression
// references any variable NOT in B AND NOT recognized as a lambda or CT
// (caller decides whether to treat that as a failure or a CT contribution).
//
// This handles: Const, Variable, Neg, Mul, Add, Sub.
// For Mul: every factor must be a constant or B-substitutable variable.
// For Add/Sub: recursive on summands.
std::optional<mpq_class> evalConst(
    const CoreIr& ir,
    ExprId id,
    const std::unordered_map<std::string, mpz_class>& B)
{
    const auto& e = ir.get(id);
    if (e.kind == Kind::ConstInt || e.kind == Kind::ConstReal) {
        return constAsRational(ir, id);
    }
    if (e.kind == Kind::Variable) {
        if (auto vn = varName(ir, id)) {
            auto it = B.find(*vn);
            if (it != B.end()) return mpq_class(it->second);
        }
        return std::nullopt;   // var not in B → uneval-able as constant
    }
    if (e.kind == Kind::Neg && e.children.size() == 1) {
        if (auto v = evalConst(ir, e.children[0], B)) return -(*v);
        return std::nullopt;
    }
    if (e.kind == Kind::Add) {
        mpq_class acc = 0;
        for (ExprId c : e.children) {
            if (auto v = evalConst(ir, c, B)) acc += *v;
            else return std::nullopt;
        }
        return acc;
    }
    if (e.kind == Kind::Sub) {
        if (e.children.empty()) return std::nullopt;
        auto first = evalConst(ir, e.children[0], B);
        if (!first) return std::nullopt;
        mpq_class acc = *first;
        for (std::size_t i = 1; i < e.children.size(); ++i) {
            auto v = evalConst(ir, e.children[i], B);
            if (!v) return std::nullopt;
            acc -= *v;
        }
        return acc;
    }
    if (e.kind == Kind::Mul) {
        mpq_class acc = 1;
        for (ExprId c : e.children) {
            if (auto v = evalConst(ir, c, B)) acc *= *v;
            else return std::nullopt;
        }
        return acc;
    }
    return std::nullopt;
}

// Single-monomial extractor: walks a Mul / Variable / Neg(monomial) /
// Const sub-expression and returns:
//   - lambdaIdx ∈ [0, |lambdas|), CT-coef map, B-substituted coefficient
// returned via output parameters.
// "ctCoefs" is the linear coefficient of each CT var that appears as a
// factor in this monomial (typically 0 or 1 such var). Bilinear monomials
// like (c * λ_j * v_k) where v_k is bounded → coefficient c * B(v_k).
// Where v_k is CT → CT-side coefficient.
// Returns false on shape failure (e.g. λ² or two CTs).
//
// Output:
//   lambdaIdx: -1 if no λ factor (pure constant after B-sub), else index
//   ctVar: name of CT-like var factor if any (empty = none)
//   coef: numeric coefficient (constant times B-substituted bounded factors)
struct MonomialInfo {
    int lambdaIdx = -1;
    std::string ctVar;          // empty when no CT factor
    std::string residName;      // empty when no residual co-var factor
    mpq_class coef = 1;
};

bool extractMonomial(
    const CoreIr& ir,
    ExprId id,
    const std::unordered_map<std::string, int>& lambdaIndexOf,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::unordered_set<std::string>& ctVars,
    const std::unordered_set<std::string>& residCoVars,
    MonomialInfo& out)
{
    const auto& e = ir.get(id);
    out = MonomialInfo{};
    out.coef = 1;

    // Walk a list of "factors" (Mul children, or just the single expr if
    // not a Mul). For each, classify as constant / λ / CT / bounded.
    std::vector<ExprId> factors;
    bool negate = false;
    {
        ExprId cur = id;
        // Strip outer Neg: Neg(x) = (-1) * x.
        while (ir.get(cur).kind == Kind::Neg && ir.get(cur).children.size() == 1) {
            negate = !negate;
            cur = ir.get(cur).children[0];
        }
        const auto& ce = ir.get(cur);
        if (ce.kind == Kind::Mul) {
            for (ExprId c : ce.children) factors.push_back(c);
        } else {
            factors.push_back(cur);
        }
    }

    int lambdaSeen = 0;
    int ctSeen = 0;
    for (ExprId f : factors) {
        const auto& fe = ir.get(f);
        // Constant factor — accumulate into coef.
        if (fe.kind == Kind::ConstInt || fe.kind == Kind::ConstReal) {
            if (auto c = constAsRational(ir, f)) out.coef *= *c;
            else return false;
            continue;
        }
        if (fe.kind == Kind::Neg) {
            if (auto c = evalConst(ir, f, B)) { out.coef *= *c; continue; }
            // Neg of a non-constant — recurse into the inner factor.
            if (fe.children.size() != 1) return false;
            MonomialInfo inner;
            if (!extractMonomial(ir, fe.children[0], lambdaIndexOf, B, ctVars, residCoVars, inner)) return false;
            // Multiply by -1.
            out.coef *= -inner.coef;
            if (inner.lambdaIdx >= 0) {
                if (lambdaSeen) return false;
                out.lambdaIdx = inner.lambdaIdx;
                lambdaSeen = 1;
            }
            if (!inner.ctVar.empty()) {
                if (ctSeen) return false;
                out.ctVar = inner.ctVar;
                ctSeen = 1;
            }
            if (!inner.residName.empty()) {
                if (!out.residName.empty()) return false;
                out.residName = inner.residName;
            }
            continue;
        }
        if (fe.kind == Kind::Variable) {
            auto vn = varName(ir, f);
            if (!vn) return false;
            // Classify: λ, CT, residual, or bounded (B-substitutable).
            auto lit = lambdaIndexOf.find(*vn);
            if (lit != lambdaIndexOf.end()) {
                if (lambdaSeen) return false;
                out.lambdaIdx = lit->second;
                lambdaSeen = 1;
                continue;
            }
            if (ctVars.count(*vn)) {
                if (ctSeen) return false;
                out.ctVar = *vn;
                ctSeen = 1;
                continue;
            }
            if (residCoVars.count(*vn)) {
                if (!out.residName.empty()) return false;  // 2 resid factors
                out.residName = *vn;
                continue;
            }
            // Bounded → substitute from B.
            auto bit = B.find(*vn);
            if (bit == B.end()) return false;
            out.coef *= mpq_class(bit->second);
            continue;
        }
        // For Add/Sub inside Mul we don't expand here; treat as failure
        // since proper poly expansion isn't supported in P1 v1.
        // However a pure constant Add/Sub (no vars) is fine.
        if (auto c = evalConst(ir, f, B)) { out.coef *= *c; continue; }
        return false;
    }

    if (negate) out.coef = -out.coef;
    return true;
}

} // namespace

// ---- evalUnderB (poly → pure rational, fails if any CT-var appears) ----
std::optional<mpq_class> FarkasOrBranchSolver::evalUnderB(
    ExprId polyId,
    const std::unordered_map<std::string, mpz_class>& B) const
{
    return evalConst(ir_, polyId, B);
}

// ---- extractEqRow: walk equality polynomial, build λ-coefficient row ----
std::optional<FarkasOrBranchSolver::EqRow>
FarkasOrBranchSolver::extractEqRow(
    ExprId atomId,
    const std::vector<std::string>& lambdas,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::unordered_set<std::string>& residCoVars) const
{
    const auto& e = ir_.get(atomId);
    if (e.kind != Kind::Eq || e.children.size() != 2) return std::nullopt;

    // One side must be the constant 0 (post-normalization).
    auto rhsConst = constAsRational(ir_, e.children[1]);
    auto lhsConst = constAsRational(ir_, e.children[0]);
    ExprId polyId;
    mpq_class rhsValue = 0;
    if (rhsConst) { polyId = e.children[0]; rhsValue = *rhsConst; }
    else if (lhsConst) { polyId = e.children[1]; rhsValue = *lhsConst; }
    else return std::nullopt;

    std::unordered_map<std::string, int> lambdaIndexOf;
    for (std::size_t i = 0; i < lambdas.size(); ++i) lambdaIndexOf[lambdas[i]] = (int)i;
    std::unordered_set<std::string> emptyCt;   // equalities are CT-free per Stroeder

    EqRow row;
    row.coeffs.assign(lambdas.size(), mpq_class(0));
    row.constant = -rhsValue;

    std::function<bool(ExprId, int)> walk;
    walk = [&](ExprId id, int sign) -> bool {
        const auto& pe = ir_.get(id);
        if (pe.kind == Kind::Add) {
            for (ExprId c : pe.children) if (!walk(c, sign)) return false;
            return true;
        }
        if (pe.kind == Kind::Sub) {
            if (pe.children.empty()) return false;
            if (!walk(pe.children[0], sign)) return false;
            for (std::size_t i = 1; i < pe.children.size(); ++i) {
                if (!walk(pe.children[i], -sign)) return false;
            }
            return true;
        }
        if (pe.kind == Kind::Neg) {
            if (pe.children.size() != 1) return false;
            return walk(pe.children[0], -sign);
        }
        MonomialInfo m;
        if (!extractMonomial(ir_, id, lambdaIndexOf, B, emptyCt, residCoVars, m)) return false;
        if (!m.ctVar.empty()) return false;   // equality must be CT-free
        mpq_class scoef = mpq_class(sign) * m.coef;
        if (m.lambdaIdx >= 0) {
            row.coeffs[m.lambdaIdx] += scoef;
        } else if (!m.residName.empty()) {
            row.residCoeffs[m.residName] += scoef;
        } else {
            row.constant += scoef;
        }
        return true;
    };
    if (!walk(polyId, 1)) return std::nullopt;
    return row;
}

std::optional<FarkasOrBranchSolver::IneqRow>
FarkasOrBranchSolver::extractIneqRow(
    ExprId atomId,
    const std::vector<std::string>& lambdas,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::vector<std::string>& ctVars,
    const std::unordered_set<std::string>& residCoVars) const
{
    const auto& e = ir_.get(atomId);
    IneqRow::Rel rel;
    switch (e.kind) {
        case Kind::Geq: rel = IneqRow::Rel::Geq; break;
        case Kind::Gt:  rel = IneqRow::Rel::Gt;  break;
        case Kind::Leq: rel = IneqRow::Rel::Leq; break;
        case Kind::Lt:  rel = IneqRow::Rel::Lt;  break;
        case Kind::Eq:  rel = IneqRow::Rel::Eq;  break;
        default: return std::nullopt;
    }
    if (e.children.size() != 2) return std::nullopt;
    auto rhsConst = constAsRational(ir_, e.children[1]);
    auto lhsConst = constAsRational(ir_, e.children[0]);
    ExprId polyId;
    mpq_class rhsValue = 0;
    bool polyOnLeft;
    if (rhsConst) { polyId = e.children[0]; rhsValue = *rhsConst; polyOnLeft = true; }
    else if (lhsConst) { polyId = e.children[1]; rhsValue = *lhsConst; polyOnLeft = false; }
    else return std::nullopt;

    std::unordered_map<std::string, int> lambdaIndexOf;
    for (std::size_t i = 0; i < lambdas.size(); ++i) lambdaIndexOf[lambdas[i]] = (int)i;
    std::unordered_set<std::string> ctSet(ctVars.begin(), ctVars.end());

    IneqRow row;
    row.lambdaCoeffs.assign(lambdas.size(), mpq_class(0));
    row.constant = -rhsValue;
    row.rel = rel;

    // Flip relation if polyOnLeft is false (poly is on right side):
    //   (0 ≤ poly)  ≡  (poly ≥ 0)
    //   (0 < poly)  ≡  (poly > 0)
    if (!polyOnLeft) {
        switch (row.rel) {
            case IneqRow::Rel::Leq: row.rel = IneqRow::Rel::Geq; break;
            case IneqRow::Rel::Lt:  row.rel = IneqRow::Rel::Gt;  break;
            case IneqRow::Rel::Geq: row.rel = IneqRow::Rel::Leq; break;
            case IneqRow::Rel::Gt:  row.rel = IneqRow::Rel::Lt;  break;
            case IneqRow::Rel::Eq:  break;
        }
        row.constant = rhsValue;  // poly rel rhs → poly - rhs rel 0; rhs is on LHS here, so flip sign
    }

    std::function<bool(ExprId, int)> walk;
    walk = [&](ExprId id, int sign) -> bool {
        const auto& pe = ir_.get(id);
        if (pe.kind == Kind::Add) {
            for (ExprId c : pe.children) if (!walk(c, sign)) return false;
            return true;
        }
        if (pe.kind == Kind::Sub) {
            if (pe.children.empty()) return false;
            if (!walk(pe.children[0], sign)) return false;
            for (std::size_t i = 1; i < pe.children.size(); ++i) {
                if (!walk(pe.children[i], -sign)) return false;
            }
            return true;
        }
        if (pe.kind == Kind::Neg) {
            if (pe.children.size() != 1) return false;
            return walk(pe.children[0], -sign);
        }
        MonomialInfo m;
        if (!extractMonomial(ir_, id, lambdaIndexOf, B, ctSet, residCoVars, m)) return false;
        mpq_class signed_coef = mpq_class(sign) * m.coef;
        if (m.lambdaIdx >= 0 && !m.ctVar.empty()) {
            row.bilinearCoeffs.emplace_back(m.lambdaIdx, m.ctVar, signed_coef);
            return true;
        }
        if (m.lambdaIdx >= 0) {
            row.lambdaCoeffs[m.lambdaIdx] += signed_coef;
        } else if (!m.ctVar.empty()) {
            row.ctCoeffs[m.ctVar] += signed_coef;
        } else if (!m.residName.empty()) {
            row.residCoeffs[m.residName] += signed_coef;
        } else {
            row.constant += signed_coef;
        }
        return true;
    };
    if (!walk(polyId, 1)) return std::nullopt;
    return row;
}

// ---- Q-matrix Gaussian elimination + primitive non-negative integer ray.
//
// Given matrix A_S (rows × cols), reduce to row-echelon form, find null
// space basis. If null space dim == 1, scale to primitive integer vector
// with consistent sign, check non-negativity. If dim > 1 or 0, return
// empty.
std::vector<mpz_class> FarkasOrBranchSolver::findPrimitiveNonNegRay(
    const std::vector<std::vector<mpq_class>>& A_S_in) const
{
    if (A_S_in.empty() || A_S_in[0].empty()) return {};
    std::size_t rows = A_S_in.size();
    std::size_t cols = A_S_in[0].size();
    // Copy A_S so we can row-reduce.
    std::vector<std::vector<mpq_class>> A = A_S_in;

    // Row reduction with partial pivoting. Result: pivot columns and
    // free columns identified.
    std::vector<int> pivotCol(rows, -1);   // pivot column for each row, or -1
    std::vector<int> rowOfCol(cols, -1);   // which row pivots this col
    std::size_t r = 0;
    for (std::size_t c = 0; c < cols && r < rows; ++c) {
        // Find a pivot in column c at row >= r.
        std::size_t pivot = r;
        bool found = false;
        for (std::size_t i = r; i < rows; ++i) {
            if (A[i][c] != 0) { pivot = i; found = true; break; }
        }
        if (!found) continue;
        std::swap(A[r], A[pivot]);
        mpq_class scale = A[r][c];
        for (std::size_t j = c; j < cols; ++j) A[r][j] /= scale;
        for (std::size_t i = 0; i < rows; ++i) {
            if (i == r) continue;
            mpq_class f = A[i][c];
            if (f != 0) {
                for (std::size_t j = c; j < cols; ++j) A[i][j] -= f * A[r][j];
            }
        }
        pivotCol[r] = (int)c;
        rowOfCol[c] = (int)r;
        ++r;
    }

    // Free columns = those without pivots.
    std::vector<std::size_t> freeCols;
    for (std::size_t c = 0; c < cols; ++c) {
        if (rowOfCol[c] == -1) freeCols.push_back(c);
    }
    if (freeCols.size() != 1) return {};   // not exactly 1 free → not unique-ray

    std::size_t f = freeCols[0];
    // Construct rational ray: ray[f] = 1, ray[pivot c] = -A[row_of_c][f].
    std::vector<mpq_class> rationalRay(cols, mpq_class(0));
    rationalRay[f] = 1;
    for (std::size_t c = 0; c < cols; ++c) {
        if (rowOfCol[c] != -1) rationalRay[c] = -A[rowOfCol[c]][f];
    }

    // Scale to primitive integer ray.
    // Step 1: clear denominators (multiply by LCM of denominators).
    mpz_class lcmDen = 1;
    for (const auto& q : rationalRay) {
        mpz_class d = q.get_den();
        mpz_class g; mpz_gcd(g.get_mpz_t(), lcmDen.get_mpz_t(), d.get_mpz_t());
        lcmDen = (lcmDen / g) * d;
    }
    std::vector<mpz_class> intRay(cols);
    for (std::size_t i = 0; i < cols; ++i) {
        mpq_class scaled = rationalRay[i] * mpq_class(lcmDen);
        intRay[i] = scaled.get_num();  // denominator now 1
    }
    // Step 2: divide by GCD of |entries|.
    mpz_class g = 0;
    for (const auto& v : intRay) {
        mpz_class av = abs(v);
        mpz_class ng; mpz_gcd(ng.get_mpz_t(), g.get_mpz_t(), av.get_mpz_t());
        g = ng;
    }
    if (g > 1) for (auto& v : intRay) v /= g;

    // Step 3: canonical sign (force first non-zero entry positive).
    for (std::size_t i = 0; i < cols; ++i) {
        if (intRay[i] != 0) {
            if (intRay[i] < 0) for (auto& v : intRay) v = -v;
            break;
        }
    }

    // Non-negativity check: every entry must be >= 0.
    for (const auto& v : intRay) if (v < 0) return {};

    return intRay;
}

// ---- Task #151: solve A_λ·λ + A_r·r = c with λ ∈ Z^L_≥0, r ∈ Z^R ----
//
// Replaces the brittle residual-grid enumeration. RREF the full
// augmented matrix [A_r | A_λ | c] with residual columns pivoted FIRST,
// so residuals become *dependent* on (free vars + RHS), and the
// remaining pure-λ rows form the only constraint on λ. Then enumerate
// free λ variables in {0..maxFreeRange} and recover pivot λs.
//
// Stroeder p21258 (z3-verified SAT): RFN1_main_x=20, RFN1_main_y=-26,
// RFN1_CT=-7, λ=(6,1,22,1,22,1). No grid covers ±26; only an augmented
// solve recovers these values from λ via the residual-pivot rows.
std::vector<FarkasOrBranchSolver::AugmentedSolution>
FarkasOrBranchSolver::solveAugmentedFarkas(
    const std::vector<std::vector<mpq_class>>& A_lambda,
    const std::vector<std::vector<mpq_class>>& A_resid,
    const std::vector<mpq_class>& c,
    const std::vector<std::string>& residNames,
    std::size_t maxFreeRange,
    std::size_t maxSolutions) const
{
    std::vector<AugmentedSolution> out;
    if (A_lambda.empty()) return out;
    std::size_t m = A_lambda.size();
    std::size_t L = A_lambda[0].empty() ? 0 : A_lambda[0].size();
    std::size_t R = residNames.size();
    if (R > 0 && (A_resid.empty() || A_resid[0].size() != R)) return out;
    if (c.size() != m) return out;

    // Build augmented matrix M of size m × (R + L + 1).
    // Column order: [resid_0..resid_{R-1} | lam_0..lam_{L-1} | c]
    std::vector<std::vector<mpq_class>> M(m, std::vector<mpq_class>(R + L + 1, mpq_class(0)));
    for (std::size_t i = 0; i < m; ++i) {
        for (std::size_t j = 0; j < R; ++j) {
            M[i][j] = A_resid[i][j];
        }
        for (std::size_t j = 0; j < L; ++j) {
            M[i][R + j] = A_lambda[i][j];
        }
        M[i][R + L] = c[i];
    }

    // RREF with column priority: residuals first (cols 0..R-1), then
    // lambdas (cols R..R+L-1). The constant column (R+L) is the RHS;
    // never pivot on it.
    std::vector<int> rowOfCol(R + L, -1);
    std::vector<int> pivotColOfRow(m, -1);
    std::size_t r = 0;
    for (std::size_t cc = 0; cc < R + L && r < m; ++cc) {
        std::size_t pivot = r;
        bool found = false;
        for (std::size_t i = r; i < m; ++i) {
            if (M[i][cc] != 0) { pivot = i; found = true; break; }
        }
        if (!found) continue;
        std::swap(M[r], M[pivot]);
        mpq_class scale = M[r][cc];
        for (std::size_t j = cc; j <= R + L; ++j) M[r][j] /= scale;
        for (std::size_t i = 0; i < m; ++i) {
            if (i == r) continue;
            mpq_class f = M[i][cc];
            if (f != 0) {
                for (std::size_t j = cc; j <= R + L; ++j) M[i][j] -= f * M[r][j];
            }
        }
        rowOfCol[cc] = (int)r;
        pivotColOfRow[r] = (int)cc;
        ++r;
    }

    // Consistency: rows with no pivot must have c entry = 0.
    for (std::size_t i = r; i < m; ++i) {
        if (M[i][R + L] != 0) return out;   // infeasible
    }

    // Identify free variables (non-pivot columns).
    std::vector<std::size_t> freeLambdaCols;
    std::vector<std::size_t> freeResidCols;
    for (std::size_t cc = 0; cc < R; ++cc) {
        if (rowOfCol[cc] == -1) freeResidCols.push_back(cc);
    }
    for (std::size_t cc = R; cc < R + L; ++cc) {
        if (rowOfCol[cc] == -1) freeLambdaCols.push_back(cc);
    }

    // Helper: compute pivoted-var value given free-var assignments.
    //   M[pivotRow] is the row x[pivotCol] + Σ_{free f} M[pivotRow][f] · x[f] = M[pivotRow][R+L]
    //   So x[pivotCol] = M[pivotRow][R+L] − Σ_{free f} M[pivotRow][f] · x[f]
    auto computePivotValue = [&](std::size_t pivotRow,
                                 const std::vector<mpq_class>& xFull) -> mpq_class {
        mpq_class val = M[pivotRow][R + L];
        for (std::size_t f = 0; f < R + L; ++f) {
            if (rowOfCol[f] == -1) {   // free col
                val -= M[pivotRow][f] * xFull[f];
            }
        }
        return val;
    };

    // Bounded enumeration of free λ values in {0..maxFreeRange}.
    // Free residuals are fixed at 0 (any integer would work; 0 is the
    // simplest representative for the residual nullspace).
    // For ≥3 free λs, restrict range to keep combos ≤ ~30³ = 27000.
    std::size_t numFreeL = freeLambdaCols.size();
    std::size_t actualRange = (maxFreeRange + 1);
    if (numFreeL >= 3) actualRange = 8;     // 8³ = 512
    if (numFreeL >= 4) actualRange = 5;     // 5⁴ = 625
    if (numFreeL >= 5) return out;          // too many free dims

    std::vector<std::size_t> idx(numFreeL, 0);
    auto enumerate = [&]() -> bool {
        // Build full xFull vector with current free assignments.
        std::vector<mpq_class> xFull(R + L, mpq_class(0));
        // Free residuals → 0 (already).
        // Free lambdas → idx[i].
        for (std::size_t i = 0; i < numFreeL; ++i) {
            xFull[freeLambdaCols[i]] = mpq_class((long)idx[i]);
        }
        // Compute pivot vars.
        for (std::size_t cc = 0; cc < R + L; ++cc) {
            if (rowOfCol[cc] != -1) {
                xFull[cc] = computePivotValue(rowOfCol[cc], xFull);
            }
        }
        // Check all λ vars are non-neg integers.
        std::vector<mpz_class> lambdaVals(L);
        for (std::size_t j = 0; j < L; ++j) {
            const auto& v = xFull[R + j];
            if (v.get_den() != 1) return false;
            mpz_class num = v.get_num();
            if (num < 0) return false;
            lambdaVals[j] = num;
        }
        // Reject the all-zero ray (caller can handle trivial-ray separately).
        bool allZero = true;
        for (const auto& v : lambdaVals) if (v != 0) { allZero = false; break; }
        if (allZero) return false;
        // Check residuals are integers.
        std::unordered_map<std::string, mpz_class> rVals;
        for (std::size_t j = 0; j < R; ++j) {
            const auto& v = xFull[j];
            if (v.get_den() != 1) return false;
            rVals[residNames[j]] = v.get_num();
        }
        AugmentedSolution sol;
        sol.lambdaValues = std::move(lambdaVals);
        sol.residValues  = std::move(rVals);
        out.push_back(std::move(sol));
        return true;
    };

    if (numFreeL == 0) {
        enumerate();   // single forced solution
    } else {
        while (true) {
            if (out.size() >= maxSolutions) break;
            enumerate();
            // Increment odometer.
            std::size_t pos = 0;
            while (pos < numFreeL) {
                ++idx[pos];
                if (idx[pos] < actualRange) break;
                idx[pos] = 0;
                ++pos;
            }
            if (pos == numFreeL) break;
        }
    }
    return out;
}

// ---- P1 v2: solve A·λ = c for non-neg integer λ (augmented system) ----
std::vector<mpz_class> FarkasOrBranchSolver::findNonNegIntegerSolution(
    const std::vector<std::vector<mpq_class>>& A_S_in,
    const std::vector<mpq_class>& c_in) const
{
    // Homogeneous fast path.
    bool homogeneous = true;
    for (const auto& ci : c_in) if (ci != 0) { homogeneous = false; break; }
    if (homogeneous) return findPrimitiveNonNegRay(A_S_in);

    if (A_S_in.empty()) return {};
    std::size_t rows = A_S_in.size();
    std::size_t cols = A_S_in[0].size();
    if (c_in.size() != rows) return {};

    // Augment with c as final column.
    std::vector<std::vector<mpq_class>> A(rows, std::vector<mpq_class>(cols + 1));
    for (std::size_t i = 0; i < rows; ++i) {
        for (std::size_t j = 0; j < cols; ++j) A[i][j] = A_S_in[i][j];
        A[i][cols] = c_in[i];
    }

    // RREF on the first `cols` columns; the constant column carries the RHS.
    std::vector<int> rowOfCol(cols, -1);
    std::size_t r = 0;
    for (std::size_t c = 0; c < cols && r < rows; ++c) {
        std::size_t pivot = r;
        bool found = false;
        for (std::size_t i = r; i < rows; ++i) {
            if (A[i][c] != 0) { pivot = i; found = true; break; }
        }
        if (!found) continue;
        std::swap(A[r], A[pivot]);
        mpq_class scale = A[r][c];
        for (std::size_t j = c; j <= cols; ++j) A[r][j] /= scale;
        for (std::size_t i = 0; i < rows; ++i) {
            if (i == r) continue;
            mpq_class f = A[i][c];
            if (f != 0) {
                for (std::size_t j = c; j <= cols; ++j) A[i][j] -= f * A[r][j];
            }
        }
        rowOfCol[c] = (int)r;
        ++r;
    }

    // Consistency: every all-zero A-row must have a zero RHS.
    for (std::size_t i = r; i < rows; ++i) {
        if (A[i][cols] != 0) return {};
    }

    std::vector<std::size_t> freeCols;
    for (std::size_t c = 0; c < cols; ++c) {
        if (rowOfCol[c] == -1) freeCols.push_back(c);
    }

    auto tryNonNegInt = [&](const std::vector<mpq_class>& sol)
        -> std::vector<mpz_class> {
        std::vector<mpz_class> out(sol.size());
        for (std::size_t i = 0; i < sol.size(); ++i) {
            if (sol[i].get_den() != 1) return {};
            mpz_class num = sol[i].get_num();
            if (num < 0) return {};
            out[i] = num;
        }
        return out;
    };

    // Particular: free vars = 0, pivot vars from RHS column.
    std::vector<mpq_class> particular(cols, mpq_class(0));
    for (std::size_t c = 0; c < cols; ++c) {
        if (rowOfCol[c] != -1) particular[c] = A[rowOfCol[c]][cols];
    }

    auto p_int = tryNonNegInt(particular);
    if (!p_int.empty()) return p_int;

    // 1D nullspace: try particular + t · homog for bounded rational t.
    // homog[f] = 1, homog[pivot c] = -A[rowOfCol[c]][f], homog[other free] = 0.
    if (freeCols.size() == 1) {
        std::size_t f = freeCols[0];
        std::vector<mpq_class> homog(cols, mpq_class(0));
        homog[f] = 1;
        for (std::size_t c = 0; c < cols; ++c) {
            if (rowOfCol[c] != -1) homog[c] = -A[rowOfCol[c]][f];
        }

        // Find LCM of denominators across (particular, homog) and search t.
        // Bounded integer t handles the typical small-coefficient case.
        // For finer granularity (Stroeder occasionally needs t with a small
        // rational), try t = k / D where D = LCM of homog denominators.
        mpz_class denomLcm = 1;
        for (const auto& q : homog) {
            mpz_class d = q.get_den();
            mpz_class g; mpz_gcd(g.get_mpz_t(), denomLcm.get_mpz_t(), d.get_mpz_t());
            denomLcm = (denomLcm / g) * d;
        }
        // Try t ∈ {-200/D, ..., 200/D}.
        for (long k = 1; k <= 200; ++k) {
            mpq_class t(k);
            t /= mpq_class(denomLcm);
            std::vector<mpq_class> sol(cols);
            for (std::size_t i = 0; i < cols; ++i) sol[i] = particular[i] + t * homog[i];
            auto s = tryNonNegInt(sol);
            if (!s.empty()) return s;
        }
        for (long k = -1; k >= -200; --k) {
            mpq_class t(k);
            t /= mpq_class(denomLcm);
            std::vector<mpq_class> sol(cols);
            for (std::size_t i = 0; i < cols; ++i) sol[i] = particular[i] + t * homog[i];
            auto s = tryNonNegInt(sol);
            if (!s.empty()) return s;
        }
    }

    return {};
}

// ---- deriveCtBound: substitute ray into IneqRow, derive bound on CT ----
CtBound FarkasOrBranchSolver::deriveCtBound(
    const IneqRow& row,
    const std::vector<mpz_class>& ray,
    const std::vector<std::string>& lambdaNames) const
{
    CtBound bound;
    // Pure-λ contribution to the constant side: sum(lambdaCoeffs · ray).
    mpq_class lambdaSide = 0;
    for (std::size_t i = 0; i < ray.size(); ++i) {
        lambdaSide += row.lambdaCoeffs[i] * mpq_class(ray[i]);
    }
    // CT residual coefficients: start from pure-CT terms, then add the
    // ray-weighted bilinear contributions.
    bound.residualCoefs = row.ctCoeffs;
    for (const auto& [lamIdx, ctVar, coef] : row.bilinearCoeffs) {
        bound.residualCoefs[ctVar] += coef * mpq_class(ray[lamIdx]);
    }
    bound.residualConst = lambdaSide + row.constant;
    switch (row.rel) {
        case IneqRow::Rel::Geq: bound.residualRel = CtBound::Rel::Geq; break;
        case IneqRow::Rel::Gt:  bound.residualRel = CtBound::Rel::Geq;  // poly > 0 → poly ≥ 1 for integer
                                bound.residualConst -= 1; break;
        case IneqRow::Rel::Leq: bound.residualRel = CtBound::Rel::Leq; break;
        case IneqRow::Rel::Lt:  bound.residualRel = CtBound::Rel::Leq;
                                bound.residualConst += 1; break;
        case IneqRow::Rel::Eq:  bound.residualRel = CtBound::Rel::Eq; break;
    }

    // Single-CT-var path: convert to interval if exactly one nonzero ctCoef.
    int nonZeroCt = 0;
    std::string ctVar;
    mpq_class ctCoef = 0;
    for (const auto& [v, c] : bound.residualCoefs) {
        if (c != 0) { ++nonZeroCt; ctVar = v; ctCoef = c; }
    }
    if (nonZeroCt == 1) {
        bound.hasInterval = true;
        bound.ctVar = ctVar;
        // constraint: ctCoef * CT + const rel 0
        //   Geq: ctCoef * CT >= -const → CT >= -const/ctCoef (if ctCoef>0)
        //                              → CT <= -const/ctCoef (if ctCoef<0)
        //   Leq: opposite direction.
        if (ctCoef == 0) {
            // No CT influence; check residualConst rel 0.
            if (bound.residualRel == CtBound::Rel::Geq &&
                bound.residualConst >= 0) {
                bound.ctLoFinite = bound.ctHiFinite = false;  // any CT works
            } else if (bound.residualRel == CtBound::Rel::Leq &&
                       bound.residualConst <= 0) {
                bound.ctLoFinite = bound.ctHiFinite = false;
            } else {
                // Infeasible — encode as empty interval.
                bound.ctLo = 1; bound.ctHi = 0;
                bound.ctLoFinite = bound.ctHiFinite = true;
            }
            return bound;
        }
        mpq_class threshold = -bound.residualConst / ctCoef;
        bool flip = ctCoef < 0;
        if (bound.residualRel == CtBound::Rel::Geq) {
            if (!flip) { bound.ctLo = threshold; bound.ctLoFinite = true; bound.ctHiFinite = false; }
            else       { bound.ctHi = threshold; bound.ctHiFinite = true; bound.ctLoFinite = false; }
        } else if (bound.residualRel == CtBound::Rel::Leq) {
            if (!flip) { bound.ctHi = threshold; bound.ctHiFinite = true; bound.ctLoFinite = false; }
            else       { bound.ctLo = threshold; bound.ctLoFinite = true; bound.ctHiFinite = false; }
        } else {  // Eq
            bound.ctLo = threshold; bound.ctHi = threshold;
            bound.ctLoFinite = bound.ctHiFinite = true;
        }
    }
    return bound;
}

// ---- Identify residual co-vars in a branch ----
namespace {
// Walk all atoms of a branch and collect Variable names that are NOT
// λ vars, NOT in B, and NOT in ctVars. These are the residual co-vars
// that we grid-enumerate in the top-level solveBranch.
std::unordered_set<std::string> collectResidualCoVars(
    const CoreIr& ir,
    const FarkasBranch& branch,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::vector<std::string>& ctVars)
{
    std::unordered_set<std::string> lambdaSet(branch.lambdas.begin(), branch.lambdas.end());
    std::unordered_set<std::string> ctSet(ctVars.begin(), ctVars.end());
    std::unordered_set<std::string> result;
    std::function<void(ExprId)> walk;
    walk = [&](ExprId id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto vn = varName(ir, id)) {
                if (lambdaSet.count(*vn)) return;
                if (B.count(*vn)) return;
                if (ctSet.count(*vn)) return;
                result.insert(*vn);
            }
            return;
        }
        for (ExprId c : e.children) walk(c);
    };
    for (ExprId atom : branch.equalities)   walk(atom);
    for (ExprId atom : branch.inequalities) walk(atom);
    return result;
}
} // namespace

std::vector<BranchCandidate> FarkasOrBranchSolver::solveBranch(
    const FarkasBranch& branch,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::vector<std::string>& ctVars) const
{
    auto residCoVars = collectResidualCoVars(ir_, branch, B, ctVars);
    if (residCoVars.empty()) {
        return solveBranchCore(branch, B, ctVars);
    }

    // Task #151: replace residual-grid enumeration with the augmented
    // Farkas solver. Build A_λ, A_r, c from equality rows, RREF with
    // residual pivots first, enumerate free λs in a bounded range.
    std::vector<std::string> residNames(residCoVars.begin(), residCoVars.end());
    std::sort(residNames.begin(), residNames.end());

    // Extract equality rows with residual coefficients populated.
    std::vector<EqRow> eqRows;
    eqRows.reserve(branch.equalities.size());
    for (ExprId atom : branch.equalities) {
        auto row = extractEqRow(atom, branch.lambdas, B, residCoVars);
        if (!row) return {};
        eqRows.push_back(std::move(*row));
    }
    if (eqRows.empty()) {
        return solveBranchCore(branch, B, ctVars);
    }

    const std::size_t L = branch.lambdas.size();
    const std::size_t R = residNames.size();
    const std::size_t m = eqRows.size();

    std::vector<std::vector<mpq_class>> A_lambda(m, std::vector<mpq_class>(L, mpq_class(0)));
    std::vector<std::vector<mpq_class>> A_resid(m,  std::vector<mpq_class>(R, mpq_class(0)));
    std::vector<mpq_class> cVec(m);
    for (std::size_t i = 0; i < m; ++i) {
        for (std::size_t j = 0; j < L; ++j) A_lambda[i][j] = eqRows[i].coeffs[j];
        for (std::size_t j = 0; j < R; ++j) {
            auto it = eqRows[i].residCoeffs.find(residNames[j]);
            A_resid[i][j] = (it != eqRows[i].residCoeffs.end()) ? it->second : mpq_class(0);
        }
        // eqRow: coeffs·λ + residCoeffs·r + constant = 0 → A·x = -constant.
        cVec[i] = -eqRows[i].constant;
    }

    auto sols = solveAugmentedFarkas(A_lambda, A_resid, cVec, residNames,
                                     /*maxFreeRange=*/30, /*maxSolutions=*/4);

    // Extract inequality rows once (residual-aware) for ctBound derivation.
    std::vector<IneqRow> ineqRowsTemplate;
    ineqRowsTemplate.reserve(branch.inequalities.size());
    bool ineqOk = true;
    for (ExprId atom : branch.inequalities) {
        auto row = extractIneqRow(atom, branch.lambdas, B, ctVars, residCoVars);
        if (!row) { ineqOk = false; break; }
        ineqRowsTemplate.push_back(std::move(*row));
    }
    if (!ineqOk) return {};

    std::vector<BranchCandidate> out;
    for (const auto& sol : sols) {
        // Build per-candidate ineqRows with residual values substituted
        // into the constant term.
        std::vector<IneqRow> ineqRows = ineqRowsTemplate;
        for (auto& row : ineqRows) {
            for (auto it = row.residCoeffs.begin(); it != row.residCoeffs.end(); ) {
                auto rv = sol.residValues.find(it->first);
                if (rv != sol.residValues.end()) {
                    row.constant += it->second * mpq_class(rv->second);
                    it = row.residCoeffs.erase(it);
                } else {
                    ++it;
                }
            }
        }
        BranchCandidate cand;
        cand.lambdaNames = branch.lambdas;
        cand.lambdaRay = sol.lambdaValues;
        cand.scaleT = 1;
        cand.residValues = sol.residValues;
        cand.ctBounds.reserve(ineqRows.size());
        for (const auto& row : ineqRows) {
            cand.ctBounds.push_back(deriveCtBound(row, sol.lambdaValues, branch.lambdas));
        }
        // Reject if any ctBound is infeasible at this λ ray.
        bool feasible = true;
        for (const auto& b : cand.ctBounds) {
            if (b.hasInterval && b.ctLoFinite && b.ctHiFinite
                && b.ctLo > b.ctHi) { feasible = false; break; }
            if (!b.hasInterval) {
                bool ctEmpty = b.residualCoefs.empty()
                    || std::all_of(b.residualCoefs.begin(), b.residualCoefs.end(),
                        [](const auto& p){ return p.second == 0; });
                if (ctEmpty) {
                    if (b.residualRel == CtBound::Rel::Geq && b.residualConst < 0) { feasible = false; break; }
                    if (b.residualRel == CtBound::Rel::Leq && b.residualConst > 0) { feasible = false; break; }
                    if (b.residualRel == CtBound::Rel::Eq  && b.residualConst != 0) { feasible = false; break; }
                }
            }
        }
        if (feasible) out.push_back(std::move(cand));
    }
    return out;
}

std::vector<BranchCandidate> FarkasOrBranchSolver::solveBranchCore(
    const FarkasBranch& branch,
    const std::unordered_map<std::string, mpz_class>& B,
    const std::vector<std::string>& ctVars) const
{
    std::vector<BranchCandidate> out;
    if (branch.lambdas.empty()) return out;

    // Step 1: extract all equality rows. P1 v2 accepts non-homogeneous
    // (constant ≠ 0) rows: A·λ + constant = 0, equivalently A·λ = -constant,
    // i.e. c[i] = -eqRows[i].constant for the augmented system.
    std::vector<EqRow> eqRows;
    eqRows.reserve(branch.equalities.size());
    for (ExprId atom : branch.equalities) {
        auto row = extractEqRow(atom, branch.lambdas, B);
        if (!row) return out;        // shape failure → infeasible
        eqRows.push_back(std::move(*row));
    }

    // Step 2: extract all inequality rows (needed for ctBound derivation).
    std::vector<IneqRow> ineqRows;
    ineqRows.reserve(branch.inequalities.size());
    for (ExprId atom : branch.inequalities) {
        auto row = extractIneqRow(atom, branch.lambdas, B, ctVars);
        if (!row) return out;
        ineqRows.push_back(std::move(*row));
    }

    // Step 3: support enumeration over λ subsets of size 1..Kmax.
    const std::size_t k = branch.lambdas.size();
    const std::size_t Kmax = std::min<std::size_t>(k, 4);
    for (std::size_t supSize = 1; supSize <= Kmax; ++supSize) {
        // Enumerate combinations of size supSize from {0..k-1}.
        std::vector<std::size_t> idx(supSize);
        std::iota(idx.begin(), idx.end(), 0);
        while (true) {
            // Build A_S: rows = eqRows.size(), cols = supSize, plus
            // c_S (RHS vector) for non-homogeneous handling.
            std::vector<std::vector<mpq_class>> A_S(
                eqRows.size(), std::vector<mpq_class>(supSize, mpq_class(0)));
            std::vector<mpq_class> c_S(eqRows.size(), mpq_class(0));
            for (std::size_t r = 0; r < eqRows.size(); ++r) {
                for (std::size_t c = 0; c < supSize; ++c) {
                    A_S[r][c] = eqRows[r].coeffs[idx[c]];
                }
                // Equality is `coeffs·λ + constant = 0` so A·λ = -constant.
                c_S[r] = -eqRows[r].constant;
            }
            // Check that out-of-support λ's are forced to 0 — i.e. the
            // unsupported columns of the FULL coefficient matrix must not
            // contribute to A_full · λ_full = -constant. Since λ_unsupp = 0,
            // those columns drop out automatically; no extra check needed.
            //
            // Find non-neg integer solution of A_S · λ_S = c_S.
            auto rayS = findNonNegIntegerSolution(A_S, c_S);
            if (!rayS.empty()) {
                // Build full-width ray: zero outside support.
                std::vector<mpz_class> ray(k, mpz_class(0));
                for (std::size_t c = 0; c < supSize; ++c) {
                    ray[idx[c]] = rayS[c];
                }
                // Derive CT bounds for each inequality.
                BranchCandidate cand;
                cand.lambdaNames = branch.lambdas;
                cand.lambdaRay = ray;
                cand.scaleT = 1;
                cand.ctBounds.reserve(ineqRows.size());
                for (const auto& row : ineqRows) {
                    cand.ctBounds.push_back(deriveCtBound(row, ray, branch.lambdas));
                }
                out.push_back(std::move(cand));
            }

            // Next combination.
            std::size_t pos = supSize;
            while (pos > 0) {
                --pos;
                if (idx[pos] < k - (supSize - pos)) {
                    ++idx[pos];
                    for (std::size_t q = pos + 1; q < supSize; ++q) idx[q] = idx[q - 1] + 1;
                    goto next_iter;
                }
            }
            break;
            next_iter: ;
        }
    }

    return out;
}

} // namespace xolver::farkas
