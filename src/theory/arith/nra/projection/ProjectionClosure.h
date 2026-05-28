#pragma once

#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/projection/SubresultantChain.h"
#include "expr/types.h"
#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver {

class PolynomialKernel;

// ---------------------------------------------------------------------------
// ProjectionClosure — the unconditionally-sound (Collins) projection of a
// constraint set, computed ONCE per solve (projection is sample-independent).
//
// For variable order x_0 < ... < x_{n-1} (x_0 assigned first by CDCAC), it
// composes the single-elimination Collins operator from the top variable down,
// producing for each level k the set of polynomials (in x_0..x_k) whose real
// roots delineate x_k's axis. Every produced polynomial carries provenance
// (ProjectionSource) so a debug validator can replay it.
//
// Operator per elimination of v over a poly set E:
//   * per f in E: all coefficients of f in v (the reducta leading coeffs),
//     and the principal-subresultant-coefficient chain of (f, f');
//   * per pair (f,g) in E: the PSC chain of (f, g).
// This is the Collins set — it includes the full PSC chain that the legacy
// McCallum-style LocalProjectionEngine omitted. It is unconditionally sound
// (no well-orientedness precondition).
//
// SOUNDNESS CONTRACT: if build() does not return None, the closure is
// INCOMPLETE and no UNSAT may rest on it (caller => Unknown). An oversized
// Sylvester submatrix => BudgetExceeded. A zero resultant (common factor) or
// identically-zero discriminant is SKIPPED, not bailed: the shared/repeated
// factor's roots are roots of the source polynomials themselves, already in
// the closure and delineated during lifting (soundness cross-checked by the
// benchmark invariant false-UNSAT = 0).
// ---------------------------------------------------------------------------

enum class ProjectionOpKind : uint8_t {
    Input,                              // an original constraint polynomial
    Coefficient,                        // coefficient of parent1 in eliminatedVar
    PrincipalSubresultantCoefficient,   // psc_{pscIndex} of (parent1, parent2)
};

struct ProjectionSource {
    ProjectionOpKind op = ProjectionOpKind::Input;
    int parent1 = -1;                   // index into ProjectionClosure entries
    int parent2 = -1;                   // -1 for a unary op
    VarId eliminatedVar = NullVar;
    int pscIndex = -1;                  // which psc_j (PSC op only)
    int coeffIndex = -1;                // which coefficient (Coefficient op only)
};

enum class ProjectionIncompleteReason : uint8_t {
    None,                   // complete — UNSAT may rest on this closure
    CommonFactorDegeneracy, // reserved (currently skipped, not bailed)
    BudgetExceeded,         // Sylvester submatrix or registry size over budget
    KernelFailure,
};

class ProjectionClosure {
public:
    struct Entry {
        RationalPolynomial poly;
        int mainVarLevel = -1;          // index in varOrder; -1 if constant
        ProjectionSource source;
    };

    struct Config {
        int maxMatrixDim = 9;           // Sylvester submatrix dimension cap
        size_t maxPolys = 8000;         // registry size cap
        Config() = default;
    };

    // Build the closure. constraints must be non-constant in varOrder (caller
    // resolves constant-zero atoms by relation BEFORE this). Returns the
    // incompleteness reason (None == complete).
    //
    // `kernel` is OPTIONAL and only consulted on the PSC path: when non-null
    // AND the env flag XOLVER_NRA_LIBPOLY_PSC is ON, the per-level PSC chains
    // route through libpoly instead of the determinant. Null kernel or flag
    // OFF => the determinant path, byte-identical to historical behaviour.
    ProjectionIncompleteReason build(
        const std::vector<RationalPolynomial>& constraints,
        const std::vector<VarId>& varOrder,
        const Config& cfg,
        PolynomialKernel* kernel = nullptr);
    ProjectionIncompleteReason build(
        const std::vector<RationalPolynomial>& constraints,
        const std::vector<VarId>& varOrder) {
        return build(constraints, varOrder, Config(), nullptr);
    }

    bool complete() const { return reason_ == ProjectionIncompleteReason::None; }
    ProjectionIncompleteReason reason() const { return reason_; }

    const std::vector<Entry>& entries() const { return entries_; }
    // Entry ids whose main variable is varOrder[k] (non-constant boundary polys).
    const std::vector<int>& levelPolys(int k) const;

private:
    std::vector<Entry> entries_;
    std::vector<std::vector<int>> levelPolys_;
    std::vector<VarId> varOrder_;
    Config cfg_;
    PolynomialKernel* kernel_ = nullptr;   // optional; PSC libpoly-path handle
    ProjectionIncompleteReason reason_ = ProjectionIncompleteReason::None;
    std::unordered_map<std::string, int> dedup_;
    std::vector<int> emptyLevel_;

    int mainVarLevelOf(const RationalPolynomial& p) const;
    int intern(const RationalPolynomial& p, const ProjectionSource& src);
    void projectLevel(const std::vector<int>& inputIds, VarId elimVar, int elimLevel);
};

} // namespace xolver
