// Farkas-Or Model Constructor — data types (Phase 0: detector).
//
// User-provided diagnosis (2026-06-02): VeryMax/Stroeder QF_NIA SAT cases are
// disjunctive Farkas-certificate-synthesis problems, not general NIA. The Or
// blocks have the shape
//   (or (and (>= λ_i 0)...  (= Σ c_j(B)·λ_j 0)... (rel Σ c_j(B,C)·λ_j + k 0)) ...)
// where λ_i are Farkas multipliers, B are small-domain bounded global vars,
// C are unbounded CT-like cost vars. SAT models pick one branch per Or block
// and share a common (B, C) assignment.
//
// This header defines the *result* of the detector. Phase 0 only populates
// these structures and dumps them; phases 1-4 add solving / model construction.
//
// Soundness: this lane returns SAT only (validated against the original
// CoreIr formula by ArithModelValidator). It NEVER claims UNSAT.

#pragma once

#include "expr/types.h"
#include <gmpxx.h>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace xolver::farkas {

// A single branch inside a Farkas-Or block. Records the atoms that classify
// as λ-non-negativity, λ-linear equalities, and λ-linear inequalities. Phase
// 1 will use these to build the A(B) matrix; Phase 0 just records shape.
struct FarkasBranch {
    ExprId originalAnd = NullExpr;          // the `And` ExprId that became this branch

    // λ-like vars: each came from an atom of form `(>= v 0)` (or, equivalently,
    // `(<= v 0)` after negation in CDCL(T) — but in the original assertion we
    // expect Geq).
    std::vector<std::string> lambdas;

    // Atoms classified as λ-linear equalities `Σ c_j(B)·λ_j = 0`.
    std::vector<ExprId> equalities;

    // Atoms classified as λ-linear inequalities (with possibly small constant)
    // `Σ c_j(B,C)·λ_j + k rel 0`.
    std::vector<ExprId> inequalities;

    // Atoms we couldn't classify (didn't fit a Farkas template). When > 0
    // the branch is "almost" Farkas but a structural check rejected something.
    std::vector<ExprId> unclassified;

    bool farkasShape() const {
        return !lambdas.empty() && (!equalities.empty() || !inequalities.empty())
            && unclassified.empty();
    }
};

// A top-level `Or` whose every child looks like a Farkas branch.
struct FarkasOrBlock {
    ExprId originalOr = NullExpr;
    std::vector<FarkasBranch> branches;

    bool allBranchesFarkas() const {
        if (branches.empty()) return false;
        for (const auto& b : branches) {
            if (!b.farkasShape()) return false;
        }
        return true;
    }
};

// Top-level profile of a CoreIr assertion list.
struct FarkasProfile {
    // Or blocks classified as Farkas-shaped (every branch is FarkasBranch::farkasShape()).
    std::vector<FarkasOrBlock> blocks;

    // Bounded global vars discovered from outer And constraints of form
    // `(and (<= L v) (<= v U))` or `(and (>= v L) (<= v U))`.
    // name → (lo, hi) inclusive integer bounds.
    std::unordered_map<std::string, std::pair<mpz_class, mpz_class>> boundedGlobals;

    // Vars that appear in λ·v bilinear monomials inside Farkas branches AND
    // have no detected bounded domain. These are the "CT-like" cost vars
    // (e.g. Nl2CT1, RFN1_CT in Stroeder).
    std::unordered_set<std::string> unboundedCT;

    // Vars used purely in outer linear constraints (not as Farkas multipliers
    // and not as λ-coefficients). e.g. main_x, main_y, undef3, undef4 — they
    // typically appear in the residual LIA solver, not in branch solving.
    std::unordered_set<std::string> residualVars;

    // Top-level assertions that were NOT classified as Farkas-Or blocks.
    // These remain plain assertions that the residual LIA solver must satisfy.
    std::vector<ExprId> outerAssertions;

    bool good() const { return !blocks.empty(); }
    std::size_t branchTotal() const {
        std::size_t n = 0;
        for (const auto& b : blocks) n += b.branches.size();
        return n;
    }
};

} // namespace xolver::farkas
