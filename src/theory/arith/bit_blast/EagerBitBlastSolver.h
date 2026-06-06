#pragma once

#include "expr/ir.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/PolynomialConverter.h"
#include <gmpxx.h>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace xolver::bitblast {

// Whole-formula eager bit-blaster (BLAN-style) as a SOUND PORTFOLIO ARM.
//
// Translates the ENTIRE (lowered) QF_NIA formula — boolean skeleton via Tseitin
// gates + each arithmetic atom reified via the ported bit-blaster (Int vars ->
// two's-complement bit-vectors) — into ONE SAT instance and solves it once.
//
// SOUNDNESS (invariants 1 + 7): this is a SAT-FINDER ONLY. A SAT model is a
// CANDIDATE; it is accepted only after EXACT integer re-evaluation of every
// assertion (kernel arithmetic + the boolean structure). It NEVER returns Unsat
// (a bit-blast UNSAT at a heuristic width proves nothing about the unbounded
// integer problem) and NEVER returns an unvalidated Sat. Any encoding mistake
// can therefore only downgrade a candidate to Unknown, never produce a wrong
// answer. Widths are escalated (cascade); overflow of the var budget bails the
// whole attempt to Unknown.
//
// Self-contained: owns its own PolynomialKernel + PolynomialConverter + a fresh
// SAT instance per width attempt. Does NOT touch the CDCL(T) main loop
// (invariant 5) — it is a parallel strategy, exactly what BLAN is.
class EagerBitBlastSolver {
public:
    enum class Status { Sat, Unknown };
    struct Result {
        // (boolModel) populated alongside model on Sat so callers (Solver::Impl)
        // can hand a complete typed channel to ModelConverter::reconstruct.
        // Without this, evalBool's missing-var default to false caused wrong
        // Ite-branch selection during reconstruction (test_model_consistency).
        Status status = Status::Unknown;
        std::unordered_map<std::string, mpz_class> model;     // validated int model
        std::unordered_map<std::string, bool> boolModel;      // Bool variables
    };

    EagerBitBlastSolver();

    // Attempt to find (and exactly validate) a model for `assertions` in `ir`.
    Result solve(const CoreIr& ir, const std::vector<ExprId>& assertions);

private:
    std::unique_ptr<PolynomialKernel> kernel_;
    std::unique_ptr<PolynomialConverter> converter_;

    // Per-atom converted constraints (each arith atom -> a list of (diff, rel)
    // combined by AND: a single relation for Lt/Leq/Gt/Geq, a chain for n-ary
    // Eq, all pairwise Neq for Distinct). Filled by collect(); reused in encode
    // and validate so both see identical polynomials.
    struct AtomCs { std::vector<std::pair<PolyId, Relation>> parts; };
    std::unordered_map<ExprId, AtomCs> atomCs_;
    std::vector<std::string> intVars_;

    // Per-variable bounds extracted from simple bound atoms (x rel const). A
    // both-sided-bounded var is encoded at its EXACT width (bitsToCover) instead
    // of the uniform cascade width — BLAN's collector discipline. Shrinks the
    // encoding massively on bound-heavy formulas (Farkas templates) and keeps
    // products narrow. Sound: the value provably lies in [lb,ub] (the bound atom
    // is still encoded), so the exact width always suffices.
    std::unordered_map<std::string, mpz_class> lb_, ub_;
    void tryExtractBound(PolyId diff, Relation rel);


    // Walk the DAG: reject unsupported constructs (UF/array/quantifier/real),
    // convert every arith atom, collect int vars. Returns false => bail Unknown.
    bool collect(const CoreIr& ir, const std::vector<ExprId>& assertions);

    bool isBoolTyped(ExprId eid, const CoreIr& ir) const;
    bool isArithAtom(ExprId eid, const CoreIr& ir) const;

    static Relation relOf(Kind k);
    static bool relationHolds(const mpz_class& v, Relation rel);
};

} // namespace xolver::bitblast
