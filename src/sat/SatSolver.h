#pragma once

#include "expr/types.h"
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace xolver {

/**
 * SAT literal: signed variable.
 * Positive = var true, Negative = var false.
 */
struct SatLit {
    SatVar var = 0;
    bool sign = true;

    SatLit() = default;
    SatLit(SatVar v, bool s) : var(v), sign(s) {}

    static SatLit positive(SatVar v) { return {v, true}; }
    static SatLit negative(SatVar v) { return {v, false}; }
    SatLit negated() const { return {var, !sign}; }

    bool operator==(const SatLit& other) const { return var == other.var && sign == other.sign; }
    bool operator!=(const SatLit& other) const { return !(*this == other); }
};

#ifdef XOLVER_ENABLE_PROOFS
/**
 * One captured clause of an LRAT refutation (Phase F1 in-memory capture).
 * Original input clauses have an empty `chain`; derived clauses carry their
 * antecedent clause-ids (the LRAT resolution hints). Literals are external
 * DIMACS ints (signed variable). Captured in CaDiCaL emission order; original
 * clauses keep their assigned ids (derived ids may interleave among them).
 */
struct LratClause {
    int64_t id = 0;
    std::vector<int> lits;
    std::vector<int64_t> chain;   // empty => original input clause
    bool original = false;
};
#endif

/**
 * Abstract SAT solver interface.
 *
 * CaDiCaL wrapper — the only supported SAT backend.
 */
class SatSolver {
public:
    virtual ~SatSolver() = default;

    virtual SatVar newVar() = 0;
    virtual void addClause(const std::vector<SatLit>& clause) = 0;

    enum class SolveResult { Sat, Unsat, Unknown };
    virtual SolveResult solve() = 0;
    virtual SolveResult solve(const std::vector<SatLit>& assumptions) = 0;

    virtual bool value(SatVar v) const = 0;
    virtual bool configure(const char* name, int64_t value) { (void)name; (void)value; return false; }

    // Per-solve resource limit (e.g. "conflicts", "decisions"). Bounds the NEXT
    // solve() so a single hard instance cannot consume an unbounded budget; a
    // solve that hits the limit returns Unknown. Default no-op (returns false).
    virtual bool limit(const char* name, int value) { (void)name; (void)value; return false; }

    // Assumption / unsat-core support
    virtual std::vector<SatLit> getFailedAssumptions() const { return {}; }

    // Observed variable support (for CaDiCaL ExternalPropagator)
    virtual void addObservedVar(SatVar /*v*/) {}

    // Force the DEFAULT decision phase of a variable (search heuristic only —
    // never changes satisfiability). Used by Nelson-Oppen combination to default
    // shared-equality atoms to FALSE (the "all-distinct" arrangement), so the SAT
    // core stops freely guessing interface equalities. Default no-op.
    virtual void setDefaultPhase(SatVar /*v*/, bool /*value*/) {}

    // --- UNSAT proof tracing (Phase B; backend gated by XOLVER_ENABLE_PROOFS) ---
    // Enable propositional-proof emission for this solve. `base` is a path stem:
    // the backend writes the DIMACS clause set it feeds the SAT engine to
    // `<base>.cnf` and the refutation proof to `<base>.drat` (or `.lrat`), so an
    // independent checker (drat-trim / lrat-check) can verify `<base>.cnf` ⊢ ⊥.
    // MUST be called before any addClause()/solve() (CaDiCaL CONFIGURING state).
    // Returns false if unsupported or not built with proof support — the caller
    // then runs in degraded "no-proof" mode (still emits unsat, no certificate).
    virtual bool enableProofTrace(const std::string& /*base*/, bool /*lrat*/) { return false; }

    // Finalize the proof of the just-decided UNSAT solve (CaDiCaL conclude()) and
    // flush both artifacts to disk so they are readable immediately. No-op unless
    // proof tracing was enabled and the last solve was UNSAT.
    virtual void finalizeProof() {}

#ifdef XOLVER_ENABLE_PROOFS
    // --- In-memory LRAT capture (Phase F1; backend gated by XOLVER_ENABLE_PROOFS).
    // Unlike enableProofTrace (which writes <base>.cnf/.drat), this captures the
    // resolution refutation WITH antecedent chains directly in memory, no files,
    // for the propositional Boolean-assembly proof. Used on a dedicated SAT solve
    // over a flat CNF. MUST be called before any addClause()/solve(). Returns
    // false if unsupported / not built with proof support.
    virtual bool enableLratCapture() { return false; }

    // After an UNSAT solve() with LRAT capture enabled, fill `out` with the
    // captured clauses (original input + derived, in emission order). Returns
    // false (and leaves `out` untouched) if nothing was captured.
    virtual bool getLratProof(std::vector<LratClause>& /*out*/) const { return false; }
#endif
};

/**
 * Factory: creates the best available SAT backend.
 */
std::unique_ptr<SatSolver> createSatSolver();

} // namespace xolver
