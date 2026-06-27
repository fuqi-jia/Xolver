#pragma once

#include "sat/SatSolver.h"
#include <cadical.hpp>
#include <memory>

namespace xolver {

class CadicalTheoryPropagator;
// Custom CaDiCaL proof tracer that captures the COMPLETE input clause set
// (original CNF + every external-propagator clause CaDiCaL records as original:
// lemmas, conflicts, reason clauses) via add_original_clause. Defined in the .cpp
// (it needs CaDiCaL's internal tracer.hpp). This is the single source of truth
// for the DIMACS the external checker needs — it cannot miss a clause path the
// way per-callback hooks could. Only used under XOLVER_ENABLE_PROOFS.
class ProofCnfCapture;
// LratCapture (Phase F1): a CaDiCaL::Tracer connected WITH antecedents, recording
// the full resolution refutation (original input clauses + derived clauses with
// their LRAT antecedent chains) in memory. Defined in the .cpp. No file output.
class LratCapture;

class CadicalBackend : public SatSolver {
public:
    CadicalBackend();
    ~CadicalBackend() override;

    SatVar newVar() override;
    void addClause(const std::vector<SatLit>& clause) override;
    SolveResult solve() override;
    SolveResult solve(const std::vector<SatLit>& assumptions) override;
    bool value(SatVar v) const override;
    bool configure(const char* name, int64_t value) override;
    bool limit(const char* name, int value) override;
    std::vector<SatLit> getFailedAssumptions() const override;
    void addObservedVar(SatVar v) override;
    void setDefaultPhase(SatVar v, bool value) override;

    void connectPropagator(CadicalTheoryPropagator* propagator);
    void disconnectPropagator();
    void requestTerminate();

    bool enableProofTrace(const std::string& base, bool lrat) override;
    void finalizeProof() override;
#ifdef XOLVER_ENABLE_PROOFS
    bool enableLratCapture() override;
    bool getLratProof(std::vector<LratClause>& out) const override;
#endif

    // Statistics (available only when compiled with CaDiCaL)
    struct Stats {
        int64_t vars = 0;
        int64_t clauses = 0;
        int64_t conflicts = 0;
        int64_t decisions = 0;
        int64_t propagations = 0;
    };
    Stats getStats() const;

private:
    // Wall-clock terminator: CaDiCaL polls terminate() DURING solve(), so even a
    // single long internal SAT solve (e.g. the bit-blast's dedicated solver, whose
    // conflict limit is unbounded by default) aborts when the solve deadline
    // passes. Default-INERT: terminate() is false unless XOLVER_WALLCLOCK_MS set a
    // deadline that has now passed (wall::remainingMs()). Sound: an aborted solve
    // returns Unknown.
    struct WallClockTerminator : public CaDiCaL::Terminator {
        bool terminate() override;
    };
    WallClockTerminator wallTerm_;

    std::unique_ptr<CaDiCaL::Solver> solver_;
    SatVar maxVar_ = 0;
    SatVar declaredVars_ = 0;
    bool terminateRequested_ = false;
    bool propagatorConnected_ = false;
    bool inSolving_ = false;
    std::vector<SatLit> lastAssumptions_;
    std::vector<bool> observedVars_;

    // --- UNSAT proof tracing state (active only when enableProofTrace succeeded;
    // compiled only under XOLVER_ENABLE_PROOFS — see CadicalBackend.cpp). ---
    bool proofTracing_ = false;     // proof emission enabled for this solve
    bool proofConcluded_ = false;   // finalizeProof already ran (idempotent guard)
    std::string proofBase_;         // path stem: <base>.cnf + <base>.drat/.lrat
    // How many clauses we fed via addClause() (= the original CNF size). The
    // capture tracer records original CNF + external theory clauses together, so
    // (captured total - this) = the count of theory lemmas ASSUMED as axioms — a
    // theory instance's proof certifies the Boolean skeleton only; the lemmas are
    // justified in Phase C. Recorded as a comment in <base>.cnf for honesty.
    std::size_t proofOrigClauseCount_ = 0;
#ifdef XOLVER_ENABLE_PROOFS
    // Gated out in the default (no-proof) build: a unique_ptr to the incomplete
    // ProofCnfCapture would need the full type at the (.cpp) destructor, which is
    // only defined under this macro.
    std::unique_ptr<ProofCnfCapture> proofCapture_; // the add_original_clause sink
    // Phase F1 in-memory LRAT capture (no files). Active only when
    // enableLratCapture() succeeded, on a dedicated flat-CNF solve.
    bool lratCapturing_ = false;
    bool lratConcluded_ = false;
    std::unique_ptr<LratCapture> lratCapture_;
#endif
    void writeProofCnf() const;     // dump <base>.cnf from the capture tracer
};

} // namespace xolver
