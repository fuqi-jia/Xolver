#pragma once

// Presolve.h — the theory-check presolve fixpoint shared by NIA / NIRA / NRA.
//
// The engine receives the active arithmetic atoms (each as `poly rel 0`) and
// runs the reusable capabilities (Caps. 1–7, 11) to a fixed point, recording
// every consequence in a DerivationLedger.  It NEVER returns SAT directly
// (soundness invariant).  Possible terminal outcomes:
//   - Conflict : an exact contradiction was derived (UNSAT direction).
//   - Lemma    : a finite case-split lemma (Cap. 6) for the SAT solver.
//   - Progress : derived substitutions / fixed values / bounds for the
//                downstream complete engines (e.g. BoundedNiaSolver) and Cap. 9.
//   - NoProgress.

#include "expr/types.h"
#include "sat/SatSolver.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/core/DerivedFact.h"

#include <chrono>
#include <map>
#include <memory>
#include <vector>

namespace xolver {

// One working atom: poly rel 0, with its reason DAG node.
struct PresolveAtom {
    RationalPolynomial poly;
    Relation rel;
    ReasonNode reasons;
    bool live = true;
};

struct FixedVal { mpq_class value; ReasonNode reasons; };
struct BoundVal { IntervalSet set; ReasonNode reasons; };

// Mutable working state shared by all capabilities during a fixpoint sweep.
struct PresolveState {
    PolynomialKernel* kernel = nullptr;
    bool integerDomain = false;   // true => all vars Int (NIA); false => Real (NRA)

    std::vector<PresolveAtom> atoms;

    // Solved-form substitution map: eliminated var -> (value, fact index).
    // iter-74: cache `value.variables()` per entry to make the backward-composition
    // loop in registerSubstitution use O(log V) per-entry lookup instead of
    // O(terms × vars-per-term). Maintained at every entry write/rewrite site.
    struct SubstEntry {
        RationalPolynomial value;
        size_t factIndex;
        std::set<VarId> vars;
    };
    std::map<VarId, SubstEntry> substMap;

    std::map<VarId, FixedVal> fixedValues;
    std::map<VarId, BoundVal> bounds;

    // var ≡ residue (mod modulus), from Cap. 5 (SNF lattice) or Cap. 6.
    struct CongruenceVal { mpz_class modulus; mpz_class residue; ReasonNode reasons; };
    std::map<VarId, CongruenceVal> congruences;

    DerivationLedger ledger;

    // Terminal outputs.
    bool hasConflict = false;
    TheoryConflict conflict;
    bool hasLemma = false;
    TheoryLemma lemma;
};

// A capability operates on the shared state.  Returns true iff it derived at
// least one new fact this call (drives the fixpoint).  It may set
// state.hasConflict / state.hasLemma to request termination.
class PresolveCapability {
public:
    virtual ~PresolveCapability() = default;
    virtual const char* name() const = 0;
    virtual bool run(PresolveState& st) = 0;
};

// ---------------------------------------------------------------------------
// Shared helpers (PresolveSupport.cpp)
// ---------------------------------------------------------------------------

// Substitute variable v by the polynomial `value` throughout p (exact).
RationalPolynomial substituteVar(const RationalPolynomial& p, VarId v,
                                 const RationalPolynomial& value);

// Eliminate variable v by substituting `value` (which must not contain v) into
// every live atom, recording the derivation in the ledger.  Records a
// DerivedFixedValue when `value` is constant, else a DerivedSubst, and updates
// st.substMap / st.fixedValues.  Sets st.hasConflict when a collapsed-constant
// atom violates its relation.  Returns true (progress).  The caller must ensure
// v is not already in st.substMap.  Shared by Cap. 1 and Cap. 5.
bool registerSubstitution(PresolveState& st, VarId v, RationalPolynomial value,
                          const ReasonNode& reasons);

// Intersect a derived interval into st.bounds[v], merging reasons.  Sets
// st.hasConflict when the intersection becomes empty (Real) or admits no
// integer (Int).  Returns true iff the stored bound changed (progress).
bool addBound(PresolveState& st, VarId v, const IntervalSet& incoming,
              const ReasonNode& reasons);

// Maximum total degree of any monomial (constant => 0; zero poly => 0).
int totalDegree(const RationalPolynomial& p);

// Evaluate `c rel 0` for a constant c.
bool relationHoldsForConstant(const mpq_class& c, Relation rel);

// ---------------------------------------------------------------------------
// PresolveResult / PresolveEngine
// ---------------------------------------------------------------------------
struct PresolveResult {
    enum class Kind { Conflict, Lemma, Progress, NoProgress } kind = Kind::NoProgress;
    TheoryConflict conflict;
    TheoryLemma lemma;
};

class PresolveEngine {
public:
    PresolveEngine(PolynomialKernel* kernel, bool integerDomain);

    // Add an active atom (poly rel 0) with its base SAT literal.
    void addAtom(const RationalPolynomial& poly, Relation rel, SatLit reason);

    // Run the fixpoint. Optional `deadline`: if reached during the inner loop
    // (checked after every capability call), the fixpoint aborts early and
    // returns Progress / NoProgress based on whether any derivation fired.
    // SOUND: every derivation already recorded in st_.ledger is semantically
    // valid; aborting just means downstream stages see a SUBSET of the facts
    // an unbudgeted run would derive — never an incorrect derivation.
    // Conflict / Lemma terminations always return immediately regardless of
    // the deadline.
    // Default `time_point::max()` is "no deadline", matching the pre-iter#21
    // unbudgeted behavior for callers that don't pass one.
    PresolveResult run(std::chrono::steady_clock::time_point deadline =
                           std::chrono::steady_clock::time_point::max());

    // Read-only access to derived facts for the integration layer
    // (inject bounds into DomainStore, reconstruct models, run Cap. 9).
    const PresolveState& state() const { return st_; }

    static constexpr int kMaxFactsPerSweep = 64;

private:
    PresolveState st_;
    std::vector<std::unique_ptr<PresolveCapability>> caps_;
};

} // namespace xolver
