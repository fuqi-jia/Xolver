#pragma once

#include "proof/AletheProof.h"
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace xolver {
namespace proof {

// --- Increment F1: pure-propositional (flat-clausal) Boolean-assembly proofs ---
//
// Translate a SAT-engine LRAT refutation of a FLAT-CLAUSAL propositional problem
// into a single Alethe proof. "Flat-clausal" means every asserted formula is a
// Boolean literal (a Bool variable or its negation) or a disjunction of such
// literals — so clausification is exactly the Alethe `or` rule plus units, with
// NO Tseitin proxy variables to define (deferred to a later increment). The
// resolution refutation is replayed step-for-step from the LRAT antecedent chains
// (CaDiCaL's RUP hints), each becoming an Alethe `resolution` step.
//
// This module is pure text/structure: it has no SAT or solver dependency. The
// caller (Solver) detects the flat-clausal shape, builds the flat CNF, runs the
// SAT engine with LRAT capture, and renders the IR atoms to SMT-LIB strings.

// One flat-clausal asserted formula, prepared for assembly.
struct ClausalAssertion {
    // The whole assertion rendered as SMT-LIB — the `assume` term. Must be
    // textually identical to the matching `(assert ...)` in the emitted problem.
    std::string smtText;
    // The disjunct literals in IR-child order, each rendered as SMT-LIB (e.g.
    // "x1" or "(not x3)"). For a unit assertion this is the single literal. The
    // Alethe `or` rule requires the clause to list disjuncts in term order, so
    // these come from the IR `(or ...)` children, NOT from the SAT clause.
    std::vector<std::string> clauseTerms;
    // True when the assertion is a single literal: the `assume` already IS the
    // unit clause, so no `or` clausification step is emitted.
    bool isUnit = false;
};

// One captured LRAT clause (mirror of the SAT backend's record, kept dependency-
// free here). Original input clauses have an empty chain; derived clauses carry
// their antecedent clause-ids. Literals are signed SAT-variable ints.
struct LratStep {
    bool original = false;
    int64_t id = 0;
    std::vector<int> lits;
    std::vector<int64_t> chain;  // antecedent ids (derived clauses only)
};

// Build a complete Alethe refutation, or std::nullopt if anything fails to
// translate (the caller then degrades to the DRAT path — never a wrong proof).
//
//  - assertions : the flat-clausal assertions, in the order their clauses were
//                 fed to the SAT engine (one clause per assertion).
//  - lrat       : the captured LRAT, in emission order. The k-th `original`
//                 entry corresponds to assertions[k].
//  - varTerm    : varTerm[v] is the SMT-LIB atom for SAT variable v (1-based;
//                 index 0 unused). A negative literal renders as "(not <atom>)".
std::optional<AletheProof> buildClausalRefutation(
    const std::vector<ClausalAssertion>& assertions,
    const std::vector<LratStep>& lrat,
    const std::vector<std::string>& varTerm);

} // namespace proof
} // namespace xolver
