#pragma once

#include <string>
#include <vector>

namespace xolver {
namespace proof {

// Minimal builder for Alethe proofs (the format checked by Carcara). Pure text /
// no solver dependency, so it compiles in every build and is exercised only on
// the proof path. Terms are passed as already-printed SMT-LIB strings (the theory
// solvers know how to render their own atoms); this type owns only the proof
// *structure* (assume/step commands, clauses, ids) and its serialization.
//
// An Alethe proof is a list of commands:
//   (assume h1 <formula>)
//   (step  t1 (cl <lits>) :rule <r> :premises (..) :args (..))
//   ...
//   (step  tN (cl)        :rule resolution :premises (..))   ; the empty clause
// A `(cl)` with no literals is the empty clause — the refutation's conclusion.
class AletheProof {
public:
    // Add `(assume <id> <term>)`; returns the fresh id (h1, h2, ...).
    std::string assume(const std::string& term);

    // Add `(step <id> (cl <clause...>) :rule <rule> [:premises (...)] [:args (...)])`.
    // `clause` literals and `args` are SMT-LIB strings; `premises` are step ids.
    // Returns the fresh id (t1, t2, ...).
    std::string step(const std::vector<std::string>& clause,
                     const std::string& rule,
                     const std::vector<std::string>& premises = {},
                     const std::vector<std::string>& args = {});

    // Full Alethe proof text (one command per line, trailing newline).
    std::string serialize() const;

    bool empty() const { return commands_.empty(); }

private:
    struct Command {
        std::string id;
        bool isAssume = false;
        std::string assumeTerm;
        std::vector<std::string> clause;
        std::string rule;
        std::vector<std::string> premises;
        std::vector<std::string> args;
    };
    std::vector<Command> commands_;
    int assumeCount_ = 0;
    int stepCount_ = 0;
};

// One asserted literal of a theory conflict: the atom (SMT-LIB) and whether it
// was asserted positively (the fact `atom`) or negatively (the fact `(not atom)`,
// e.g. an EUF disequality). The tautology clause negates each — with double
// negation simplified — so a positive literal contributes `(not atom)` and a
// negative literal contributes `atom`.
struct AssertedLit {
    std::string atom;
    bool positive = true;
};

// Build a complete refutation of a jointly-inconsistent conflict L1..Ln:
//   assume each Li (in its asserted polarity), derive the tautology
//   (cl ¬L1 ... ¬Ln) by `rule` (with `args`), then resolve with the assumes to
//   the empty clause. This is the shape of a single-conflict theory refutation
//   (LRA la_generic with Farkas coefficients, EUF eq_transitive, DL la_generic
//   over a negative cycle, …).
AletheProof buildConflictRefutation(const std::vector<AssertedLit>& lits,
                                    const std::string& rule,
                                    const std::vector<std::string>& args);

} // namespace proof
} // namespace xolver
