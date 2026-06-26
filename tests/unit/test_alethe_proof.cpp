// White-box: the Alethe proof emitter (src/proof/AletheProof).
//
// These tests pin the exact serialized text. The strings below are not
// arbitrary — they are byte-for-byte the proofs the external checker Carcara
// accepts as `valid` (validated out-of-band against the original .smt2 problem;
// see docs/proof / tools/proof). If the serializer drifts, Carcara would reject
// the output, so these golden strings are the in-tree guard for that contract.

#include <doctest/doctest.h>
#include "proof/AletheProof.h"

using namespace xolver::proof;

TEST_CASE("AletheProof: empty proof serializes to nothing") {
    AletheProof p;
    CHECK(p.empty());
    CHECK(p.serialize().empty());
}

TEST_CASE("AletheProof: assume/step ids and serialization") {
    AletheProof p;
    CHECK(p.assume("(> x 0)") == "h1");
    CHECK(p.assume("(< x 0)") == "h2");
    CHECK(p.step({"(not (> x 0))", "(not (< x 0))"}, "la_generic", {}, {"1", "1"}) == "t1");
    CHECK(p.step({}, "resolution", {"t1", "h1", "h2"}) == "t2");
    CHECK(p.serialize() ==
          "(assume h1 (> x 0))\n"
          "(assume h2 (< x 0))\n"
          "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))\n"
          "(step t2 (cl) :rule resolution :premises (t1 h1 h2))\n");
}

TEST_CASE("AletheProof: buildConflictRefutation matches the Carcara-valid LRA Farkas proof") {
    // lra_003 (x>0 and x<0), both asserted positively, Farkas multipliers (1 1).
    // This exact text is checked `valid` by Carcara against
    // tests/regression/lra/lra_003_unsat_strict.smt2.
    AletheProof p = buildConflictRefutation(
        {{"(> x 0)", true}, {"(< x 0)", true}}, "la_generic", {"1", "1"});
    CHECK(p.serialize() ==
          "(assume h1 (> x 0))\n"
          "(assume h2 (< x 0))\n"
          "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))\n"
          "(step t2 (cl) :rule resolution :premises (t1 h1 h2))\n");
}

TEST_CASE("AletheProof: polarity is handled — EUF eq_transitive with a negative diseq literal") {
    // a=b, b=c asserted positively; a=c asserted NEGATIVELY (the disequality).
    // The clause negates each (double-neg simplified): (= a c), not (not (not ...)).
    // This is byte-for-byte the eq_transitive proof Carcara accepts.
    AletheProof p = buildConflictRefutation(
        {{"(= a b)", true}, {"(= b c)", true}, {"(= a c)", false}}, "eq_transitive", {});
    CHECK(p.serialize() ==
          "(assume h1 (= a b))\n"
          "(assume h2 (= b c))\n"
          "(assume h3 (not (= a c)))\n"
          "(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)\n"
          "(step t2 (cl) :rule resolution :premises (t1 h1 h2 h3))\n");
}
