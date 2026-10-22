// White-box: ProofManager (Stage J skeleton) and ModelValidator (Stage A).
//
// ProofManager — currently records but does not verify; we only check the
// API contract: lemmas can be recorded and exports return strings without
// crashing.
//
// ModelValidator — validates Bool-structure assignments. We test that
// and/or/not/ite/eq evaluation matches truth-table semantics.

#include <doctest/doctest.h>
#include "evidence/ProofManager.h"
#include "evidence/ModelValidator.h"
#include "ir/NativeTerms.h"
#include "ir/types.h"

using namespace xolver;

// -----------------------------------------------------------------------
// ProofManager
// -----------------------------------------------------------------------

TEST_CASE("Proof: empty manager exports without crashing") {
    ProofManager m;
    CHECK_NOTHROW(m.exportAlethe());
    CHECK_NOTHROW(m.exportLFSC());
}

TEST_CASE("Proof: recordTheoryLemma accepts empty clause") {
    ProofManager m;
    CHECK_NOTHROW(m.recordTheoryLemma({}, "empty"));
}

TEST_CASE("Proof: recordTheoryLemma stores multiple lemmas") {
    ProofManager m;
    std::vector<SatLit> c1 = {SatLit::positive(1), SatLit::negative(2)};
    std::vector<SatLit> c2 = {SatLit::positive(3)};
    CHECK_NOTHROW(m.recordTheoryLemma(c1, "LRA-conflict"));
    CHECK_NOTHROW(m.recordTheoryLemma(c2, "EUF-lemma"));
    auto alethe = m.exportAlethe();
    // Skeleton may return empty or placeholder; at minimum it should not crash.
    CHECK_NOTHROW((void)alethe.length());
}

TEST_CASE("Proof: setSatProofFile is settable to empty and non-empty path") {
    ProofManager m;
    CHECK_NOTHROW(m.setSatProofFile(""));
    CHECK_NOTHROW(m.setSatProofFile("/tmp/xolver_proof.drat"));
}

// -----------------------------------------------------------------------
// ModelValidator
// -----------------------------------------------------------------------

static ExprId mkBoolVar(NativeTerms& ir, const std::string& name) {
    ir.registerSort(0, SortKind::Bool);
    TermExpr e;
    e.kind = Kind::Variable;
    e.sort = 0;  // bool sort id
    e.payload = Payload(std::string(name));
    return ir.add(std::move(e));
}

static ExprId mkOp(NativeTerms& ir, Kind k, std::vector<ExprId> args) {
    TermExpr e;
    e.kind = k;
    e.sort = 0;
    for (auto a : args) e.children.push_back(a);
    return ir.add(std::move(e));
}

TEST_CASE("MV: AND truth table") {
    NativeTerms ir;
    ExprId p = mkBoolVar(ir, "p");
    ExprId q = mkBoolVar(ir, "q");
    ExprId pq = mkOp(ir, Kind::And, {p, q});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[p] = true; a[q] = true;  CHECK(mv.eval(pq, ir, a) == true);
    a[p] = true; a[q] = false; CHECK(mv.eval(pq, ir, a) == false);
    a[p] = false; a[q] = true; CHECK(mv.eval(pq, ir, a) == false);
    a[p] = false; a[q] = false; CHECK(mv.eval(pq, ir, a) == false);
}

TEST_CASE("MV: OR truth table") {
    NativeTerms ir;
    ExprId p = mkBoolVar(ir, "p");
    ExprId q = mkBoolVar(ir, "q");
    ExprId pq = mkOp(ir, Kind::Or, {p, q});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[p] = true;  a[q] = true;  CHECK(mv.eval(pq, ir, a) == true);
    a[p] = true;  a[q] = false; CHECK(mv.eval(pq, ir, a) == true);
    a[p] = false; a[q] = true;  CHECK(mv.eval(pq, ir, a) == true);
    a[p] = false; a[q] = false; CHECK(mv.eval(pq, ir, a) == false);
}

TEST_CASE("MV: NOT flips") {
    NativeTerms ir;
    ExprId p = mkBoolVar(ir, "p");
    ExprId notp = mkOp(ir, Kind::Not, {p});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[p] = true;  CHECK(mv.eval(notp, ir, a) == false);
    a[p] = false; CHECK(mv.eval(notp, ir, a) == true);
}

TEST_CASE("MV: ITE selects branch") {
    NativeTerms ir;
    ExprId c = mkBoolVar(ir, "c");
    ExprId t = mkBoolVar(ir, "t");
    ExprId e = mkBoolVar(ir, "e");
    ExprId ite = mkOp(ir, Kind::Ite, {c, t, e});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[c] = true;  a[t] = true;  a[e] = false; CHECK(mv.eval(ite, ir, a) == true);
    a[c] = false; a[t] = true;  a[e] = false; CHECK(mv.eval(ite, ir, a) == false);
    a[c] = true;  a[t] = false; a[e] = true;  CHECK(mv.eval(ite, ir, a) == false);
    a[c] = false; a[t] = false; a[e] = true;  CHECK(mv.eval(ite, ir, a) == true);
}

TEST_CASE("MV: Eq on Bool atoms — equivalence") {
    NativeTerms ir;
    ExprId p = mkBoolVar(ir, "p");
    ExprId q = mkBoolVar(ir, "q");
    ExprId eq = mkOp(ir, Kind::Eq, {p, q});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[p] = true;  a[q] = true;  CHECK(mv.eval(eq, ir, a) == true);
    a[p] = false; a[q] = false; CHECK(mv.eval(eq, ir, a) == true);
    a[p] = true;  a[q] = false; CHECK(mv.eval(eq, ir, a) == false);
}

TEST_CASE("MV: nested And of Or") {
    NativeTerms ir;
    ExprId p = mkBoolVar(ir, "p");
    ExprId q = mkBoolVar(ir, "q");
    ExprId r = mkBoolVar(ir, "r");
    ExprId pq = mkOp(ir, Kind::Or, {p, q});
    ExprId all = mkOp(ir, Kind::And, {pq, r});

    ModelValidator mv;
    ModelValidator::BoolAssignment a;
    a[p] = true;  a[q] = false; a[r] = true;  CHECK(mv.eval(all, ir, a) == true);
    a[p] = false; a[q] = false; a[r] = true;  CHECK(mv.eval(all, ir, a) == false);
    a[p] = true;  a[q] = true;  a[r] = false; CHECK(mv.eval(all, ir, a) == false);
}
