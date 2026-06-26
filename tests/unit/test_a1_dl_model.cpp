// Guards for IDL/RDL model read-off (getModel), recovering the
// strict-validation flips idl_009/011/012/015 and rdl_007/009/012: the solvers
// used to leave all difference-logic variables at the model builder's default
// (0), which breaks the constraints. getModel() now reads off the Bellman-Ford
// potentials (anchored at __ZERO__=0). These tests drive the solvers directly
// and check the produced model actually satisfies the asserted constraints —
// independent of the high-level strict-validation gate.

#include <doctest/doctest.h>
#include "theory/arith/logics/dl/IdlSolver.h"
#include "theory/arith/logics/dl/RdlSolver.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "expr/types.h"
#include <gmpxx.h>

using namespace xolver;

namespace {

TheoryAtomRecord mkDiffAtom(SatVar sv, TheoryId theory,
                            const std::string& plusVar, const std::string& minusVar,
                            Relation rel, const mpq_class& rhs) {
    LinearFormKey lhs;
    if (!plusVar.empty()) lhs.terms.push_back({plusVar, mpq_class(1)});
    if (!minusVar.empty()) lhs.terms.push_back({minusVar, mpq_class(-1)});
    return TheoryAtomRecord{sv, theory, false, NullExpr,
                            LinearAtomPayload{lhs, rel, RealValue::fromMpq(rhs)}};
}

} // namespace

TEST_CASE("IDL getModel: read-off satisfies difference + single-var constraints") {
    IdlSolver solver;
    solver.push();
    TheoryLemmaDatabase lemmaDb;

    SatVar sv = 1;
    auto assertC = [&](const std::string& p, const std::string& n, Relation rel, long rhs) {
        solver.assertLit(mkDiffAtom(sv, TheoryId::IDL, p, n, rel, mpq_class(rhs)),
                         true, 0, SatLit{sv, true});
        ++sv;
    };
    // 8-node-DAG-style schedule (mirrors idl_009).
    assertC("t2", "t1", Relation::Geq, 3);
    assertC("t3", "t1", Relation::Geq, 2);
    assertC("t4", "t2", Relation::Geq, 4);
    assertC("t4", "t3", Relation::Geq, 5);
    assertC("t1", "",  Relation::Geq, 0);   // t1 >= 0  (single-var -> __ZERO__)
    assertC("t4", "",  Relation::Leq, 50);  // t4 <= 50

    auto r = solver.check(lemmaDb);
    REQUIRE(r.kind == TheoryCheckResult::Kind::Consistent);

    auto m = solver.getModel();
    REQUIRE(m.has_value());
    auto v = [&](const std::string& nm) -> mpz_class {
        REQUIRE(m->assignments.count(nm) == 1);
        return mpz_class(m->assignments.at(nm));
    };
    CHECK(v("t2") - v("t1") >= 3);
    CHECK(v("t3") - v("t1") >= 2);
    CHECK(v("t4") - v("t2") >= 4);
    CHECK(v("t4") - v("t3") >= 5);
    CHECK(v("t1") >= 0);
    CHECK(v("t4") <= 50);
}

TEST_CASE("RDL getModel: read-off satisfies real difference constraints (strict)") {
    RdlSolver solver;
    solver.push();
    TheoryLemmaDatabase lemmaDb;

    SatVar sv = 1;
    auto assertC = [&](const std::string& p, const std::string& n, Relation rel, long rhs) {
        solver.assertLit(mkDiffAtom(sv, TheoryId::RDL, p, n, rel, mpq_class(rhs)),
                         true, 0, SatLit{sv, true});
        ++sv;
    };
    // a < b < c with a >= 0, c <= 10 (strict — exercises the delta instantiation).
    assertC("b", "a", Relation::Gt, 0);     // b - a > 0
    assertC("c", "b", Relation::Gt, 0);     // c - b > 0
    assertC("a", "",  Relation::Geq, 0);    // a >= 0
    assertC("c", "",  Relation::Leq, 10);   // c <= 10

    auto r = solver.check(lemmaDb);
    REQUIRE(r.kind == TheoryCheckResult::Kind::Consistent);

    auto m = solver.getModel();
    REQUIRE(m.has_value());
    auto v = [&](const std::string& nm) -> mpq_class {
        REQUIRE(m->assignments.count(nm) == 1);
        return mpq_class(m->assignments.at(nm));
    };
    CHECK(v("b") - v("a") > 0);
    CHECK(v("c") - v("b") > 0);
    CHECK(v("a") >= 0);
    CHECK(v("c") <= 10);
}
