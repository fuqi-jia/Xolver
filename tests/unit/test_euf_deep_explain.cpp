// Stack-overflow regression for the EUF proof-forest explanation path.
//
// IncrementalEGraph::ensureTermRegistered (arg registration) and the
// explainEquality<->explainEdge mutual recursion both recursed to a depth equal
// to the UF-nesting depth, so a deeply-nested UF congruence chain blew the call
// stack (the scrambler in competition can produce exactly this shape). Both were
// converted to explicit work-stacks; this test builds a depth-60000 unary-UF
// chain f^N(a) / f^N(b), propagates a=b up the chain by congruence, and explains
// f^N(a)=f^N(b) — the former recursion SIGSEGV'd the runner, the iterative
// version completes. The existing deep tests cover arith+bool walkers only, not
// the EUF explanation path.
//
// It runs on the default doctest thread (~8MB), NOT under the CLI's 512MB
// worker-stack wrapper (tools/cli/main.cpp), so the recursion is actually
// exposed. Built at the egraph level to bypass the recursive-descent parser
// (which would overflow first on deep S-expressions, masking this path).
#include <doctest/doctest.h>
#include "expr/ir.h"
#include "theory/euf/EufTermManager.h"
#include "theory/euf/IncrementalEGraph.h"
#include "sat/SatSolver.h"
#include <deque>

using namespace zolver;

TEST_CASE("EUF: deeply-nested UF congruence explanation does not overflow") {
    constexpr int kDeep = 60000;

    CoreIr ir;
    SortId u = ir.allocateSortId();
    ir.registerSort(u, SortKind::Other);  // uninterpreted sort U

    ExprId a = ir.add(CoreExpr{Kind::Variable, u, {}, Payload(std::string("a"))});
    ExprId b = ir.add(CoreExpr{Kind::Variable, u, {}, Payload(std::string("b"))});
    ExprId fa = a, fb = b;
    for (int i = 0; i < kDeep; ++i) {
        fa = ir.add(CoreExpr{Kind::UFApply, u, {fa}, Payload(std::string("f"))});
        fb = ir.add(CoreExpr{Kind::UFApply, u, {fb}, Payload(std::string("f"))});
    }

    EufTermManager tm;
    EufTermId ta = tm.intern(a, ir);
    EufTermId tb = tm.intern(b, ir);
    EufTermId tfa = tm.intern(fa, ir);   // intern is already iterative
    EufTermId tfb = tm.intern(fb, ir);
    REQUIRE(ta != NullEufTerm);
    REQUIRE(tb != NullEufTerm);
    REQUIRE(tfa != NullEufTerm);
    REQUIRE(tfb != NullEufTerm);

    IncrementalEGraph eg(tm);
    std::deque<PendingMerge> q;
    auto drain = [&]() {
        while (!q.empty()) {
            PendingMerge m = q.front();
            q.pop_front();
            eg.merge(m.a, m.b, m.reason, q);
        }
    };

    // Register the two deep chains (was recursive on args -> overflow at this depth).
    eg.ensureTermRegistered(tfa, q);
    eg.ensureTermRegistered(tfb, q);
    drain();

    // Assert a = b with a SAT-literal reason; congruence propagates f^k(a)=f^k(b)
    // up the whole chain.
    SatLit abLit(1, true);
    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.lit = abLit;
    eg.merge(ta, tb, mr, q);
    drain();

    REQUIRE(eg.same(tfa, tfb));   // congruence reached the full depth

    // The explanation walk recurses to depth kDeep in the old code -> SIGSEGV.
    ExplainResult r = eg.explainEquality(tfa, tfb);
    REQUIRE(r.ok);
    // Behavior-identity: the unique asserted reason along the chain is a = b.
    REQUIRE(r.reasons.size() == 1);
    CHECK(r.reasons[0].var == abLit.var);
    CHECK(r.reasons[0].sign == abLit.sign);
}

// Same recursion, exercised through ARRAY (store) congruence — the shape this
// lane actually produces (read2-style store towers). store terms are ordinary
// app nodes on the shared egraph, so a depth-N store chain explains via the same
// explainEquality<->explainEdge path; the array arg is the deep recursion.
TEST_CASE("EUF: deeply-nested store-tower congruence explanation does not overflow") {
    constexpr int kDeep = 60000;

    CoreIr ir;
    SortId idxSort = ir.allocateSortId();
    ir.registerSort(idxSort, SortKind::Other);
    SortId elemSort = ir.allocateSortId();
    ir.registerSort(elemSort, SortKind::Other);
    SortId arrSort = ir.allocateSortId();
    ir.registerSort(arrSort, SortKind::Array);

    ExprId A = ir.add(CoreExpr{Kind::Variable, arrSort, {}, Payload(std::string("A"))});
    ExprId B = ir.add(CoreExpr{Kind::Variable, arrSort, {}, Payload(std::string("B"))});
    ExprId i = ir.add(CoreExpr{Kind::Variable, idxSort, {}, Payload(std::string("i"))});
    ExprId v = ir.add(CoreExpr{Kind::Variable, elemSort, {}, Payload(std::string("v"))});

    // store_k = store(store_{k-1}, i, v); the same i/v at every level, so the
    // only varying argument is the (deep) array, and A=B propagates by congruence.
    ExprId sA = A, sB = B;
    for (int k = 0; k < kDeep; ++k) {
        sA = ir.add(CoreExpr{Kind::Store, arrSort, {sA, i, v}, {}});
        sB = ir.add(CoreExpr{Kind::Store, arrSort, {sB, i, v}, {}});
    }

    EufTermManager tm;
    EufTermId tA = tm.intern(A, ir);
    EufTermId tB = tm.intern(B, ir);
    EufTermId tsA = tm.intern(sA, ir);
    EufTermId tsB = tm.intern(sB, ir);
    REQUIRE(tA != NullEufTerm);
    REQUIRE(tsA != NullEufTerm);
    REQUIRE(tsB != NullEufTerm);

    IncrementalEGraph eg(tm);
    std::deque<PendingMerge> q;
    auto drain = [&]() {
        while (!q.empty()) {
            PendingMerge m = q.front();
            q.pop_front();
            eg.merge(m.a, m.b, m.reason, q);
        }
    };
    eg.ensureTermRegistered(tsA, q);
    eg.ensureTermRegistered(tsB, q);
    drain();

    SatLit abLit(7, true);
    MergeReason mr;
    mr.kind = MergeReasonKind::AssertedEquality;
    mr.lit = abLit;
    eg.merge(tA, tB, mr, q);
    drain();

    REQUIRE(eg.same(tsA, tsB));

    ExplainResult r = eg.explainEquality(tsA, tsB);
    REQUIRE(r.ok);
    REQUIRE(r.reasons.size() == 1);   // only A = B is asserted along the tower
    CHECK(r.reasons[0].var == abLit.var);
    CHECK(r.reasons[0].sign == abLit.sign);
}
