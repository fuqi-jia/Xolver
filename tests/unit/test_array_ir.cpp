// Array IR plumbing (Part 3A): the frontend adapter must map SMT-LIB array
// operations (select / store / (as const ...)) to the new CoreExpr kinds and
// record the (index, element) sorts of each Array sort, which SortId otherwise
// does not carry.

#include <doctest/doctest.h>
#include <somtparser/frontend/parser.h>

#include "parser/adapter.h"
#include "expr/ir.h"

using namespace zolver;

TEST_SUITE("array_ir") {

TEST_CASE("adapter maps select/store and records (Array Int Real) sort params") {
    SOMTParser::Parser parser;
    // Use non-foldable terms: a plain select, and a store read at a *different*
    // index j, so the parser cannot apply read-over-write at parse time.
    bool ok = parser.parseStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const b (Array Int Real))\n"
        "(declare-const i Int)\n"
        "(declare-const j Int)\n"
        "(declare-const v Real)\n"
        "(assert (> (select b i) 0.0))\n"
        "(assert (= (select (store b i v) j) v))\n");
    REQUIRE(ok);

    FrontendAdapter adapter(parser);
    auto ir = adapter.importProblem();
    REQUIRE(ir);

    bool sawSelect = false, sawStore = false;
    SortId arraySort = NullSort;
    for (ExprId id = 0; id < static_cast<ExprId>(ir->size()); ++id) {
        const CoreExpr& n = ir->get(id);
        if (n.kind == Kind::Select) sawSelect = true;
        if (n.kind == Kind::Store) { sawStore = true; arraySort = n.sort; }
    }
    CHECK(sawSelect);
    CHECK(sawStore);
    REQUIRE(arraySort != NullSort);

    auto params = ir->arraySortParams(arraySort);
    REQUIRE(params.has_value());
    CHECK(ir->sortKind(params->first)  == SortKind::Int);   // index
    CHECK(ir->sortKind(params->second) == SortKind::Real);  // element
}

TEST_CASE("adapter maps (as const ...) to Kind::ConstArray") {
    SOMTParser::Parser parser;
    parser.setOption("expand_functions", true);
    bool ok = parser.parseStr(
        "(set-logic QF_ALIA)\n"
        "(declare-const i Int)\n"
        "(assert (= (select ((as const (Array Int Int)) 7) i) 7))\n");
    REQUIRE(ok);

    FrontendAdapter adapter(parser);
    auto ir = adapter.importProblem();
    REQUIRE(ir);

    bool sawConstArray = false;
    for (ExprId id = 0; id < static_cast<ExprId>(ir->size()); ++id)
        if (ir->get(id).kind == Kind::ConstArray) sawConstArray = true;
    CHECK(sawConstArray);
}

}  // TEST_SUITE
