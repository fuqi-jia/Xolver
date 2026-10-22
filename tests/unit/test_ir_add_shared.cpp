// Native construction keeps explicit fresh allocations separate, while shared
// construction uses SOMTParser structural equality. Binder declarations retain
// identity; equal numeric constants can be shared across distinct allocations.

#include "ir/NativeTerms.h"
#include <doctest/doctest.h>

using namespace xolver;

namespace {

SortId mkIntSort(NativeTerms& ir) {
    SortId s = ir.allocateSortId();
    ir.registerSort(s, SortKind::Int);
    ir.setIntSortId(s);
    return s;
}

ExprId mkConstInt(NativeTerms& ir, int64_t v, SortId intSort, bool shared) {
    TermExpr e;
    e.kind = Kind::ConstInt;
    e.sort = intSort;
    e.payload = Payload(v);
    return shared ? ir.addShared(std::move(e)) : ir.add(std::move(e));
}

ExprId mkAdd(NativeTerms& ir, ExprId a, ExprId b, SortId intSort, bool shared) {
    TermExpr e;
    e.kind = Kind::Add;
    e.sort = intSort;
    e.children.push_back(a);
    e.children.push_back(b);
    return shared ? ir.addShared(std::move(e)) : ir.add(std::move(e));
}

}  // namespace

TEST_CASE("NativeTerms::add ALWAYS allocates fresh ExprId — parser path uniqueness") {
    NativeTerms ir;
    SortId intSort = mkIntSort(ir);

    ExprId five_a = mkConstInt(ir, 5, intSort, /*shared=*/false);
    ExprId five_b = mkConstInt(ir, 5, intSort, /*shared=*/false);
    CHECK(five_a != five_b);  // distinct allocations, even for identical content

    ExprId add_a = mkAdd(ir, five_a, five_b, intSort, /*shared=*/false);
    ExprId add_b = mkAdd(ir, five_a, five_b, intSort, /*shared=*/false);
    CHECK(add_a != add_b);  // same children but distinct parents
}

TEST_CASE("NativeTerms::addShared DEDUPS identical (kind, sort, children, payload)") {
    NativeTerms ir;
    SortId intSort = mkIntSort(ir);

    // Two ConstInt(5, Int) — should collapse to same ExprId.
    ExprId five_a = mkConstInt(ir, 5, intSort, /*shared=*/true);
    ExprId five_b = mkConstInt(ir, 5, intSort, /*shared=*/true);
    CHECK(five_a == five_b);

    // Different value -> different ExprId.
    ExprId six = mkConstInt(ir, 6, intSort, /*shared=*/true);
    CHECK(five_a != six);
}

TEST_CASE("NativeTerms::addShared dedups compound nodes with structurally-equal children") {
    NativeTerms ir;
    SortId intSort = mkIntSort(ir);

    ExprId five = mkConstInt(ir, 5, intSort, /*shared=*/true);
    ExprId six  = mkConstInt(ir, 6, intSort, /*shared=*/true);

    ExprId add_a = mkAdd(ir, five, six, intSort, /*shared=*/true);
    ExprId add_b = mkAdd(ir, five, six, intSort, /*shared=*/true);
    CHECK(add_a == add_b);

    // Child order matters — Add[5,6] != Add[6,5] in the structural sense.
    ExprId add_swapped = mkAdd(ir, six, five, intSort, /*shared=*/true);
    CHECK(add_a != add_swapped);
}

TEST_CASE("addShared dedups across add()'d children — opt-in path participation") {
    NativeTerms ir;
    SortId intSort = mkIntSort(ir);

    // Parser-style: allocate ConstInt(5) via add() (fresh each time).
    ExprId five_parser1 = mkConstInt(ir, 5, intSort, /*shared=*/false);
    ExprId five_parser2 = mkConstInt(ir, 5, intSort, /*shared=*/false);
    REQUIRE(five_parser1 != five_parser2);

    // Preprocess-style: addShared on Add with the SAME parser-allocated child.
    ExprId add_a = mkAdd(ir, five_parser1, five_parser1, intSort, /*shared=*/true);
    ExprId add_b = mkAdd(ir, five_parser1, five_parser1, intSort, /*shared=*/true);
    CHECK(add_a == add_b);  // dedup via addShared

    // Native structural sharing identifies equal constants even when their
    // construction handles differ. Bound declarations are tested separately.
    ExprId add_c = mkAdd(ir, five_parser1, five_parser2, intSort, /*shared=*/true);
    CHECK(add_a == add_c);
}

TEST_CASE("addShared dedup is sort-aware") {
    NativeTerms ir;
    SortId intSort  = mkIntSort(ir);
    SortId realSort = ir.allocateSortId();
    ir.registerSort(realSort, SortKind::Real);
    ir.setRealSortId(realSort);

    // Same value 5, different sort -> different ExprIds.
    TermExpr e1;
    e1.kind = Kind::ConstInt;
    e1.sort = intSort;
    e1.payload = Payload(int64_t(5));
    ExprId five_int = ir.addShared(std::move(e1));

    TermExpr e2;
    e2.kind = Kind::ConstReal;
    e2.sort = realSort;  // equal numerical value in a different native sort
    e2.payload = Payload(int64_t(5));
    ExprId five_real = ir.addShared(std::move(e2));

    CHECK(five_int != five_real);  // sort field distinguishes
}
