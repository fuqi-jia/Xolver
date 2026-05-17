#include "expr/ir.h"
#include "expr/CoreIteLowerer.h"
#include <doctest/doctest.h>

using namespace nlcolver;

static bool containsIte(const CoreIr& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Ite) return true;
    for (ExprId child : e.children) {
        if (containsIte(ir, child)) return true;
    }
    return false;
}

static size_t countKind(const CoreIr& ir, ExprId eid, Kind kind) {
    if (eid == NullExpr) return 0;
    const auto& e = ir.get(eid);
    size_t cnt = (e.kind == kind) ? 1 : 0;
    for (ExprId child : e.children) {
        cnt += countKind(ir, child, kind);
    }
    return cnt;
}

static size_t countVariables(const CoreIr& ir, ExprId eid) {
    return countKind(ir, eid, Kind::Variable);
}

TEST_CASE("CoreIteLowerer: lowerBoolIte produces 1 fresh var + 4 guarded assertions") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.setBoolSortId(boolSort);

    ExprId c = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c")});
    ExprId p = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("p")});
    ExprId q = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("q")});
    ExprId ite = ir.add(CoreExpr{Kind::Ite, boolSort, {c, p, q}, Payload{}});

    ir.addAssertion(ite);

    CoreIteLowerer lowerer(ir);
    std::vector<ExprId> lowered;
    for (ExprId a : ir.assertions()) {
        lowered.push_back(lowerer.lowerAssertion(a));
    }
    for (ExprId def : lowerer.generatedAssertions()) {
        lowered.push_back(def);
    }

    CHECK(lowered.size() == 5);  // 1 lowered assertion + 4 generated guards
    CHECK(!containsIte(ir, lowered[0]));

    // Count fresh variables (internal names start with __nlc_ite)
    size_t freshCount = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__nlc_ite") != std::string::npos) {
                    ++freshCount;
                }
            }
        }
    }
    CHECK(freshCount == 1);  // one fresh Bool var for the ITE
}

TEST_CASE("CoreIteLowerer: lowerTermIte produces 1 fresh term + 2 guarded assertions") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c")});
    ExprId x = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId y = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId ite = ir.add(CoreExpr{Kind::Ite, intSort, {c, x, y}, Payload{}});

    // (= z (ite c x y))
    ExprId z = ir.add(CoreExpr{Kind::Variable, intSort, {}, Payload("z")});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {z, ite}, Payload{}});
    ir.addAssertion(eq);

    CoreIteLowerer lowerer(ir);
    std::vector<ExprId> lowered;
    for (ExprId a : ir.assertions()) {
        lowered.push_back(lowerer.lowerAssertion(a));
    }
    for (ExprId def : lowerer.generatedAssertions()) {
        lowered.push_back(def);
    }

    CHECK(lowered.size() == 3);  // 1 lowered assertion + 2 generated guards
    CHECK(!containsIte(ir, lowered[0]));
    for (ExprId def : lowerer.generatedAssertions()) {
        CHECK(!containsIte(ir, def));
    }

    size_t freshCount = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__nlc_ite") != std::string::npos) {
                    ++freshCount;
                }
            }
        }
    }
    CHECK(freshCount == 1);  // one fresh term for the ITE
}

TEST_CASE("CoreIteLowerer: shared ITE is lowered only once") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c")});
    ExprId x = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId y = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId ite = ir.add(CoreExpr{Kind::Ite, intSort, {c, x, y}, Payload{}});

    // (= z1 ite) and (= z2 ite)
    ExprId z1 = ir.add(CoreExpr{Kind::Variable, intSort, {}, Payload("z1")});
    ExprId z2 = ir.add(CoreExpr{Kind::Variable, intSort, {}, Payload("z2")});
    ExprId eq1 = ir.add(CoreExpr{Kind::Eq, boolSort, {z1, ite}, Payload{}});
    ExprId eq2 = ir.add(CoreExpr{Kind::Eq, boolSort, {z2, ite}, Payload{}});
    ir.addAssertion(eq1);
    ir.addAssertion(eq2);

    CoreIteLowerer lowerer(ir);
    std::vector<ExprId> lowered;
    for (ExprId a : ir.assertions()) {
        lowered.push_back(lowerer.lowerAssertion(a));
    }
    for (ExprId def : lowerer.generatedAssertions()) {
        lowered.push_back(def);
    }

    // 2 lowered assertions + 2 guards (shared ITE -> only 1 fresh term -> 2 guards)
    CHECK(lowered.size() == 4);
    CHECK(lowerer.generatedAssertions().size() == 2);

    size_t freshCount = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__nlc_ite") != std::string::npos) {
                    ++freshCount;
                }
            }
        }
    }
    CHECK(freshCount == 1);  // still only one fresh term
}

TEST_CASE("CoreIteLowerer: nested ITE linear scale") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c1 = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c1")});
    ExprId c2 = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c2")});
    ExprId c3 = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c3")});
    ExprId a = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId b = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId d = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});

    // ite(c2, a, b)
    ExprId ite2 = ir.add(CoreExpr{Kind::Ite, intSort, {c2, a, b}, Payload{}});
    // ite(c3, a, d)
    ExprId ite3 = ir.add(CoreExpr{Kind::Ite, intSort, {c3, a, d}, Payload{}});
    // ite(c1, ite2, ite3)
    ExprId ite1 = ir.add(CoreExpr{Kind::Ite, intSort, {c1, ite2, ite3}, Payload{}});

    ExprId z = ir.add(CoreExpr{Kind::Variable, intSort, {}, Payload("z")});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {z, ite1}, Payload{}});
    ir.addAssertion(eq);

    CoreIteLowerer lowerer(ir);
    std::vector<ExprId> lowered;
    for (ExprId a : ir.assertions()) {
        lowered.push_back(lowerer.lowerAssertion(a));
    }
    for (ExprId def : lowerer.generatedAssertions()) {
        lowered.push_back(def);
    }

    // 1 lowered + 2 guards per ITE = 1 + 6 = 7
    CHECK(lowered.size() == 7);
    CHECK(lowerer.generatedAssertions().size() == 6);

    size_t freshCount = 0;
    for (ExprId id = 0; id < ir.size(); ++id) {
        const auto& e = ir.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) {
                if (s->find("__nlc_ite") != std::string::npos) {
                    ++freshCount;
                }
            }
        }
    }
    CHECK(freshCount == 3);  // 3 fresh terms for 3 ITEs
}

TEST_CASE("CoreIteLowerer: ite(c, t, t) -> t optimization") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(CoreExpr{Kind::Variable, boolSort, {}, Payload("c")});
    ExprId t = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(42))});
    ExprId ite = ir.add(CoreExpr{Kind::Ite, intSort, {c, t, t}, Payload{}});

    ExprId z = ir.add(CoreExpr{Kind::Variable, intSort, {}, Payload("z")});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {z, ite}, Payload{}});
    ir.addAssertion(eq);

    CoreIteLowerer lowerer(ir);
    std::vector<ExprId> lowered;
    for (ExprId a : ir.assertions()) {
        lowered.push_back(lowerer.lowerAssertion(a));
    }
    for (ExprId def : lowerer.generatedAssertions()) {
        lowered.push_back(def);
    }

    // Optimized away: no fresh term, no guards
    CHECK(lowered.size() == 1);
    CHECK(lowerer.generatedAssertions().empty());
}
