#include <doctest/doctest.h>
#include "expr/ir.h"
#include "frontend/preprocess/ArithCastNormalizer.h"
#include "frontend/preprocess/LinearToIntPurifier.h"
#include "expr/CoreIteLowerer.h"
#include "theory/LogicFeatureDetector.h"
#include <iostream>

using namespace nlcolver;

TEST_CASE("Debug: LogicFeatureDetector after purification") {
    CoreIr ir;
    SortId boolSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.setBoolSortId(boolSort);
    SortId intSort = ir.allocateSortId();
    ir.registerSort(intSort, SortKind::Int);
    ir.setIntSortId(intSort);
    SortId realSort = ir.allocateSortId();
    ir.registerSort(realSort, SortKind::Real);
    ir.setRealSortId(realSort);

    // Build: (= (to_int x) 3)
    ExprId x = ir.add(CoreExpr{Kind::Variable, realSort, {}, Payload(std::string("x"))});
    ExprId toInt = ir.add(CoreExpr{Kind::ToInt, intSort, {x}, {}});
    ExprId three = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});
    ExprId eq = ir.add(CoreExpr{Kind::Eq, boolSort, {toInt, three}, {}});
    ir.addAssertion(eq);

    // Build: (= x (/ 7 2))
    ExprId seven = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(7))});
    ExprId two = ir.add(CoreExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId div = ir.add(CoreExpr{Kind::Div, realSort, {seven, two}, {}});
    ExprId eq2 = ir.add(CoreExpr{Kind::Eq, boolSort, {x, div}, {}});
    ir.addAssertion(eq2);

    // Run passes
    {
        CoreIteLowerer lowerer(ir);
        auto originalScoped = ir.getScopedAssertions();
        std::vector<std::pair<ScopeLevel, ExprId>> loweredScoped;
        for (const auto& [level, a] : originalScoped) {
            size_t before = lowerer.generatedAssertions().size();
            ExprId la = lowerer.lowerAssertion(a);
            loweredScoped.push_back({level, la});
            for (size_t i = before; i < lowerer.generatedAssertions().size(); ++i) {
                loweredScoped.push_back({level, lowerer.generatedAssertions()[i]});
            }
        }
        ir.clearAssertions();
        for (const auto& [level, a] : loweredScoped) {
            ir.addAssertion(a, level);
        }
    }

    {
        ArithCastNormalizer norm(ir);
        auto result = norm.run();
        ir.clearAssertions();
        for (const auto& [level, a] : result.assertions) {
            ir.addAssertion(a, level);
        }
    }

    {
        LinearToIntPurifier purifier(ir);
        auto purifyResult = purifier.run();
        ir.clearAssertions();
        for (const auto& [level, a] : purifyResult.purifiedAssertions) {
            ir.addAssertion(a, level);
        }
        for (const auto& [level, lemma] : purifyResult.floorLemmas) {
            ir.addAssertion(lemma, level);
        }
    }

    // Now detect features
    LogicFeatureDetector detector(ir);
    LogicFeatures features = detector.detect();

    std::cerr << "hasBool=" << features.hasBool
              << " Int=" << features.hasInt
              << " Real=" << features.hasReal
              << " UF=" << features.hasUF
              << " NL=" << features.hasNonlinear
              << " Mixed=" << features.hasMixedIntReal
              << " Unsupported=" << features.hasUnsupported
              << "\n";

    REQUIRE(!features.hasNonlinear);
    REQUIRE(!features.hasUnsupported);
}
