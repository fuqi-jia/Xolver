#include "ir/NativeTerms.h"
#include "frontend/preprocess/IteLowerer.h"
#include "ir/NumericLiteral.h"
#include "algebra/linear/LinearExpr.h"
#include <doctest/doctest.h>

using namespace xolver;

static bool containsIte(const NativeTerms& ir, ExprId eid) {
    if (eid == NullExpr) return false;
    const auto& e = ir.get(eid);
    if (e.kind == Kind::Ite) return true;
    for (ExprId child : e.children) {
        if (containsIte(ir, child)) return true;
    }
    return false;
}

static size_t countKind(const NativeTerms& ir, ExprId eid, Kind kind) {
    if (eid == NullExpr) return 0;
    const auto& e = ir.get(eid);
    size_t cnt = (e.kind == kind) ? 1 : 0;
    for (ExprId child : e.children) {
        cnt += countKind(ir, child, kind);
    }
    return cnt;
}

static size_t countVariables(const NativeTerms& ir, ExprId eid) {
    return countKind(ir, eid, Kind::Variable);
}

TEST_CASE("IteLowerer: wide shared DAG preserves nested Boolean and arithmetic choices") {
    for (const auto kind : {SortKind::Int, SortKind::Real}) {
        NativeTerms ir;
        const auto boolean = ir.allocateSortId();
        const auto arithmetic = ir.allocateSortId();
        ir.registerSort(boolean, SortKind::Bool);
        ir.registerSort(arithmetic, kind);
        ir.setBoolSortId(boolean);
        if (kind == SortKind::Int) ir.setIntSortId(arithmetic);
        else ir.setRealSortId(arithmetic);
        auto variable = [&](SortId sort, const std::string& name) {
            return ir.add(TermExpr{Kind::Variable, sort, {}, Payload(name)});
        };
        const auto flag = variable(boolean, "flag");
        const auto p = variable(boolean, "p"), q = variable(boolean, "q");
        const auto condition = ir.add(TermExpr{Kind::Ite, boolean, {flag, p, q}, Payload{}});
        const auto x = variable(arithmetic, "x"), y = variable(arithmetic, "y");
        const auto choice = ir.add(TermExpr{Kind::Ite, arithmetic, {condition, x, y}, Payload{}});
        TermExpr conjunction{Kind::And, boolean, {}, Payload{}};
        std::vector<ExprId> originalVariables;
        for (size_t i = 0; i < 4096; ++i) {
            const auto z = variable(arithmetic, "z" + std::to_string(i));
            originalVariables.push_back(z);
            conjunction.children.push_back(ir.add(TermExpr{Kind::Eq, boolean, {z, choice}, Payload{}}));
        }
        const auto root = ir.add(std::move(conjunction));
        IteLowerer lowerer(ir);
        const auto lowered = lowerer.lowerAssertion(root);
        CHECK_FALSE(containsIte(ir, lowered));
        REQUIRE(ir.get(lowered).children.size() == originalVariables.size());
        REQUIRE(lowerer.generatedAssertions().size() == 6);
        const auto replacement = ir.get(ir.get(lowered).children[0]).children[1];
        CHECK(ir.get(replacement).sort == arithmetic);
        for (size_t i = 0; i < originalVariables.size(); ++i) {
            const auto& equality = ir.get(ir.get(lowered).children[i]);
            REQUIRE(equality.kind == Kind::Eq);
            CHECK(equality.children[0] == originalVariables[i]);
            CHECK(equality.children[1] == replacement);
        }
        // A second root reuses the same nested choices and their definitions.
        const auto other = ir.add(TermExpr{Kind::Or, boolean, {root, condition}, Payload{}});
        const auto loweredOther = lowerer.lowerAssertion(other);
        CHECK_FALSE(containsIte(ir, loweredOther));
        CHECK(ir.get(loweredOther).children[0] == lowered);
        CHECK(lowerer.generatedAssertions().size() == 6);
    }
}

TEST_CASE("IteLowerer: lowerBoolIte produces 1 fresh var + 4 guarded assertions") {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.setBoolSortId(boolSort);

    ExprId c = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c"))});
    ExprId p = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("p"))});
    ExprId q = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("q"))});
    ExprId ite = ir.add(TermExpr{Kind::Ite, boolSort, {c, p, q}, Payload{}});

    ir.addAssertion(ite);

    IteLowerer lowerer(ir);
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

TEST_CASE("IteLowerer: lowerTermIte produces 1 fresh term + 2 guarded assertions") {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c"))});
    ExprId x = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId y = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId ite = ir.add(TermExpr{Kind::Ite, intSort, {c, x, y}, Payload{}});

    // (= z (ite c x y))
    ExprId z = ir.add(TermExpr{Kind::Variable, intSort, {}, Payload(std::string("z"))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {z, ite}, Payload{}});
    ir.addAssertion(eq);

    IteLowerer lowerer(ir);
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

TEST_CASE("IteLowerer: shared ITE is lowered only once") {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c"))});
    ExprId x = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId y = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId ite = ir.add(TermExpr{Kind::Ite, intSort, {c, x, y}, Payload{}});

    // (= z1 ite) and (= z2 ite)
    ExprId z1 = ir.add(TermExpr{Kind::Variable, intSort, {}, Payload(std::string("z1"))});
    ExprId z2 = ir.add(TermExpr{Kind::Variable, intSort, {}, Payload(std::string("z2"))});
    ExprId eq1 = ir.add(TermExpr{Kind::Eq, boolSort, {z1, ite}, Payload{}});
    ExprId eq2 = ir.add(TermExpr{Kind::Eq, boolSort, {z2, ite}, Payload{}});
    ir.addAssertion(eq1);
    ir.addAssertion(eq2);

    IteLowerer lowerer(ir);
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

TEST_CASE("IteLowerer: nested ITE linear scale") {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c1 = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c1"))});
    ExprId c2 = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c2"))});
    ExprId c3 = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c3"))});
    ExprId a = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(1))});
    ExprId b = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(2))});
    ExprId d = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(3))});

    // ite(c2, a, b)
    ExprId ite2 = ir.add(TermExpr{Kind::Ite, intSort, {c2, a, b}, Payload{}});
    // ite(c3, a, d)
    ExprId ite3 = ir.add(TermExpr{Kind::Ite, intSort, {c3, a, d}, Payload{}});
    // ite(c1, ite2, ite3)
    ExprId ite1 = ir.add(TermExpr{Kind::Ite, intSort, {c1, ite2, ite3}, Payload{}});

    ExprId z = ir.add(TermExpr{Kind::Variable, intSort, {}, Payload(std::string("z"))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {z, ite1}, Payload{}});
    ir.addAssertion(eq);

    IteLowerer lowerer(ir);
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

TEST_CASE("IteLowerer: ite(c, t, t) -> t optimization") {
    NativeTerms ir;
    SortId boolSort = ir.allocateSortId();
    SortId intSort = ir.allocateSortId();
    ir.registerSort(boolSort, SortKind::Bool);
    ir.registerSort(intSort, SortKind::Int);
    ir.setBoolSortId(boolSort);
    ir.setIntSortId(intSort);

    ExprId c = ir.add(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c"))});
    ExprId t = ir.add(TermExpr{Kind::ConstInt, intSort, {}, Payload(int64_t(42))});
    ExprId ite = ir.add(TermExpr{Kind::Ite, intSort, {c, t, t}, Payload{}});

    ExprId z = ir.add(TermExpr{Kind::Variable, intSort, {}, Payload(std::string("z"))});
    ExprId eq = ir.add(TermExpr{Kind::Eq, boolSort, {z, ite}, Payload{}});
    ir.addAssertion(eq);

    IteLowerer lowerer(ir);
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

namespace {
using ArithmeticValues = std::unordered_map<ExprId, mpq_class>;
mpq_class evaluateChoice(const NativeTerms& ir, ExprId id, const ArithmeticValues& values) {
    if (const auto it = values.find(id); it != values.end()) return it->second;
    const auto node = ir.get(id);
    if (const auto value = numericLiteral(node)) return *value;
    if (node.kind == Kind::ConstBool) return std::get<bool>(node.payload.value) ? 1 : 0;
    auto child = [&](size_t i) { return evaluateChoice(ir, node.children[i], values); };
    if (node.kind == Kind::Not) return child(0) == 0 ? 1 : 0;
    if (node.kind == Kind::Or) return child(0) != 0 || child(1) != 0 ? 1 : 0;
    if (node.kind == Kind::Eq) return child(0) == child(1) ? 1 : 0;
    if (node.kind == Kind::Ite) return child(0) != 0 ? child(1) : child(2);
    if (node.kind == Kind::Neg) return -child(0);
    mpq_class result = node.kind == Kind::Mul ? 1 : 0;
    for (size_t i = 0; i < node.children.size(); ++i) {
        const auto value = child(i);
        if (node.kind == Kind::Add) result += value;
        else if (node.kind == Kind::Mul) result *= value;
        else if (node.kind == Kind::Sub) result += i == 0 && node.children.size() > 1 ? value : mpq_class(-value);
        else { FAIL("unexpected expression in arithmetic-choice witness replay"); return 0; }
    }
    return result;
}

void replayChoiceDefinitions(const NativeTerms& ir, const std::vector<ExprId>& definitions,
                             ArithmeticValues& values) {
    // Both guarded equations are retained. Give each fresh residual exactly
    // the value of its selected branch, then check both implications.
    for (auto definition : definitions) {
        const auto guard = ir.get(definition);
        REQUIRE(guard.kind == Kind::Or);
        if (evaluateChoice(ir, guard.children[0], values) != 0) continue;
        const auto equation = ir.get(guard.children[1]);
        REQUIRE(equation.kind == Kind::Eq);
        values[equation.children[0]] = evaluateChoice(ir, equation.children[1], values);
    }
    for (auto definition : definitions) CHECK(evaluateChoice(ir, definition, values) == 1);
}
}

TEST_CASE("IteLowerer: affine choices preserve signed nested branch witnesses") {
    for (bool real : {false, true}) {
        NativeTerms ir;
        ir.registerSort(ir.allocateSortId(), SortKind::Bool);
        ir.registerSort(ir.allocateSortId(), SortKind::Int);
        ir.registerSort(ir.allocateSortId(), SortKind::Real);
        const auto sort = real ? ir.realSortId() : ir.intSortId();
        const auto boolSort = ir.boolSortId();
        auto variable = [&](const char* name, SortId type) {
            return ir.addShared(TermExpr{Kind::Variable, type, {}, Payload(std::string(name))});
        };
        auto constant = [&](long value) {
            return ir.addShared(TermExpr{real ? Kind::ConstReal : Kind::ConstInt, sort, {}, Payload(int64_t(value))});
        };
        const auto x = variable("x", sort), c = variable("c", boolSort), d = variable("d", boolSort);
        const auto base = ir.addShared(TermExpr{Kind::Mul, sort, {constant(-3), x}, Payload{}});
        const auto a = ir.addShared(TermExpr{Kind::Add, sort, {base, constant(-7)}, Payload{}});
        const auto b = ir.addShared(TermExpr{Kind::Add, sort, {base, constant(5)}, Payload{}});
        const auto inner = ir.addShared(TermExpr{Kind::Ite, sort, {d, a, b}, Payload{}});
        const auto outer = ir.addShared(TermExpr{Kind::Ite, sort, {c, inner, base}, Payload{}});
        const auto assertion = ir.addShared(TermExpr{Kind::Eq, boolSort, {x, outer}, Payload{}});
        IteLowerer lowerer(ir);
        const auto lowered = ir.get(lowerer.lowerAssertion(assertion)).children[1];
        CHECK_FALSE(containsIte(ir, lowered));
        for (long numerator = -5; numerator <= 5; ++numerator) {
            for (int choices = 0; choices < 4; ++choices) {
                ArithmeticValues values{{x, mpq_class(numerator, real ? 2 : 1)},
                                        {c, choices & 1}, {d, (choices >> 1) & 1}};
                const auto expected = evaluateChoice(ir, outer, values);
                replayChoiceDefinitions(ir, lowerer.generatedAssertions(), values);
                CHECK(evaluateChoice(ir, lowered, values) == expected);
            }
        }
    }
}

TEST_CASE("IteLowerer: integer residual choices expose a nonzero affine lattice") {
    NativeTerms ir;
    ir.registerSort(ir.allocateSortId(), SortKind::Bool);
    ir.registerSort(ir.allocateSortId(), SortKind::Int);
    const auto sort = ir.intSortId(), boolSort = ir.boolSortId();
    const auto x = ir.addShared(TermExpr{Kind::Variable, sort, {}, Payload(std::string("x"))});
    const auto c = ir.addShared(TermExpr{Kind::Variable, boolSort, {}, Payload(std::string("c"))});
    auto offset = [&](long value) {
        const auto number = ir.addShared(TermExpr{Kind::ConstInt, sort, {}, Payload(int64_t(value))});
        return ir.addShared(TermExpr{Kind::Add, sort, {x, number}, Payload{}});
    };
    const auto choice = ir.addShared(TermExpr{Kind::Ite, sort, {c, offset(-5), offset(7)}, Payload{}});
    const auto assertion = ir.addShared(TermExpr{Kind::Eq, boolSort, {choice, x}, Payload{}});
    IteLowerer lowerer(ir);
    const auto lowered = ir.get(lowerer.lowerAssertion(assertion)).children[0];
    std::unordered_map<std::string, mpq_class> coefficients;
    mpq_class constant;
    REQUIRE(extractLinearExpr(lowered, ir, coefficients, constant));
    CHECK(constant == -5);
    CHECK(coefficients.at("x") == 1);
    coefficients.erase("x");
    REQUIRE(coefficients.size() == 1);
    CHECK(coefficients.begin()->second == 12);
    for (long value = -3; value <= 3; ++value) {
        for (int selected = 0; selected <= 1; ++selected) {
            ArithmeticValues values{{x, value}, {c, selected}};
            replayChoiceDefinitions(ir, lowerer.generatedAssertions(), values);
            CHECK(evaluateChoice(ir, lowered, values) == value + (selected ? -5 : 7));
        }
    }
}

TEST_CASE("IteLowerer: factoring residual coefficients preserves nonlinear common atoms") {
    NativeTerms ir;
    ir.registerSort(ir.allocateSortId(), SortKind::Bool);
    ir.registerSort(ir.allocateSortId(), SortKind::Int);
    const auto sort = ir.intSortId(), boolSort = ir.boolSortId();
    auto variable = [&](const char* name, SortId type) {
        return ir.addShared(TermExpr{Kind::Variable, type, {}, Payload(std::string(name))});
    };
    auto number = [&](long value) {
        return ir.addShared(TermExpr{Kind::ConstInt, sort, {}, Payload(int64_t(value))});
    };
    const auto x = variable("x", sort), y = variable("y", sort), z = variable("z", sort);
    const auto c = variable("c", boolSort);
    const auto common = ir.addShared(TermExpr{Kind::Mul, sort, {x, y}, Payload{}});
    const auto leftTerm = ir.addShared(TermExpr{Kind::Mul, sort, {number(3), y}, Payload{}});
    const auto rightTerm = ir.addShared(TermExpr{Kind::Mul, sort, {number(-9), z}, Payload{}});
    const auto left = ir.addShared(TermExpr{Kind::Add, sort, {common, leftTerm, number(7)}, Payload{}});
    const auto right = ir.addShared(TermExpr{Kind::Add, sort, {common, rightTerm, number(13)}, Payload{}});
    const auto choice = ir.addShared(TermExpr{Kind::Ite, sort, {c, left, right}, Payload{}});
    const auto assertion = ir.addShared(TermExpr{Kind::Eq, boolSort, {choice, x}, Payload{}});
    IteLowerer lowerer(ir);
    const auto lowered = ir.get(lowerer.lowerAssertion(assertion)).children[0];
    for (long a = -2; a <= 2; ++a) {
        for (long b = -2; b <= 2; ++b) {
            for (long d = -2; d <= 2; ++d) {
                for (int selected = 0; selected <= 1; ++selected) {
                    ArithmeticValues values{{x, a}, {y, b}, {z, d}, {c, selected}};
                    const auto expected = evaluateChoice(ir, choice, values);
                    replayChoiceDefinitions(ir, lowerer.generatedAssertions(), values);
                    CHECK(evaluateChoice(ir, lowered, values) == expected);
                }
            }
        }
    }
}
