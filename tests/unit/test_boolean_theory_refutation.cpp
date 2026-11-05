#include <doctest/doctest.h>
#include "search/boolean/TheoryRefutation.h"
#include "search/refute/PolynomialBooleanRefutation.h"
#include "algebra/poly/PolynomialConverter.h"
#include "base/WorkBudget.h"
#include <xolver/Solver.h>

using namespace xolver;

TEST_CASE("Boolean refutation: inherited caller cancellation precedes private search") {
    auto sat = createSatSolver();
    const auto a = sat->newVar();
    sat->addClause({SatLit::positive(a)});
    BooleanRefutationLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::hours(1);
    size_t selected = 0, queried = 0;
    wall::endSolve();
    {
        const auto expired = std::chrono::steady_clock::now() - std::chrono::seconds(1);
        wall::DeadlineScope caller(expired);
        const auto result = refuteBooleanTheory(*sat, [&](const SatSolver&) {
            ++selected;
            return std::vector<SatLit>{SatLit::positive(a)};
        }, [&](std::span<const SatLit>) -> std::optional<std::vector<SatLit>> {
            ++queried;
            return std::vector<SatLit>{SatLit::positive(a)};
        }, limits);
        CHECK(result.exhausted);
        CHECK_FALSE(result.refuted);
        CHECK(result.assignments == 0);
        CHECK(selected == 0);
        CHECK(queried == 0);
        CHECK(wall::deadline() == expired);
    }
    CHECK_FALSE(wall::hasDeadline());
}

TEST_CASE("Boolean refutation: explained alternatives close the abstraction") {
    auto sat = createSatSolver();
    const auto a = sat->newVar(), b = sat->newVar();
    sat->addClause({SatLit::positive(a), SatLit::positive(b)});
    BooleanRefutationLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
    auto result = refuteBooleanTheory(*sat, [=](const SatSolver& model) {
        return std::vector<SatLit>{{a, model.value(a)}, {b, model.value(b)}};
    }, [](std::span<const SatLit> assignment) -> std::optional<std::vector<SatLit>> {
        for (auto literal : assignment)
            if (literal.sign) return std::vector<SatLit>{literal};
        return std::nullopt;
    }, limits);
    CHECK(result.refuted);
    CHECK(result.conflicts == 2);
}

TEST_CASE("Boolean refutation: open and invalid explanations cannot prove UNSAT") {
    for (bool invalid : {false, true}) {
        auto sat = createSatSolver();
        const auto a = sat->newVar();
        sat->addClause({SatLit::positive(a)});
        BooleanRefutationLimits limits;
        size_t published = 0;
        auto result = refuteBooleanTheory(*sat, [=](const SatSolver&) {
            return std::vector<SatLit>{SatLit::positive(a)};
        }, [=](std::span<const SatLit>) -> std::optional<std::vector<SatLit>> {
            if (invalid) return std::vector<SatLit>{SatLit::negative(a)};
            return std::nullopt;
        }, limits, [&](std::span<const SatLit>) { ++published; });
        CHECK_FALSE(result.refuted);
        CHECK(result.conflicts == 0);
        CHECK(published == 0);
    }
}

TEST_CASE("Boolean refutation: partial conflicts survive an exhausted search") {
    auto sat = createSatSolver();
    const auto a = sat->newVar(), b = sat->newVar();
    sat->addClause({SatLit::positive(a), SatLit::positive(b)});
    BooleanRefutationLimits limits;
    limits.assignments = 1;
    std::vector<std::vector<SatLit>> learned;
    const auto result = refuteBooleanTheory(*sat, [=](const SatSolver& model) {
        return std::vector<SatLit>{{a, model.value(a)}, {b, model.value(b)}};
    }, [](std::span<const SatLit> assignment) -> std::optional<std::vector<SatLit>> {
        for (auto literal : assignment) if (literal.sign) return std::vector<SatLit>{literal};
        return std::nullopt;
    }, limits, [&](std::span<const SatLit> clause) { learned.emplace_back(clause.begin(), clause.end()); });
    CHECK_FALSE(result.refuted);
    CHECK(result.exhausted);
    REQUIRE(learned.size() == 1);
    REQUIRE(learned.front().size() == 1);
    CHECK_FALSE(learned.front().front().sign);
    CHECK(sat->solve() == SatSolver::SolveResult::Sat);
}

TEST_CASE("Polynomial refutation: Boolean alternatives share real and integer explanations") {
    for (auto sort : {SortKind::Int, SortKind::Real}) {
        NativeTerms terms;
        terms.registerSort(0, sort);
        terms.registerSort(1, SortKind::Bool);
        terms.setBoolSortId(1);
        auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
        auto y = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
        auto zero = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
        auto product = terms.add(TermExpr{Kind::Mul, 0, {x, y}, {}});
        auto positiveX = terms.add(TermExpr{Kind::Gt, 1, {x, zero}, {}});
        auto positiveY = terms.add(TermExpr{Kind::Gt, 1, {y, zero}, {}});
        auto equal = terms.add(TermExpr{Kind::Eq, 1, {product, zero}, {}});
        auto negative = terms.add(TermExpr{Kind::Lt, 1, {product, zero}, {}});
        auto positive = terms.add(TermExpr{Kind::Gt, 1, {product, zero}, {}});
        auto impossible = terms.add(TermExpr{Kind::Or, 1, {equal, negative}, {}});
        auto feasible = terms.add(TermExpr{Kind::Or, 1, {equal, positive}, {}});
        BooleanRefutationLimits limits;
        limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
        PolynomialBooleanStatistics stats;
        CHECK(refutePolynomialBoolean(terms, {positiveX, positiveY, impossible}, limits, &stats));
        CHECK(stats.boolean.conflicts == 2);
        CHECK_FALSE(refutePolynomialBoolean(terms, {positiveX, positiveY, feasible}, limits));
        limits.assignments = 1;
        std::vector<PolynomialTheoryClause> learned;
        CHECK_FALSE(refutePolynomialBoolean(terms, {positiveX, positiveY, impossible}, limits, &stats,
            [&](const PolynomialTheoryClause& clause) { learned.push_back(clause); }));
        REQUIRE(learned.size() == 1);
        for (int vx : {-1, 0, 1}) for (int vy : {-1, 0, 1}) {
            bool valid = false;
            for (const auto& [expression, sign] : learned.front()) {
                REQUIRE((expression == positiveX || expression == positiveY || expression == equal || expression == negative));
                const bool value = expression == positiveX ? vx > 0 : expression == positiveY ? vy > 0 :
                    expression == equal ? vx * vy == 0 : vx * vy < 0;
                valid |= value == sign;
            }
            CHECK(valid);
        }
        limits.deadline = std::chrono::steady_clock::now();
        CHECK_FALSE(refutePolynomialBoolean(terms, {positiveX, positiveY, impossible}, limits));
    }
}

TEST_CASE("Polynomial refutation: unsupported products remain open and Boolean equality is exact") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    terms.registerSort(1, SortKind::Bool);
    terms.setBoolSortId(1);
    auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    auto zero = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(0))});
    auto one = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(1))});
    auto divzero = terms.add(TermExpr{Kind::Div, 0, {one, zero}, {}});
    auto product = terms.add(TermExpr{Kind::Mul, 0, {x, divzero}, {}});
    auto fixed = terms.add(TermExpr{Kind::Eq, 1, {x, one}, {}});
    auto partial = terms.add(TermExpr{Kind::Eq, 1, {product, zero}, {}});
    BooleanRefutationLimits limits;
    limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
    CHECK_FALSE(refutePolynomialBoolean(terms, {fixed, partial}, limits));
    auto positive = terms.add(TermExpr{Kind::Gt, 1, {x, zero}, {}});
    auto negative = terms.add(TermExpr{Kind::Lt, 1, {x, zero}, {}});
    auto truth = terms.add(TermExpr{Kind::ConstBool, 1, {}, Payload(true)});
    auto equivalence = terms.add(TermExpr{Kind::Eq, 1, {positive, truth}, {}});
    CHECK(refutePolynomialBoolean(terms, {negative, equivalence}, limits));
}

TEST_CASE("Polynomial refutation: large contexts retain exact linear reasoning over monomials") {
    for (const auto sort : {SortKind::Int, SortKind::Real}) {
        for (const bool feasible : {false, true}) {
            CAPTURE(sort);
            CAPTURE(feasible);
            NativeTerms terms;
            terms.registerSort(0, sort);
            terms.registerSort(1, SortKind::Bool);
            terms.setBoolSortId(1);
            const auto zero = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(0))});
            const auto one = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(1))});
            const auto three = terms.add({Kind::ConstInt, 0, {}, Payload(int64_t(3))});
            const auto x = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
            const auto y = terms.add({Kind::Variable, 0, {}, Payload(std::string("y"))});
            const auto product = terms.add({Kind::Mul, 0, {x, y}, {}});
            const auto difference = terms.add({Kind::Sub, 0, {x, y}, {}});
            const auto sum = terms.add({Kind::Add, 0, {product, difference}, {}});
            std::vector<ExprId> roots;
            for (int i = 0; i < 160; ++i) {
                const auto variable = terms.add({Kind::Variable, 0, {},
                    Payload("padding_" + std::to_string(i))});
                roots.push_back(terms.add({Kind::Geq, 1, {variable, zero}, {}}));
            }
            roots.push_back(terms.add({Kind::Geq, 1, {product, one}, {}}));
            roots.push_back(terms.add({Kind::Geq, 1, {difference, zero}, {}}));
            roots.push_back(terms.add({Kind::Leq, 1, {sum, feasible ? three : zero}, {}}));
            BooleanRefutationLimits limits;
            limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(5);
            PolynomialBooleanStatistics stats;
            CHECK(refutePolynomialBoolean(terms, roots, limits, &stats) == !feasible);
            CHECK(stats.largestContext == roots.size());
            CHECK(stats.theoryCalls > 0);
            CHECK(stats.linearCalls > 0);
            // For the open variant, x=y=1 and every padding variable=0 is
            // a real and integer witness. An open relaxation cannot refute it.
        }
    }
}

TEST_CASE("Polynomial refutation: inferred integer endpoints respect native variable sorts") {
    for (unsigned integerMask : {0u, 1u, 4u, 7u}) {
        CAPTURE(integerMask);
        NativeTerms terms;
        terms.registerSort(0, SortKind::Int);
        terms.registerSort(1, SortKind::Real);
        terms.registerSort(2, SortKind::Bool);
        terms.setBoolSortId(2);
        const SortId arithmeticSort = integerMask == 7 ? 0 : 1;
        auto op = [&](Kind kind, std::initializer_list<ExprId> children, SortId sort) {
            TermExpr node{kind, sort, {}, {}};
            for (auto child : children) node.children.push_back(child);
            return terms.add(std::move(node));
        };
        auto variable = [&](const char* name, unsigned bit) {
            const SortId sort = integerMask & bit ? 0 : 1;
            const auto value = terms.add({Kind::Variable, sort, {}, Payload(std::string(name))});
            return sort == arithmeticSort ? value : op(Kind::ToReal, {value}, arithmeticSort);
        };
        const auto x = variable("x", 1), y = variable("y", 2), z = variable("z", 4);
        const auto zero = terms.add({Kind::ConstInt, arithmeticSort, {}, Payload(int64_t(0))});
        const auto one = terms.add({Kind::ConstInt, arithmeticSort, {}, Payload(int64_t(1))});
        const auto product = op(Kind::Mul, {x, y}, arithmeticSort);
        const auto target = op(Kind::Add,
            {op(Kind::Sub, {product, y}, arithmeticSort), one}, arithmeticSort);
        const std::vector<ExprId> roots{
            op(Kind::Geq, {x, zero}, 2), op(Kind::Geq, {z, zero}, 2),
            op(Kind::Geq, {op(Kind::Mul, {x, z}, arithmeticSort), one}, 2),
            op(Kind::Geq, {y, one}, 2), op(Kind::Leq, {target, zero}, 2)};
        BooleanRefutationLimits limits;
        limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
        CHECK(refutePolynomialBoolean(terms, roots, limits) == bool(integerMask & 1));
        // With real x, x=1/2,y=z=2 remains a witness even when z is Int.
    }
}

TEST_CASE("Polynomial refutation: integer endpoint explanations withdraw with assumptions and scopes") {
    Solver solver;
    solver.setLogic("QF_NIA");
    auto op = [&](Kind kind, std::vector<Term> children) {
        return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
    };
    const auto x = solver.mkConst(solver.intSort(), "x");
    const auto y = solver.mkConst(solver.intSort(), "y");
    const auto z = solver.mkConst(solver.intSort(), "z");
    const auto p = solver.mkConst(solver.boolSort(), "p");
    const auto notP = op(Kind::Not, {p});
    const auto zero = solver.mkInt(0), one = solver.mkInt(1);
    solver.assertFormula(op(Kind::Geq, {x, zero}));
    solver.assertFormula(op(Kind::Geq, {z, zero}));
    solver.assertFormula(op(Kind::Geq, {op(Kind::Mul, {x, z}), one}));
    solver.assertFormula(op(Kind::Geq, {y, one}));
    const auto target = op(Kind::Add, {op(Kind::Sub, {op(Kind::Mul, {x, y}), y}), one});
    solver.assertFormula(op(Kind::Implies, {p, op(Kind::Leq, {target, zero})}));
    for (int repeat = 0; repeat < 2; ++repeat) {
        REQUIRE((solver.checkSatAssuming({p}) == Result::Unsat));
        const auto core = solver.getUnsatCore();
        CHECK(std::find(core.begin(), core.end(), p) != core.end());
        REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        solver.push();
        solver.assertFormula(p);
        REQUIRE((solver.checkSat() == Result::Unsat));
        solver.pop();
        REQUIRE((solver.checkSat() == Result::Sat));
        CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
    }
}

TEST_CASE("Polynomial conversion: bounded expansion and unrepresentable powers stay open") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    auto x = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("x"))});
    auto y = terms.add(TermExpr{Kind::Variable, 0, {}, Payload(std::string("y"))});
    auto sum = terms.add(TermExpr{Kind::Add, 0, {x, y}, {}});
    auto twenty = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(int64_t(20))});
    auto power = terms.add(TermExpr{Kind::Pow, 0, {sum, twenty}, {}});
    auto kernel = createPolynomialKernel();
    WorkBudget budget(64);
    PolynomialConverter bounded(*kernel, &budget);
    CHECK_THROWS_AS(bounded.convert(power, terms), ResourceExhausted);
    PolynomialConverter ordinary(*kernel);
    for (int64_t exponent : {int64_t(4294967296LL), int64_t(4294967297LL)}) {
        auto count = terms.add(TermExpr{Kind::ConstInt, 0, {}, Payload(exponent)});
        auto huge = terms.add(TermExpr{Kind::Pow, 0, {x, count}, {}});
        CHECK_FALSE(ordinary.convert(huge, terms).ok());
    }
}

TEST_CASE("Polynomial refutation: runtime explanations respect assumptions and scopes") {
    for (bool integer : {false, true}) {
        Solver solver;
        solver.setLogic(integer ? "QF_NIA" : "QF_NRA");
        auto op = [&](Kind kind, std::vector<Term> children) {
            return solver.mkOp(static_cast<uint32_t>(kind), std::move(children));
        };
        const auto sort = integer ? solver.intSort() : solver.realSort();
        const auto x = solver.mkConst(sort, "x");
        const auto y = solver.mkConst(sort, "y");
        const auto p = solver.mkConst(solver.boolSort(), "p");
        const auto zero = integer ? solver.mkInt(0) : solver.mkReal("0");
        const auto product = op(Kind::Mul, {x, y});
        const auto impossible = op(Kind::Or, {
            op(Kind::Eq, {product, zero}), op(Kind::Lt, {product, zero})});
        const auto notP = op(Kind::Not, {p});
        solver.assertFormula(op(Kind::Gt, {x, zero}));
        solver.assertFormula(op(Kind::Gt, {y, zero}));
        solver.assertFormula(op(Kind::Implies, {p, impossible}));
        for (int repeat = 0; repeat < 2; ++repeat) {
            REQUIRE((solver.checkSatAssuming({p}) == Result::Unsat));
            const auto core = solver.getUnsatCore();
            CHECK(std::find(core.begin(), core.end(), p) != core.end());
            REQUIRE((solver.checkSatAssuming({notP}) == Result::Sat));
            CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
            solver.push();
            solver.assertFormula(p);
            REQUIRE((solver.checkSat() == Result::Unsat));
            solver.pop();
            REQUIRE((solver.checkSat() == Result::Sat));
            CHECK(solver.validateModel() == Solver::ModelValidation::Satisfied);
        }
    }
}

TEST_CASE("Boolean refutation: the last allowed theory conflict receives a final SAT check") {
    // inconsistent() is an optional construction-time shortcut; the interface
    // permits a backend to report contradictions only through solve().
    class SolveOnlyBackend final : public SatSolver {
        std::unique_ptr<SatSolver> backend_ = createSatSolver();
    public:
        size_t solveCalls = 0;
        SatVar newVar() override { return backend_->newVar(); }
        void addClause(const std::vector<SatLit>& clause) override { backend_->addClause(clause); }
        void addTheoryClause(const std::vector<SatLit>& clause) override { backend_->addTheoryClause(clause); }
        SolveResult solve() override { ++solveCalls; return backend_->solve(); }
        SolveResult solve(const std::vector<SatLit>& assumptions) override {
            ++solveCalls;
            return backend_->solve(assumptions);
        }
        bool value(SatVar variable) const override { return backend_->value(variable); }
        bool limit(const char* name, int value) override { return backend_->limit(name, value); }
        void setDeadline(std::chrono::steady_clock::time_point deadline) override {
            backend_->setDeadline(deadline);
        }
    };
    for (size_t allocation : {size_t(3), size_t(4)}) {
        auto sat = std::make_unique<SolveOnlyBackend>();
        const auto a = sat->newVar(), b = sat->newVar();
        BooleanRefutationLimits limits;
        limits.assignments = allocation;
        limits.deadline = std::chrono::steady_clock::now() + std::chrono::seconds(1);
        const auto result = refuteBooleanTheory(*sat, [=](const SatSolver& model) {
            return std::vector<SatLit>{{a, model.value(a)}, {b, model.value(b)}};
        }, [](std::span<const SatLit> assignment) -> std::optional<std::vector<SatLit>> {
            return std::vector<SatLit>(assignment.begin(), assignment.end());
        }, limits);
        CHECK(result.refuted == (allocation == 4));
        CHECK(result.exhausted == (allocation == 3));
        CHECK(result.assignments == allocation);
        CHECK(result.conflicts == allocation);
        CHECK(sat->solveCalls == allocation + 1);
    }
}
