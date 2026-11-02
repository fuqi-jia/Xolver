#include <doctest/doctest.h>
#include "applications/satisfiability/smt/qfnia/NiaSolver.h"
#include "evidence/ArithModelValidator.h"
#include "search/arith/Reasoner.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include "search/nia/farkas/FarkasOrDetector.h"
#include <stdexcept>

using namespace xolver;

namespace {
class FarkasStageProbe : public NiaSolver {
public:
    using NiaSolver::NiaSolver;
    std::optional<TheoryCheckResult> runFarkas(TheoryLemmaStorage& db) {
        for (auto& stage : reasoners_) {
            if (stage->name() == "nia.farkas-or") return stage->run(db, TheoryEffort::Full);
        }
        throw std::runtime_error("missing Farkas stage");
    }
};

struct FarkasFormula {
    NativeTerms terms;
    SortId ints, bools;
    ExprId x, y, l0, l1, branch, disjunction, nonnegative;

    FarkasFormula() {
        ints = terms.allocateSortId(); terms.registerSort(ints, SortKind::Int);
        bools = terms.allocateSortId(); terms.registerSort(bools, SortKind::Bool);
        terms.setIntSortId(ints); terms.setBoolSortId(bools);
        x = variable("x"); y = variable("y");
        l0 = variable("l0"); l1 = variable("l1");
        const auto zero = integer(0);
        nonnegative = make(Kind::Geq, {l0, zero});
        const auto eq0 = make(Kind::Eq, {
            make(Kind::Add, {make(Kind::Mul, {integer(-4), l0}),
                             make(Kind::Mul, {x, l1})}), zero});
        const auto eq1 = make(Kind::Eq, {
            make(Kind::Add, {make(Kind::Mul, {integer(5), l0}),
                             make(Kind::Mul, {y, l1})}), zero});
        branch = make(Kind::And, {nonnegative, make(Kind::Geq, {l1, zero}),
            eq0, eq1, make(Kind::Gt, {make(Kind::Sub, {l0, integer(1)}), zero})});
        disjunction = make(Kind::Or, {branch, branch});
    }
    ExprId variable(const char* name) {
        return terms.add({Kind::Variable, ints, {}, Payload(std::string(name))});
    }
    ExprId integer(int64_t value) {
        return terms.add({Kind::ConstInt, ints, {}, Payload(value)});
    }
    ExprId make(Kind kind, std::initializer_list<ExprId> children) {
        TermExpr expr; expr.kind = kind;
        expr.sort = (kind == Kind::Add || kind == Kind::Mul || kind == Kind::Sub)
            ? ints : bools;
        for (auto child : children) expr.children.push_back(child);
        return terms.add(std::move(expr));
    }
    void assertBounds(int64_t xlo, int64_t xhi, int64_t ylo, int64_t yhi) {
        terms.addAssertion(make(Kind::And, {
            make(Kind::Geq, {x, integer(xlo)}), make(Kind::Leq, {x, integer(xhi)}),
            make(Kind::Geq, {y, integer(ylo)}), make(Kind::Leq, {y, integer(yhi)})}));
        terms.addAssertion(disjunction);
    }
};
}

TEST_CASE("NiaSolver: Farkas analysis follows assertion changes in both directions") {
    FarkasFormula f;
    auto kernel = createPolynomialKernel();
    const auto poly = kernel->mkVar(kernel->getOrCreateVar("l0"));
    FarkasStageProbe solver(std::move(kernel));
    solver.setNativeTerms(&f.terms);
    const TheoryAtomRecord atom{1, TheoryId::NIA, false, f.nonnegative,
        PolynomialAtomPayload{poly, Relation::Geq, RealValue::fromInt(0)}};
    TheoryLemmaDatabase db;
    const auto run = [&]() {
        solver.reset();
        solver.assertLit(atom, true, 0, SatLit::positive(1));
        return solver.runFarkas(db);
    };

    bool startsSat = false;
    SUBCASE("clear UNSAT assertions before a SAT query") {}
    SUBCASE("clear SAT assertions before an UNSAT query") { startsSat = true; }
    SUBCASE("pop UNSAT assertions before a SAT query") { f.terms.pushScope(); }

    if (startsSat) f.assertBounds(4, 4, -5, -5);
    else f.assertBounds(-1, 1, -1, 1);
    REQUIRE(farkas::FarkasOrDetector(f.terms).detect().good());
    const auto before = run();
    if (startsSat) {
        REQUIRE(before.has_value());
        CHECK(before->kind == TheoryCheckResult::Kind::Consistent);
    }
#ifdef XOLVER_HAS_LIBPOLY
    else {
        REQUIRE(before.has_value());
        CHECK(before->kind == TheoryCheckResult::Kind::Conflict);
    }
#endif

    if (f.terms.currentScopeLevel() > 0) f.terms.popScope();
    else f.terms.clearAssertions();
    if (startsSat) f.assertBounds(-1, 1, -1, 1);
    else f.assertBounds(4, 4, -5, -5);
    const auto after = run();
    if (startsSat) {
#ifdef XOLVER_HAS_LIBPOLY
        REQUIRE(after.has_value());
        CHECK(after->kind == TheoryCheckResult::Kind::Conflict);
#endif
    } else {
        // Check the SAT witness independently of the Farkas implementation.
        const ArithModelValidator::NumAssignment model{
            {"x", 4}, {"y", -5}, {"l0", 2}, {"l1", 2}};
        const ArithModelValidator::BoolAssignment booleans;
        CHECK(ArithModelValidator(f.terms, model, booleans).validate(f.terms.assertions())
              == ArithModelValidator::Verdict::Satisfied);
        // Exact scaling now constructs the formerly missing integer witness.
        REQUIRE(after.has_value());
        CHECK(after->kind == TheoryCheckResult::Kind::Consistent);
    }
}
