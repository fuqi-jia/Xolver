#include <doctest/doctest.h>
#include "base/EnvParam.h"
#include "applications/smt/qfnia/NiaSolver.h"
#include "search/arith/Reasoner.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <limits>
#include <stdexcept>

using namespace xolver;

namespace {
// Invoke real registered callbacks so unrelated SAT-finding stages cannot
// short-circuit the cardinality check under test.
class EnumerationStageProbe : public NiaSolver {
public:
    using NiaSolver::NiaSolver;
    std::optional<TheoryCheckResult> runStage(const std::string& name,
                                             TheoryLemmaStorage& db) {
        for (auto& stage : reasoners_) {
            if (stage->name() == name) return stage->run(db, TheoryEffort::Full);
        }
        throw std::runtime_error("missing NIA stage: " + name);
    }
};
}

TEST_CASE("NiaSolver: escalating enumeration respects Boolean cardinality limits") {
    struct Case { int booleans; long budget; bool candidate; };
    const int digits = std::numeric_limits<long>::digits;
    const long largest = std::numeric_limits<long>::max();
    for (const Case c : {Case{0, 2, true}, Case{1, 3, false}, Case{1, 4, true},
                         Case{digits - 1, largest, false},
                         Case{digits, largest, false},
                         Case{digits + 1, largest, false}}) {
        CAPTURE(c.booleans); CAPTURE(c.budget);
        env::Scope scope(env::Snapshot::capture({
            {"XOLVER_NIA_BOUNDED_ENUM_THRESHOLD", std::to_string(c.budget)}}));
        NativeTerms terms;
        const SortId bs = terms.allocateSortId();
        terms.registerSort(bs, SortKind::Bool); terms.setBoolSortId(bs);
        const SortId is = terms.allocateSortId();
        terms.registerSort(is, SortKind::Int); terms.setIntSortId(is);
        const ExprId x = terms.add({Kind::Variable, is, {}, Payload(std::string("x"))});
        const ExprId zero = terms.add({Kind::ConstInt, is, {}, Payload(int64_t(0))});
        TermExpr bound; bound.kind = Kind::Geq; bound.sort = bs; bound.children = {x, zero};
        const ExprId boundId = terms.add(bound);
        terms.addAssertion(boundId);
        for (int i = 0; i < c.booleans; ++i) {
            terms.addAssertion(terms.add({Kind::Variable, bs, {},
                                          Payload("b" + std::to_string(i))}));
        }
        auto kernel = createPolynomialKernel();
        const PolyId poly = kernel->mkVar(kernel->getOrCreateVar("x"));
        EnumerationStageProbe solver(std::move(kernel));
        solver.setNativeTerms(&terms);
        TheoryAtomRecord atom{1, TheoryId::NIA, false, boundId,
            PolynomialAtomPayload{poly, Relation::Geq, RealValue::fromInt(0)}};
        solver.assertLit(atom, true, 0, SatLit::positive(1));
        TheoryLemmaDatabase db;
        REQUIRE_FALSE(solver.runStage("nia.normalize", db).has_value());
        REQUIRE_FALSE(solver.runStage("nia.domain", db).has_value());
        const auto result = solver.runStage("nia.escalating-bounded", db);
        CHECK(result.has_value() == c.candidate);
        if (result) CHECK(result->kind == TheoryCheckResult::Kind::Consistent);
    }
}
