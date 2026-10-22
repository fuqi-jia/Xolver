#include <doctest/doctest.h>
#include "search/arith/Reasoner.h"
#include "applications/smt/qfnra/NraSolver.h"
#include "search/coordination/TheoryLemmaDatabase.h"
#include <stdexcept>
#include <string>

using namespace xolver;

namespace {
struct WitnessSolver : NraSolver {
    WitnessSolver() : NraSolver(createPolynomialKernel()) {}
    std::optional<TheoryCheckResult> witness(TheoryLemmaStorage& lemmas) {
        for (const auto& stage : reasoners_)
            if (stage->name() == "nra.subtropical")
                return stage->run(lemmas, TheoryEffort::Full);
        throw std::logic_error("NRA subtropical stage missing");
    }
};
}

TEST_CASE("NRA combination: model coincidence is not an implied equality") {
    NativeTerms terms;
    terms.registerSort(0, SortKind::Real);
    SharedTermRegistry shared;
    shared.setNativeTerms(&terms);
    WitnessSolver solver;
    solver.setNativeTerms(&terms);
    solver.setSharedTermRegistry(&shared);
    TheoryLemmaDatabase lemmas;
    auto& kernel = *solver.kernel();
    const auto x = kernel.mkVar(kernel.getOrCreateVar("x"));
    const auto expr = terms.add({Kind::Variable, 0, {}, Payload(std::string("x"))});
    const auto sx = shared.getOrCreate(expr, 0, "x", false);
    shared.addOwner(sx, TheoryId::NRA);
    shared.addOwner(sx, TheoryId::EUF);
    const TheoryAtomRecord premise{1, TheoryId::NRA, false, NullExpr,
        PolynomialAtomPayload{x, Relation::Gt, RealValue::fromInt(0)}};
    solver.assertLit(premise, true, 0, SatLit::positive(1));
    const auto result = solver.witness(lemmas);
    REQUIRE(result.has_value());
    REQUIRE(result->kind == TheoryCheckResult::Kind::Consistent);
    const auto model = solver.getModel();
    REQUIRE(model.has_value());
    REQUIRE(model->numericAssignments.count("x") == 1);
    const auto value = model->numericAssignments.at("x").tryAsRational();
    REQUIRE(value.has_value());
    REQUIRE(*value > 0);

    // The candidate makes x equal to this constant. A distinct positive x
    // still satisfies every premise, so that equality is not a theory fact.
    const auto numeral = value->get_str();
    const auto constant = terms.add({Kind::ConstReal, 0, {}, Payload(numeral)});
    const auto sc = shared.getOrCreate(constant, 0, numeral, false);
    shared.addOwner(sc, TheoryId::NRA);
    shared.addOwner(sc, TheoryId::EUF);
    const mpq_class alternative = *value + 1;
    REQUIRE(kernel.sgn(x, {{"x", alternative}}) > 0);
    REQUIRE(alternative != *value);
    CAPTURE(numeral);
    CAPTURE(alternative.get_str());

    for (const auto& propagation : solver.getDeducedSharedEqualities()) {
        CAPTURE(propagation.reasons.size());
        const bool isCoincidence = (propagation.a == sx && propagation.b == sc)
            || (propagation.a == sc && propagation.b == sx);
        // Even including all asserted reasons cannot justify this equality:
        // the alternative above satisfies the complete current assertion set.
        CHECK_FALSE(isCoincidence);
    }
}
