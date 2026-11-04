#include <doctest/doctest.h>
#include "search/refute/PolynomialConeRefutation.h"
#include "base/SolveClock.h"
#include <algorithm>

using namespace xolver;
namespace {
auto until() { return std::chrono::steady_clock::now() + std::chrono::seconds(2); }
auto var(VarId id) { return RationalPolynomial::fromVar(id, 1, 1); }
auto num(const mpq_class& q) { return RationalPolynomial::fromConstant(q); }
using Rule = PolynomialConeStep::Rule;
PolynomialProof wire(const RationalPolynomial& poly) {
    PolynomialProof result;
    for (const auto& [word, coefficient] : poly.terms())
        result.emplace(ProofMonomial(word.begin(), word.end()), coefficient);
    return result;
}
PolynomialConePremise predicate(const RationalPolynomial& poly, Relation relation) {
    return {wire(poly), relation};
}
PolynomialConeStep premise(size_t index) {
    PolynomialConeStep step; step.rule = Rule::Premise; step.source = index; return step;
}
PolynomialConeStep square(const RationalPolynomial& poly) {
    PolynomialConeStep step; step.rule = Rule::Square; step.factor = wire(poly); return step;
}
std::vector<PolynomialConePremise> premises(const std::vector<SignRefuteConstraint>& source) {
    std::vector<PolynomialConePremise> result;
    for (const auto& row : source) result.push_back(predicate(row.poly, row.rel));
    return result;
}
}

TEST_CASE("Polynomial cone certificate: square identities exclude positive constants but retain zero") {
    const auto x = var(0);
    std::vector<PolynomialConePremise> source{predicate(x * x + num(1), Relation::Eq)};
    PolynomialConeCertificate proof{{PolynomialConeStep{}, premise(0), square(x)}, {1, -1, 1}};
    const auto checked = checkPolynomialConeCertificate(proof, source, {}, until());
    REQUIRE(checked);
    CHECK(*checked == std::vector<size_t>{0});
    source[0].poly = wire(x * x);
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {}, until()));
    proof.weights[0] = 0;
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {}, until()));
}

TEST_CASE("Polynomial cone certificate: product signs and equality multipliers are checked separately") {
    const auto x = var(0), y = var(1), z = var(2);
    std::vector<PolynomialConePremise> source{
        predicate(x - y, Relation::Geq), predicate(z, Relation::Geq),
        predicate(-x * z + y * z - num(1), Relation::Geq)};
    PolynomialConeStep product; product.rule = Rule::Product; product.left = 1; product.right = 2;
    PolynomialConeCertificate proof{
        {PolynomialConeStep{}, premise(0), premise(1), premise(2), product}, {1, 0, 0, 1, 1}};
    REQUIRE(checkPolynomialConeCertificate(proof, source, {}, until()));
    source[0].rel = Relation::Eq;
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {}, until()));

    source = {predicate(x - y, Relation::Eq), predicate(x * z - y * z - num(1), Relation::Geq)};
    PolynomialConeStep multiple; multiple.rule = Rule::EqualityMultiple; multiple.source = 0; multiple.factor = wire(z);
    proof = {{PolynomialConeStep{}, premise(1), multiple}, {1, 1, -1}};
    REQUIRE(checkPolynomialConeCertificate(proof, source, {}, until()));
    source[0].rel = Relation::Geq;
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {}, until()));
}

TEST_CASE("Polynomial cone certificate: integer gaps require typed variables and include offsets") {
    const auto x = var(0), y = var(1);
    PolynomialConeStep rounded; rounded.rule = Rule::IntegralGap; rounded.left = 0;
    PolynomialConeCertificate proof{{premise(0), rounded, premise(1)}, {0, 1, 1}};
    std::vector<PolynomialConePremise> source{predicate(x, Relation::Gt), predicate(num(1) - x, Relation::Gt)};
    REQUIRE(checkPolynomialConeCertificate(proof, source, {.allInteger = true}, until()));
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {}, until()));
    const std::vector<VarId> integers{0};
    REQUIRE(checkPolynomialConeCertificate(proof, source, {.integerVariables = integers}, until()));
    source = {predicate(x + num(mpq_class(1, 2)), Relation::Gt),
        predicate(num(mpq_class(1, 2)) - x, Relation::Gt)};
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {.allInteger = true}, until()));
    const auto polynomial = x * num(mpq_class(2, 3)) + y * num(mpq_class(4, 3));
    source = {predicate(polynomial, Relation::Gt), predicate(num(mpq_class(2, 3)) - polynomial, Relation::Gt)};
    REQUIRE(checkPolynomialConeCertificate(proof, source, {.allInteger = true}, until()));
    CHECK_FALSE(checkPolynomialConeCertificate(proof, source, {.integerVariables = integers}, until()));
}

TEST_CASE("Polynomial cone certificate: malformed and expired witnesses cannot become conflicts") {
    const auto x = var(0);
    const std::vector<PolynomialConePremise> source{predicate(x * x + num(1), Relation::Eq)};
    const PolynomialConeCertificate valid{{PolynomialConeStep{}, premise(0), square(x)}, {1, -1, 1}};
    auto broken = valid; broken.weights.pop_back();
    CHECK_FALSE(checkPolynomialConeCertificate(broken, source, {}, until()));
    broken = valid; broken.weights[2] = -1;
    CHECK_FALSE(checkPolynomialConeCertificate(broken, source, {}, until()));
    broken = valid; broken.steps[2].scale = -1;
    CHECK_FALSE(checkPolynomialConeCertificate(broken, source, {}, until()));
    broken = valid; broken.steps[1].source = 100;
    CHECK_FALSE(checkPolynomialConeCertificate(broken, source, {}, until()));
    broken = valid; broken.steps[2].rule = Rule::Product; broken.steps[2].left = 2;
    CHECK_FALSE(checkPolynomialConeCertificate(broken, source, {}, until()));
    CHECK_FALSE(checkPolynomialConeCertificate(valid, source, {}, std::chrono::steady_clock::now()));
}

TEST_CASE("Polynomial cone search: a helper deadline cannot extend the caller deadline") {
    const auto x = var(0);
    const std::vector<SignRefuteConstraint> source{
        {x, Relation::Gt, SatLit::positive(1)},
        {-x, Relation::Geq, SatLit::positive(2)}};
    PolynomialConeStatistics stats;
    PolynomialConeCertificate proof;
    wall::endSolve();
    {
        wall::DeadlineScope caller(std::chrono::steady_clock::now() - std::chrono::seconds(1));
        CHECK_FALSE(refuteByPolynomialCone(source, until(), {}, &stats, &proof));
        CHECK(stats.exhausted);
        CHECK_FALSE(stats.certified);
        CHECK(proof.steps.empty());
        CHECK(wall::remainingMs() == 0);
    }
    const auto conflict = refuteByPolynomialCone(source, until(), {}, &stats, &proof);
    REQUIRE(conflict);
    CHECK(stats.certified);
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    CHECK_FALSE(wall::hasDeadline());
}

TEST_CASE("Polynomial cone search: coupled products explain only current signed premises") {
    const auto x = var(0), y = var(1), z = var(2);
    std::vector<SignRefuteConstraint> source{
        {x - y, Relation::Geq, SatLit::negative(1)},
        {z, Relation::Geq, SatLit::positive(2)},
        {x * z - y * z + num(1), Relation::Leq, SatLit::negative(3)}};
    PolynomialConeStatistics stats;
    PolynomialConeCertificate proof;
    const auto conflict = refuteByPolynomialCone(source, until(), {}, &stats, &proof);
    REQUIRE(conflict);
    CHECK(stats.certified);
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    for (auto literal : *conflict)
        CHECK(std::any_of(source.begin(), source.end(), [&](const auto& row) { return row.reason == literal; }));
    const auto withdrawn = proof;
    source.erase(source.begin() + 1);
    CHECK_FALSE(checkPolynomialConeCertificate(withdrawn, premises(source), {}, until()));
    CHECK_FALSE(refuteByPolynomialCone(source, until(), {}, &stats, &proof));
    CHECK_FALSE(stats.certified);
    CHECK(proof.steps.empty());
    CHECK_FALSE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    source.insert(source.begin() + 1, {z, Relation::Geq, SatLit::positive(2)});
    for (VarId variable = 3; variable < 19; ++variable)
        source.push_back({var(variable), Relation::Geq, SatLit::positive(variable + 1)});
    REQUIRE(refuteByPolynomialCone(source, until(), {}, &stats, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    source[2].poly -= num(1); // x = y = z = 0 now satisfies every premise.
    CHECK_FALSE(refuteByPolynomialCone(source, until(), {}, &stats, &proof));
}

TEST_CASE("Polynomial cone search: affine equality products do not assume factor signs") {
    const auto x = var(0), y = var(1), z = var(2);
    const std::vector<SignRefuteConstraint> source{
        {x + y - num(1), Relation::Eq, SatLit::positive(1)},
        {x * z + y * z - z - num(1), Relation::Geq, SatLit::negative(2)}};
    PolynomialConeCertificate proof;
    REQUIRE(refuteByPolynomialCone(source, until(), {}, nullptr, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    const std::vector<SignRefuteConstraint> inconsistent{
        {x - y, Relation::Eq, SatLit::positive(1)},
        {x - y - num(1), Relation::Eq, SatLit::negative(2)}};
    REQUIRE(refuteByPolynomialCone(inconsistent, until(), {}, nullptr, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(inconsistent), {}, until()));
    const std::vector<SignRefuteConstraint> redundant{
        {x - y, Relation::Eq, SatLit::positive(1)},
        {y - x, Relation::Eq, SatLit::negative(2)},
        {x * z - y * z - num(1), Relation::Geq, SatLit::positive(3)}};
    REQUIRE(refuteByPolynomialCone(redundant, until(), {}, nullptr, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(redundant), {}, until()));
}

TEST_CASE("Polynomial cone search: real witnesses prevent integer or mixed-domain refutations") {
    const auto x = var(0), y = var(1);
    std::vector<SignRefuteConstraint> source{
        {x, Relation::Gt, SatLit::positive(1)}, {x - num(1), Relation::Lt, SatLit::positive(2)}};
    REQUIRE(refuteByPolynomialCone(source, until(), {.allInteger = true}));
    CHECK_FALSE(refuteByPolynomialCone(source, until()));
    const auto polynomial = x * num(mpq_class(2, 3)) + y * num(mpq_class(4, 3));
    source = {{polynomial, Relation::Gt, SatLit::positive(1)},
              {polynomial - num(mpq_class(2, 3)), Relation::Lt, SatLit::positive(2)}};
    REQUIRE(refuteByPolynomialCone(source, until(), {.allInteger = true}));
    const std::vector<VarId> integers{0};
    CHECK_FALSE(refuteByPolynomialCone(source, until(), {.integerVariables = integers}));
}

TEST_CASE("Polynomial cone search: squares preserve zeros and exhausted checks remain open") {
    const auto x = var(0), y = var(1);
    std::vector<SignRefuteConstraint> source{
        {(x - y) * (x - y) + num(1), Relation::Leq, SatLit::positive(1)}};
    PolynomialConeCertificate proof;
    REQUIRE(refuteByPolynomialCone(source, until(), {}, nullptr, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    source[0].poly -= num(1);
    source[0].rel = Relation::Eq;
    CHECK_FALSE(refuteByPolynomialCone(source, until(), {}, nullptr, &proof));
    PolynomialConeStatistics stats;
    CHECK_FALSE(refuteByPolynomialCone(source, std::chrono::steady_clock::now(), {}, &stats, &proof));
    CHECK(stats.exhausted);
    CHECK(proof.steps.empty());
}

TEST_CASE("Polynomial cone search: quotient bounds certify a quadratic ratio with exact rounding") {
    const auto a = var(0), q = var(1), n = var(2), x = var(3);
    const auto k = var(4), r = var(5), s = var(6), t = var(7);
    std::vector<SignRefuteConstraint> source;
    auto append = [&](RationalPolynomial poly, Relation relation) {
        source.push_back({std::move(poly), relation, SatLit::positive(static_cast<SatVar>(source.size() + 1))});
    };
    append(a - num(1), Relation::Geq);
    append(q - a, Relation::Geq);
    append(a * num(4) - q, Relation::Geq);
    append(s, Relation::Geq); append(num(1) - s, Relation::Geq);
    append(r, Relation::Geq);
    append(x - a * q - r, Relation::Eq);
    append(a + q - n * num(2) - s, Relation::Eq);
    append(t, Relation::Geq); append(num(9999) - t, Relation::Geq);
    append(x * num(15625) - k * num(10000) - t, Relation::Eq);
    append(n * n - k, Relation::Gt);
    PolynomialConeCertificate proof;
    PolynomialConeStatistics stats;
    REQUIRE(refuteByPolynomialCone(source, until(), {.allInteger = true}, &stats, &proof));
    REQUIRE(checkPolynomialConeCertificate(proof, premises(source), {.allInteger = true}, until()));
    CHECK_FALSE(checkPolynomialConeCertificate(proof, premises(source), {}, until()));
    const std::unordered_map<VarId, mpq_class> realPoint{
        {0, 1}, {1, 4}, {2, mpq_class(5, 2)}, {3, 4},
        {4, mpq_class(62499, 10000)}, {5, 0}, {6, 0}, {7, 1}};
    for (const auto& row : source) {
        const auto value = row.poly.evaluateRational(realPoint);
        if (row.rel == Relation::Eq) CHECK(value == 0);
        else if (row.rel == Relation::Gt) CHECK(value > 0);
        else CHECK(value >= 0);
    }
}
