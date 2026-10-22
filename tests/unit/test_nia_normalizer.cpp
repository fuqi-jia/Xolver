#include <doctest/doctest.h>
#include "search/nia/preprocess/NiaNormalizer.h"
#include <unordered_map>

using namespace xolver;

namespace {
bool holds(Relation relation, const mpz_class& value) {
    switch (relation) {
        case Relation::Eq: return value == 0;
        case Relation::Neq: return value != 0;
        case Relation::Leq: return value <= 0;
        case Relation::Geq: return value >= 0;
        case Relation::Lt: return value < 0;
        case Relation::Gt: return value > 0;
    }
    return false;
}
}

TEST_CASE("NiaNormalizer: integer truth and literal reasons survive normalization") {
    auto kernel = createPolynomialKernel();
    NiaNormalizer normalizer(*kernel);
    auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    std::vector<PolyId> polynomials{
        kernel->mkConst(-1), kernel->mkZero(), kernel->mkOne(), x,
        kernel->add(kernel->mul(x, x), y),
        kernel->sub(kernel->mul(x, y), kernel->mkConst(3))};
    SatVar id = 0;
    for (auto poly : polynomials) {
        for (auto relation : {Relation::Eq, Relation::Neq, Relation::Leq,
                              Relation::Geq, Relation::Lt, Relation::Gt}) {
            ++id;
            const SatLit reason{id, id % 2 == 0};
            const auto result = normalizer.normalizeOne({poly, relation, reason});
            CHECK(result.reason == reason);
            CHECK(result.rel != Relation::Lt);
            CHECK(result.rel != Relation::Gt);
            for (int a = -3; a <= 3; ++a) {
                for (int b = -3; b <= 3; ++b) {
                    CAPTURE(id); CAPTURE(a); CAPTURE(b);
                    std::unordered_map<std::string, mpz_class> model{{"x", a}, {"y", b}};
                    auto before = kernel->evalInteger(poly, model);
                    auto after = kernel->evalInteger(result.poly, model);
                    REQUIRE(before.has_value());
                    REQUIRE(after.has_value());
                    CHECK(holds(relation, *before) == holds(result.rel, *after));
                }
            }
        }
    }
}
