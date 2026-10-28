#include "algebra/poly/PolynomialKernel.h"
#include <doctest/doctest.h>
#include <algorithm>
#include <array>
#include <set>

using namespace xolver;

TEST_CASE("PolynomialKernel support: every coefficient subtree contributes dependencies") {
    std::array<std::string, 3> names{"x", "y", "z"};
    do {
        auto kernel = createPolynomialKernel();
        std::vector<PolyId> variables;
        for (const auto& name : names)
            variables.push_back(kernel->mkVar(kernel->getOrCreateVar(name)));
        const auto product = kernel->mul(kernel->mul(variables[0], variables[1]), variables[2]);
        const auto linear = kernel->add(kernel->add(variables[0], variables[1]), variables[2]);
        const auto expectedOrder = kernel->variables(linear);
        for (size_t factor = 0; factor < variables.size(); ++factor) {
            CAPTURE(names[0]);
            CAPTURE(names[1]);
            CAPTURE(names[2]);
            CAPTURE(factor);
            const auto polynomial = kernel->add(variables[factor], product);
            const auto support = kernel->variables(polynomial);
            CHECK(support == expectedOrder);
            CHECK(std::set<std::string>(support.begin(), support.end()) ==
                  std::set<std::string>{"x", "y", "z"});
            CHECK(kernel->variables(polynomial) == support);
            // Each reported dependency has an independent exact witness:
            // change only that variable while all other values stay fixed.
            for (const auto& name : names) {
                std::unordered_map<std::string, mpz_class> sample{{"x",1},{"y",1},{"z",1}};
                const auto one = kernel->evalInteger(polynomial, sample);
                sample[name] = 0;
                const auto zero = kernel->evalInteger(polynomial, sample);
                REQUIRE(one);
                REQUIRE(zero);
                CHECK(*one != *zero);
            }
        }
    } while (std::next_permutation(names.begin(), names.end()));
}

TEST_CASE("PolynomialKernel support: immutable caches survive registration and cancellation") {
    auto kernel = createPolynomialKernel();
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto w = kernel->mkVar(kernel->getOrCreateVar("w"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const auto product = kernel->mul(x, kernel->mul(y, z));
    const auto high = kernel->mul(kernel->mul(w, y), kernel->pow(z, 3));
    const auto polynomial = kernel->add(y, kernel->add(product, high));
    const auto support = kernel->variables(polynomial);
    CHECK(std::set<std::string>(support.begin(), support.end()) ==
          std::set<std::string>{"w", "x", "y", "z"});
    kernel->getOrCreateVar("unrelated");
    CHECK(kernel->variables(polynomial) == support);
    CHECK(kernel->variables(kernel->sub(polynomial, polynomial)).empty());
    CHECK(kernel->variables(kernel->mkConst(mpq_class(7, 3))).empty());
    CHECK(kernel->variables(y) == std::vector<std::string>{"y"});
    CHECK(kernel->variables(polynomial) == support);
}

TEST_CASE("PolynomialKernel support: sparse high-id atoms exclude the unrelated registry") {
    auto kernel = createPolynomialKernel();
    for (int i = 0; i < 5000; ++i)
        kernel->getOrCreateVar("unused_" + std::to_string(i));
    const auto x = kernel->mkVar(kernel->getOrCreateVar("x"));
    const auto y = kernel->mkVar(kernel->getOrCreateVar("y"));
    const auto z = kernel->mkVar(kernel->getOrCreateVar("z"));
    const auto polynomial = kernel->add(y, kernel->mul(z, kernel->mul(x, y)));
    const auto support = kernel->variables(polynomial);
    CHECK(std::set<std::string>(support.begin(), support.end()) ==
          std::set<std::string>{"x", "y", "z"});
    CHECK(kernel->variables(polynomial) == support);
}
