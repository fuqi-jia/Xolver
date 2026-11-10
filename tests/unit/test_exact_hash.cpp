#include <doctest/doctest.h>
#include "base/GmpHash.h"
#include "contracts/LinearFormKey.h"
#include "search/linear/LinearAtomManager.h"
#include <unordered_map>
#include <unordered_set>
#include <string_view>

using namespace xolver;

TEST_CASE("exact hashes: canonical rational keys survive independent construction and rehash") {
    std::unordered_map<mpq_class, int, MpqHash> values;
    for (int numerator = -12; numerator <= 12; ++numerator) {
        for (int denominator = 1; denominator <= 12; ++denominator) {
            mpq_class value(numerator, denominator);
            value.canonicalize();
            values.emplace(value, numerator == 0 ? 0 : numerator > 0 ? 1 : -1);
        }
    }
    values.rehash(values.bucket_count() * 2);
    for (int numerator = -12; numerator <= 12; ++numerator) {
        for (int denominator = 1; denominator <= 12; ++denominator) {
            mpq_class equivalent(mpz_class(-7 * numerator), mpz_class(-7 * denominator));
            equivalent.canonicalize();
            const auto found = values.find(equivalent);
            REQUIRE(found != values.end());
            CHECK(found->second == (numerator == 0 ? 0 : numerator > 0 ? 1 : -1));
        }
    }
}

TEST_CASE("exact hashes: wide integers include middle limbs and sign") {
    std::unordered_map<mpz_class, int, MpzHash> values;
    std::unordered_set<std::size_t> positiveHashes, negativeHashes;
    mpz_class edge = 1;
    edge <<= 4 * GMP_NUMB_BITS;
    edge += 1;
    for (int index = 0; index < 128; ++index) {
        mpz_class middle = index;
        middle <<= 2 * GMP_NUMB_BITS;
        const mpz_class value = edge + middle;
        values.emplace(value, index);
        values.emplace(-value, -index - 1);
        positiveHashes.insert(MpzHash{}(value));
        negativeHashes.insert(MpzHash{}(mpz_class(-value)));
    }
    // Leading/trailing-limb-only hashes collapse this whole family.
    CHECK(positiveHashes.size() > 100);
    CHECK(negativeHashes.size() > 100);
    values.rehash(values.bucket_count() * 2);
    for (int index = 0; index < 128; ++index) {
        mpz_class middle = index;
        middle <<= 2 * GMP_NUMB_BITS;
        const mpz_class value(edge + middle);
        CHECK(values.at(mpz_class(value.get_str())) == index);
        CHECK(values.at(mpz_class(mpz_class(-value).get_str())) == -index - 1);
    }
    CHECK(MpzHash{}(mpz_class(0)) == MpzHash{}(mpz_class("0")));
}

TEST_CASE("exact hashes: normalized linear forms reuse the same simplex coordinate") {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    mpq_class half(2, 4), third(-3, 9), rhs(6, 15);
    half.canonicalize();
    third.canonicalize();
    rhs.canonicalize();
    const LinearFormKey form{{{"x", half}, {"y", third}}};
    const int coordinate = manager.getOrCreateAuxVar(simplex, form, rhs);
    const auto variables = simplex.numVars();
    const LinearFormKey equivalent{{{"x", mpq_class(1, 2)}, {"y", mpq_class(-1, 3)}}};
    for (int repeat = 0; repeat < 32; ++repeat)
        CHECK(manager.getOrCreateAuxVar(simplex, equivalent, mpq_class(2, 5)) == coordinate);
    CHECK(simplex.numVars() == variables);
    CHECK(simplex.numRows() == 1);
}

TEST_CASE("exact projections: isolated forms preserve rational equations and scaling") {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    const LinearFormKey original{{{"a", mpq_class(-7, 3)}, {"b", mpq_class(11, 5)},
                                   {"c", mpq_class(13, 7)}}};
    mpz_class wide = 1;
    wide <<= 181;
    mpq_class rhs(wide + 1, mpz_class(17));
    rhs.canonicalize();
    const mpq_class scale(-5, 11);
    LinearFormKey scaled = original;
    for (auto& [name, coefficient] : scaled.terms) {
        (void)name;
        coefficient *= scale;
    }
    const int aux = manager.getOrCreateAuxVar(simplex, original, rhs);
    const int scaledAux = manager.getOrCreateAuxVar(simplex, scaled, mpq_class(rhs * scale));
    for (size_t target = 0; target < original.terms.size(); ++target) {
        const auto* isolated = manager.isolatedAuxForm(aux, target);
        const auto* equivalent = manager.isolatedAuxForm(scaledAux, target);
        REQUIRE(isolated != nullptr);
        REQUIRE(equivalent != nullptr);
        CHECK(isolated->form == equivalent->form);
        CHECK(isolated->orderingText == equivalent->orderingText);
        std::unordered_map<std::string, mpq_class> values{
            {"a", mpq_class(2, 9)}, {"b", mpq_class(-3, 11)}, {"c", mpq_class(5, 13)}};
        mpq_class projected = isolated->form.rhs;
        for (const auto& [name, coefficient] : isolated->form.lhs.terms)
            projected += coefficient * values.at(name);
        values.at(original.terms[target].first) = projected;
        mpq_class substituted;
        for (const auto& [name, coefficient] : original.terms)
            substituted += coefficient * values.at(name);
        CHECK(substituted == rhs);
    }
}

TEST_CASE("exact projections: borrowed grouping keys survive growth and text collisions") {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    const int firstAux = manager.getOrCreateAuxVar(simplex,
        LinearFormKey{{{"a", 1}, {"x", -1}, {"y", -1}}}, 0);
    const int secondAux = manager.getOrCreateAuxVar(simplex,
        LinearFormKey{{{"b", 1}, {"x:1;y", -1}}}, 0);
    const auto* first = manager.isolatedAuxForm(firstAux, 0);
    const auto* second = manager.isolatedAuxForm(secondAux, 0);
    REQUIRE(first != nullptr);
    REQUIRE(second != nullptr);
    CHECK(first->orderingText == second->orderingText);
    CHECK_FALSE(first->form == second->form);
    const std::string_view firstText = first->orderingText;
    std::unordered_map<AffineFormKeyView, int, AffineFormKeyHash, AffineFormKeyEqual> groups;
    groups.emplace(AffineFormKeyView{first->form.lhs, first->form.rhs}, 1);
    groups.emplace(AffineFormKeyView{second->form.lhs, second->form.rhs}, 2);
    LinearFormKey dense;
    for (int i = 0; i < 64; ++i)
        dense.terms.emplace_back("d" + std::to_string(100 + i), mpq_class(i + 1));
    const int denseAux = manager.getOrCreateAuxVar(simplex, dense, 3);
    const auto* denseFirst = manager.isolatedAuxForm(denseAux, 0);
    REQUIRE(denseFirst != nullptr);
    const auto denseForm = denseFirst->form;
    for (size_t i = 1; i < dense.terms.size(); ++i)
        REQUIRE(manager.isolatedAuxForm(denseAux, i) != nullptr);
    for (int i = 0; i < 256; ++i) {
        const int aux = manager.getOrCreateAuxVar(simplex,
            LinearFormKey{{{"u", 1}, {"v", mpq_class(-i - 1)}}}, mpq_class(i));
        REQUIRE(manager.isolatedAuxForm(aux, 0) != nullptr);
    }
    CHECK(manager.isolatedAuxForm(firstAux, 0) == first);
    CHECK(manager.isolatedAuxForm(secondAux, 0) == second);
    CHECK(manager.isolatedAuxForm(denseAux, 0) == denseFirst);
    CHECK(denseFirst->form == denseForm);
    CHECK(firstText == first->orderingText);
    CHECK(firstText == "0|x:1;y:1;");
    CHECK(groups.size() == 2);
    CHECK(groups.at(AffineFormKeyView{first->form.lhs, first->form.rhs}) == 1);
    CHECK(groups.at(AffineFormKeyView{second->form.lhs, second->form.rhs}) == 2);
}

TEST_CASE("exact projections: invalid requests and changing bounds preserve pure definitions") {
    GeneralSimplex simplex;
    LinearAtomManager manager;
    const int x = manager.getOrCreateVar(simplex, "x");
    const int aux = manager.getOrCreateAuxVar(simplex, LinearFormKey{{{"x", 2}, {"y", -3}}}, 7);
    const int zero = manager.getOrCreateAuxVar(simplex,
        LinearFormKey{{{"unused", 0}, {"x", 1}}}, 0);
    const int variables = simplex.numVars(), rows = simplex.numRows();
    CHECK(manager.isolatedAuxForm(-1, 0) == nullptr);
    CHECK(manager.isolatedAuxForm(x, 0) == nullptr);
    CHECK(manager.isolatedAuxForm(aux, 2) == nullptr);
    CHECK(manager.isolatedAuxForm(zero, 0) == nullptr);
    const auto* projected = manager.isolatedAuxForm(aux, 0);
    REQUIRE(projected != nullptr);
    const auto form = projected->form;
    CHECK(simplex.assertLower(x, BoundInfo(BoundValue(DeltaRational(5)), SatLit::positive(1))));
    CHECK(simplex.assertUpper(x, BoundInfo(BoundValue(DeltaRational(9)), SatLit::positive(2))));
    CHECK(manager.isolatedAuxForm(aux, 0) == projected);
    CHECK(projected->form == form);
    CHECK(simplex.numVars() == variables);
    CHECK(simplex.numRows() == rows);
}
