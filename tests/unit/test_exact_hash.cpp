#include <doctest/doctest.h>
#include "base/GmpHash.h"
#include "contracts/LinearFormKey.h"
#include "search/linear/LinearAtomManager.h"
#include <unordered_map>
#include <unordered_set>

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
