#include <doctest/doctest.h>
#include "base/GmpHash.h"
#include "contracts/LinearFormKey.h"
#include "search/linear/LinearAtomManager.h"
#include "search/linear/LinearSource.h"
#include "base/IncrementalContext.h"
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

TEST_CASE("shared linear sources: canonical definitions survive growth and owner replacement") {
    mpq_class coefficient((mpz_class(1) << 181) + 7, (mpz_class(1) << 139) + 3);
    coefficient.canonicalize();
    LinearFormKey input{{{"left;part", coefficient}, {"right:part", mpq_class(-5, 7)}}};
    const auto expected = input;
    const mpq_class rhs(11, 13);
    AffineFormDefinition retained;
    {
        GeneralSimplex simplex;
        LinearAtomManager manager;
        const auto aux = manager.getOrCreateAuxVar(simplex, input, rhs);
        retained = manager.auxForm(aux);
        REQUIRE(retained);
        input.terms.front().second = 99;
        auto copied = manager;
        CHECK(copied.auxForm(aux) == retained);
        CHECK_FALSE(manager.auxForm(-1));
        CHECK_FALSE(manager.auxForm(manager.findVarIndex("left;part")));
        for (int offset = 0; offset < 256; ++offset)
            manager.getOrCreateAuxVar(simplex, expected, mpq_class(offset));
        CHECK(manager.auxForm(aux) == retained);
        copied = LinearAtomManager{};
        manager = LinearAtomManager{};
        CHECK(retained->lhs == expected);
        CHECK(retained->rhs == rhs);
    }
    CHECK(retained->lhs == expected);
    CHECK(retained->rhs == rhs);
    std::unordered_map<AffineFormDefinition, int, AffineFormKeyHash, AffineFormKeyEqual> index;
    index.emplace(retained, 7);
    const auto found = index.find(AffineFormKeyView{expected, rhs});
    REQUIRE(found != index.end());
    CHECK(found->second == 7);
}

TEST_CASE("shared linear sources: snapshots share definitions and retain independent premises") {
    LinearAtomManager manager;
    GeneralSimplex simplex;
    const LinearFormKey lhs{{{"snapshot-x", 1}}};
    const auto aux = manager.getOrCreateAuxVar(simplex, lhs, 3);
    LinearSource root{0, SatLit::positive(1), 1, NullExpr, Relation::Geq,
                      true, aux, false, manager.auxForm(aux)};
    incremental::IndexedContext<LinearSource, LinearSource::Key> context;
    context.append(root);
    auto saved = context.snapshot();
    auto child = root;
    child.level = 2;
    child.value = false;
    child.lit = SatLit::negative(1);
    context.replace(0, child);
    CHECK(context[0].form == root.form);
    CHECK(context[0].lit == SatLit::negative(1));
    CHECK(root.lit == SatLit::positive(1));
    context.restore(std::move(saved));
    CHECK(context[0].level == 0);
    CHECK(context[0].value);
    CHECK(context[0].lit == SatLit::positive(1));
    TheoryAtomRecord record{1, TheoryId::LIA, false, NullExpr,
        LinearAtomPayload{lhs, Relation::Geq, RealValue::fromInt(3)}};
    const auto& payload = std::get<LinearAtomPayload>(record.payload);
    CHECK(context[0].matches(record, payload, payload.rhs.asRational(), true, 0, root.lit));
    CHECK_FALSE(context[0].matches(record, payload, mpq_class(4), true, 0, root.lit));
    CHECK_FALSE(context[0].matches(record, payload, mpq_class(3), true, 1, root.lit));
    manager = LinearAtomManager{};
    CHECK(context[0].lhs() == lhs);
    CHECK(context[0].rhs() == 3);
    CHECK(child.lit == SatLit::negative(1));
}
