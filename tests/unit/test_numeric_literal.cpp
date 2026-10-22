#include <doctest/doctest.h>
#include "ir/NumericLiteral.h"
#include <limits>

using namespace xolver;

TEST_CASE("numeric IR decoding shares exact Int and Real semantics") {
    NativeTerms ir;
    TermExpr e;
    e.kind = Kind::ConstInt;
    e.payload = Payload{std::numeric_limits<int64_t>::min()};
    REQUIRE(numericLiteral(e));
    CHECK(*numericLiteral(e) == mpq_class("-9223372036854775808"));
    e.payload = Payload{std::string("123456789012345678901234567890")};
    REQUIRE(numericLiteral(e));
    CHECK(*numericLiteral(e) == mpq_class("123456789012345678901234567890"));
    e.payload = Payload{std::string("1/2")};
    CHECK_FALSE(numericLiteral(e));
    e.kind = Kind::ConstReal;
    REQUIRE(numericLiteral(e));
    CHECK(*numericLiteral(e) == mpq_class(1, 2));
    e.payload = Payload{std::string("-1.25e2")};
    CHECK(*numericLiteral(e) == -125);
    for (auto text : {"1/0", "not-a-number", "1.2.3", "", "1/2/3"}) {
        e.payload = Payload{std::string(text)};
        CHECK_FALSE(numericLiteral(e));
    }
    CHECK_FALSE(numericLiteral(ir, NullExpr));
}
