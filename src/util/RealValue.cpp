#include "util/RealValue.h"

#include <stdexcept>

// PHASE 0 SKELETON.  Every factory and operation throws; the accompanying
// tests (tests/unit/test_realvalue.cpp) are written against the intended
// semantics and are skipped by default (doctest::skip) so the shared `unit`
// ctest label stays green while a parallel agent works on `main`.  Run them
// explicitly with `nlcolver_unit_tests --no-skip -ts=realvalue` to see them
// fail as designed.  Phase 1 fills in these bodies (libpoly delegation for the
// algebraic case) and removes the skip decorator.

namespace nlcolver {

namespace {
[[noreturn]] void ni(const char* what) {
    throw std::logic_error(std::string("RealValue: not implemented: ") + what);
}
}  // namespace

// Default constructors are trivial (kept usable as members / variant default).
RealValue::RealValue() : storage_(mpq_class(0)) {}
ExtendedRealValue::ExtendedRealValue() : kind_(Kind::Finite), finite_() {}

// -- RealValue factories ----------------------------------------------------
RealValue RealValue::fromInt(int64_t)            { ni("fromInt"); }
RealValue RealValue::fromMpz(const mpz_class&)   { ni("fromMpz"); }
RealValue RealValue::fromMpq(mpq_class)          { ni("fromMpq"); }
RealValue RealValue::fromAlgebraic(AlgebraicNumber) { ni("fromAlgebraic"); }
RealValue RealValue::parse(std::string_view)     { ni("parse"); }

// -- RealValue kind / accessors ---------------------------------------------
RealValue::Kind RealValue::kind() const          { ni("kind"); }
bool RealValue::isRational() const               { ni("isRational"); }
bool RealValue::isAlgebraic() const              { ni("isAlgebraic"); }
const mpq_class& RealValue::asRational() const   { ni("asRational"); }
std::optional<mpq_class> RealValue::tryAsRational() const { ni("tryAsRational"); }
const AlgebraicNumber& RealValue::asAlgebraic() const { ni("asAlgebraic"); }

// -- RealValue arithmetic ----------------------------------------------------
RealValue RealValue::operator+(const RealValue&) const { ni("operator+"); }
RealValue RealValue::operator-(const RealValue&) const { ni("operator-"); }
RealValue RealValue::operator*(const RealValue&) const { ni("operator*"); }
RealValue RealValue::operator/(const RealValue&) const { ni("operator/"); }
RealValue RealValue::operator-() const                 { ni("operator-(unary)"); }

// -- RealValue comparison / predicates --------------------------------------
int RealValue::compare(const RealValue&) const   { ni("compare"); }
int RealValue::sign() const                      { ni("sign"); }
bool RealValue::isExactInteger() const           { ni("isExactInteger"); }
mpz_class RealValue::floor() const               { ni("floor"); }
mpz_class RealValue::ceil() const                { ni("ceil"); }

// -- RealValue serialization -------------------------------------------------
std::string RealValue::toSmtLib2() const         { ni("toSmtLib2"); }
std::string RealValue::toDebugString() const     { ni("toDebugString"); }

// -- ExtendedRealValue -------------------------------------------------------
ExtendedRealValue ExtendedRealValue::negInf()        { ni("ExtendedRealValue::negInf"); }
ExtendedRealValue ExtendedRealValue::posInf()        { ni("ExtendedRealValue::posInf"); }
ExtendedRealValue ExtendedRealValue::finite(RealValue) { ni("ExtendedRealValue::finite"); }
ExtendedRealValue::Kind ExtendedRealValue::kind() const { ni("ExtendedRealValue::kind"); }
bool ExtendedRealValue::isFinite() const             { ni("ExtendedRealValue::isFinite"); }
bool ExtendedRealValue::isNegInf() const             { ni("ExtendedRealValue::isNegInf"); }
bool ExtendedRealValue::isPosInf() const             { ni("ExtendedRealValue::isPosInf"); }
const RealValue& ExtendedRealValue::asFinite() const { ni("ExtendedRealValue::asFinite"); }
int ExtendedRealValue::compare(const ExtendedRealValue&) const { ni("ExtendedRealValue::compare"); }

} // namespace nlcolver
