#include "util/RealValue.h"
#include "util/RealAlgebraicOps.h"

#include <cctype>
#include <sstream>
#include <stdexcept>

namespace nlcolver {

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------
RealValue::RealValue() : storage_(mpq_class(0)) {}

RealValue RealValue::fromInt(int64_t v) {
    RealValue r;
    r.storage_ = mpq_class(static_cast<long>(v));
    return r;
}
RealValue RealValue::fromMpz(const mpz_class& v) {
    RealValue r;
    r.storage_ = mpq_class(v);
    return r;
}
RealValue RealValue::fromMpq(mpq_class q) {
    q.canonicalize();
    RealValue r;
    r.storage_ = std::move(q);
    return r;
}
RealValue RealValue::fromAlgebraic(AlgebraicNumber a) {
    RealValue r;
    r.storage_ = std::move(a);
    return r;
}

// ---------------------------------------------------------------------------
// Parse — canonical SMT-LIB integer/rational literal.
//   "3" | "n/d" | "(/ n d)" | "(- X)"
// ---------------------------------------------------------------------------
namespace {

std::string trim(std::string_view sv) {
    size_t a = 0, b = sv.size();
    while (a < b && std::isspace(static_cast<unsigned char>(sv[a]))) ++a;
    while (b > a && std::isspace(static_cast<unsigned char>(sv[b - 1]))) --b;
    return std::string(sv.substr(a, b - a));
}

mpz_class parseInt(const std::string& s) {
    try {
        return mpz_class(s);
    } catch (...) {
        throw std::invalid_argument("RealValue::parse: bad integer '" + s + "'");
    }
}

mpq_class parseMpq(const std::string& in) {
    std::string s = trim(in);
    if (s.empty()) throw std::invalid_argument("RealValue::parse: empty");

    if (s.front() == '(' && s.back() == ')') {
        std::string inner = trim(s.substr(1, s.size() - 2));
        if (!inner.empty() && inner.front() == '-') {
            mpq_class v = parseMpq(trim(inner.substr(1)));
            return -v;
        }
        if (!inner.empty() && inner.front() == '/') {
            std::string rest = trim(inner.substr(1));
            size_t sp = rest.find(' ');
            if (sp == std::string::npos) throw std::invalid_argument("RealValue::parse: bad (/ a b)");
            mpz_class num = parseInt(trim(rest.substr(0, sp)));
            mpz_class den = parseInt(trim(rest.substr(sp + 1)));
            mpq_class q(num, den);
            q.canonicalize();
            return q;
        }
        throw std::invalid_argument("RealValue::parse: unsupported s-expr '" + s + "'");
    }
    // plain "n" or "n/d"
    size_t slash = s.find('/');
    if (slash != std::string::npos) {
        mpz_class num = parseInt(trim(s.substr(0, slash)));
        mpz_class den = parseInt(trim(s.substr(slash + 1)));
        mpq_class q(num, den);
        q.canonicalize();
        return q;
    }
    return mpq_class(parseInt(s));
}

}  // namespace

RealValue RealValue::parse(std::string_view s) {
    return RealValue::fromMpq(parseMpq(std::string(s)));
}

// ---------------------------------------------------------------------------
// Kind / accessors
// ---------------------------------------------------------------------------
RealValue::Kind RealValue::kind() const {
    return storage_.index() == 0 ? Kind::Rational : Kind::Algebraic;
}
bool RealValue::isRational() const { return storage_.index() == 0; }
bool RealValue::isAlgebraic() const { return storage_.index() == 1; }

const mpq_class& RealValue::asRational() const {
    return std::get<mpq_class>(storage_);  // throws std::bad_variant_access if not rational
}
std::optional<mpq_class> RealValue::tryAsRational() const {
    if (isRational()) return std::get<mpq_class>(storage_);
    return std::nullopt;
}
const AlgebraicNumber& RealValue::asAlgebraic() const {
    return std::get<AlgebraicNumber>(storage_);
}

// ---------------------------------------------------------------------------
// Arithmetic — pure-GMP fast path when both operands are rational.
// ---------------------------------------------------------------------------
RealValue RealValue::operator+(const RealValue& o) const {
    if (isRational() && o.isRational()) return fromMpq(asRational() + o.asRational());
    return realalg::add(*this, o);
}
RealValue RealValue::operator-(const RealValue& o) const {
    if (isRational() && o.isRational()) return fromMpq(asRational() - o.asRational());
    return realalg::sub(*this, o);
}
RealValue RealValue::operator*(const RealValue& o) const {
    if (isRational() && o.isRational()) return fromMpq(asRational() * o.asRational());
    return realalg::mul(*this, o);
}
RealValue RealValue::operator/(const RealValue& o) const {
    if (isRational() && o.isRational()) {
        if (o.asRational() == 0) throw std::domain_error("RealValue: division by zero");
        return fromMpq(asRational() / o.asRational());
    }
    return realalg::div(*this, o);
}
RealValue RealValue::operator-() const {
    if (isRational()) return fromMpq(-asRational());
    return realalg::neg(*this);
}

// ---------------------------------------------------------------------------
// Comparison / sign
// ---------------------------------------------------------------------------
int RealValue::compare(const RealValue& o) const {
    if (isRational() && o.isRational()) {
        const mpq_class& a = asRational();
        const mpq_class& b = o.asRational();
        return (a < b) ? -1 : (a > b) ? 1 : 0;
    }
    return realalg::compare(*this, o);
}
int RealValue::sign() const {
    if (isRational()) {
        const mpq_class& a = asRational();
        return (a > 0) ? 1 : (a < 0) ? -1 : 0;
    }
    return realalg::sign(*this);
}

// ---------------------------------------------------------------------------
// Integer predicates
// ---------------------------------------------------------------------------
bool RealValue::isExactInteger() const {
    if (isRational()) return asRational().get_den() == 1;
    return realalg::isExactInteger(*this);
}
mpz_class RealValue::floor() const {
    if (isRational()) {
        const mpq_class& q = asRational();
        mpz_class r;
        mpz_fdiv_q(r.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
        return r;
    }
    return realalg::floorOf(*this);
}
mpz_class RealValue::ceil() const {
    if (isRational()) {
        const mpq_class& q = asRational();
        mpz_class r;
        mpz_cdiv_q(r.get_mpz_t(), q.get_num().get_mpz_t(), q.get_den().get_mpz_t());
        return r;
    }
    return realalg::ceilOf(*this);
}

// ---------------------------------------------------------------------------
// Serialization
// ---------------------------------------------------------------------------
namespace {
std::string rationalToSmtLib2(const mpq_class& q) {
    if (q.get_den() == 1) {
        if (q < 0) return "(- " + mpz_class(-q.get_num()).get_str() + ")";
        return q.get_num().get_str();
    }
    if (q < 0) {
        return "(- (/ " + mpz_class(-q.get_num()).get_str() + " " + q.get_den().get_str() + "))";
    }
    return "(/ " + q.get_num().get_str() + " " + q.get_den().get_str() + ")";
}
}  // namespace

std::string RealValue::toSmtLib2() const {
    if (isRational()) return rationalToSmtLib2(asRational());
    // Default (non --algebraic-model) mode: rational midpoint approximation of
    // the isolation interval.  (Exact (root-obj ...) output is a later mode.)
    const AlgebraicNumber& a = asAlgebraic();
    mpq_class mid = (a.lower + a.upper) / 2;
    mid.canonicalize();
    return rationalToSmtLib2(mid);
}

std::string RealValue::toDebugString() const {
    if (isRational()) {
        return std::string("Rational(") + asRational().get_str() + ")";
    }
    const AlgebraicNumber& a = asAlgebraic();
    std::ostringstream os;
    os << "Algebraic(poly[";
    for (size_t i = 0; i < a.coefficients.size(); ++i) {
        if (i) os << ",";
        os << a.coefficients[i].get_str();
    }
    os << "], in " << (a.lowerOpen ? "(" : "[") << a.lower.get_str() << ", "
       << a.upper.get_str() << (a.upperOpen ? ")" : "]") << ")";
    return os.str();
}

// ---------------------------------------------------------------------------
// ExtendedRealValue
// ---------------------------------------------------------------------------
ExtendedRealValue::ExtendedRealValue() : kind_(Kind::Finite), finite_() {}

ExtendedRealValue ExtendedRealValue::negInf() {
    ExtendedRealValue e;
    e.kind_ = Kind::NegInf;
    return e;
}
ExtendedRealValue ExtendedRealValue::posInf() {
    ExtendedRealValue e;
    e.kind_ = Kind::PosInf;
    return e;
}
ExtendedRealValue ExtendedRealValue::finite(RealValue v) {
    ExtendedRealValue e;
    e.kind_ = Kind::Finite;
    e.finite_ = std::move(v);
    return e;
}

ExtendedRealValue::Kind ExtendedRealValue::kind() const { return kind_; }
bool ExtendedRealValue::isFinite() const { return kind_ == Kind::Finite; }
bool ExtendedRealValue::isNegInf() const { return kind_ == Kind::NegInf; }
bool ExtendedRealValue::isPosInf() const { return kind_ == Kind::PosInf; }
const RealValue& ExtendedRealValue::asFinite() const { return finite_; }

int ExtendedRealValue::compare(const ExtendedRealValue& o) const {
    // -Inf < Finite < +Inf; finites compare by RealValue::compare.
    auto rank = [](Kind k) { return k == Kind::NegInf ? -1 : (k == Kind::PosInf ? 1 : 0); };
    int ra = rank(kind_), rb = rank(o.kind_);
    if (ra != rb) return ra < rb ? -1 : 1;
    if (kind_ != Kind::Finite) return 0;  // both same infinity
    return finite_.compare(o.finite_);
}

} // namespace nlcolver
