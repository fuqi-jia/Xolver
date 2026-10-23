#include "quantifiers/bitvector/Circuit.h"
#include <algorithm>

namespace xolver::quantifiers::bitvector {
namespace {
void matching(const Word& a, const Word& b) {
    if (a.empty() || a.size() != b.size()) throw Unsupported("bit-vector width mismatch");
}
}
Word Circuit::constant(const mpz_class& value, std::size_t width) {
    if (!width) throw Unsupported("zero-width bit-vector");
    diagram.resources.tick(width);
    Word result(width);
    for (std::size_t i = 0; i < width; ++i) result[i] = mpz_tstbit(value.get_mpz_t(), i);
    return result;
}
Word Circuit::invert(Word value) {
    for (auto& bit : value) bit = diagram.negate(bit);
    return value;
}
Word Circuit::choose(Bit condition, const Word& yes, const Word& no) {
    matching(yes, no);
    Word result(yes.size());
    for (std::size_t i = 0; i < result.size(); ++i) result[i] = diagram.ite(condition, yes[i], no[i]);
    return result;
}
Word Circuit::add(const Word& a, const Word& b, Bit carry) {
    matching(a, b);
    Word result(a.size());
    for (std::size_t i = 0; i < a.size(); ++i) {
        const Bit sum = diagram.exclusiveOr(a[i], b[i]);
        result[i] = diagram.exclusiveOr(sum, carry);
        carry = diagram.disjunction(diagram.conjunction(a[i], b[i]), diagram.conjunction(sum, carry));
    }
    return result;
}
Word Circuit::negate(const Word& a) { return add(invert(a), constant(0, a.size()), 1); }
Word Circuit::multiply(const Word& a, const Word& b) {
    matching(a, b);
    Word result(a.size(), 0);
    for (std::size_t i = 0; i < b.size(); ++i) {
        Word row(a.size(), 0);
        for (std::size_t j = 0; j + i < a.size(); ++j)
            row[j + i] = diagram.conjunction(a[j], b[i]);
        result = add(result, row);
    }
    return result;
}
Bit Circuit::equal(const Word& a, const Word& b) {
    matching(a, b);
    Bit result = 1;
    for (std::size_t i = 0; i < a.size(); ++i)
        result = diagram.conjunction(result, diagram.negate(diagram.exclusiveOr(a[i], b[i])));
    return result;
}
Bit Circuit::less(const Word& a, const Word& b, bool signedComparison) {
    matching(a, b);
    Bit result = 0;
    for (std::size_t i = 0; i < a.size(); ++i)
        result = diagram.ite(diagram.exclusiveOr(a[i], b[i]), b[i], result);
    return signedComparison
        ? diagram.ite(diagram.exclusiveOr(a.back(), b.back()), a.back(), result) : result;
}
std::pair<Word, Word> Circuit::divide(const Word& a, const Word& b) {
    matching(a, b);
    Word quotient(a.size(), 0), remainder(a.size() + 1, 0), divisor = b;
    divisor.push_back(0);
    for (std::size_t i = a.size(); i-- > 0;) {
        for (std::size_t j = remainder.size() - 1; j > 0; --j) remainder[j] = remainder[j - 1];
        remainder[0] = a[i];
        quotient[i] = diagram.negate(less(remainder, divisor));
        remainder = choose(quotient[i], subtract(remainder, divisor), remainder);
    }
    remainder.pop_back();
    // A zero divisor yields an all-ones quotient and the original dividend.
    return {std::move(quotient), std::move(remainder)};
}
Word Circuit::shift(const Word& a, const Word& amount, bool left, bool arithmetic) {
    Word result = a;
    std::size_t distance = 1;
    const Bit fill = arithmetic && !left ? a.back() : 0;
    for (Bit bit : amount) {
        Word moved(a.size(), fill);
        if (distance < a.size()) {
            for (std::size_t i = 0; i < a.size(); ++i) {
                if (left && i >= distance) moved[i] = result[i - distance];
                if (!left && distance < a.size() - i) moved[i] = result[i + distance];
            }
        }
        result = choose(bit, moved, result);
        distance = distance >= a.size() - distance ? a.size() : distance * 2;
    }
    return result;
}
}
