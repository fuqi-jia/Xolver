#pragma once
#include "quantifiers/boolean/Diagram.h"
#include <gmpxx.h>
#include <utility>

namespace xolver::quantifiers::bitvector {
using Bit = boolean::Diagram::Id;
using Word = std::vector<Bit>; // Least significant bit first; fixed-width words.
class Circuit {
public:
    boolean::Diagram& diagram;
    explicit Circuit(boolean::Diagram& d) : diagram(d) {}
    Word constant(const mpz_class&, std::size_t width);
    Word invert(Word);
    Word choose(Bit, const Word&, const Word&);
    Word add(const Word&, const Word&, Bit carry = 0);
    Word negate(const Word&);
    Word subtract(const Word& a, const Word& b) { return add(a, invert(b), 1); }
    Word multiply(const Word&, const Word&);
    Bit equal(const Word&, const Word&);
    Bit less(const Word&, const Word&, bool signedComparison = false);
    std::pair<Word, Word> divide(const Word&, const Word&);
    Word shift(const Word&, const Word& amount, bool left, bool arithmetic);
};
}
