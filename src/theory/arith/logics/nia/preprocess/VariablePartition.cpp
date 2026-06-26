#include "theory/arith/logics/nia/preprocess/VariablePartition.h"

#include <algorithm>

namespace xolver {

VariablePartition::VariablePartition(PolynomialKernel& kernel) : kernel_(kernel) {}

unsigned VariablePartition::bitsToCover(const mpz_class& lo, const mpz_class& hi) {
    // Signed two's-complement width w needs:
    //   -2^(w-1) <= lo  AND  hi <= 2^(w-1) - 1
    // i.e. max(|lo+1|, |hi|) needs ceil(log2) bits + 1 (sign).
    // Use mpz_sizeinbase which returns bits-needed-for-magnitude.
    mpz_class absLo = (lo < 0) ? -lo - 1 : mpz_class(0);
    mpz_class absHi = (hi >= 0) ? hi : mpz_class(0);
    size_t bitsLo = (absLo == 0) ? 0
                  : mpz_sizeinbase(absLo.get_mpz_t(), 2);
    size_t bitsHi = (absHi == 0) ? 0
                  : mpz_sizeinbase(absHi.get_mpz_t(), 2);
    size_t bits = std::max(bitsLo, bitsHi);
    // Add sign bit: width = bits + 1 (the sign).
    return static_cast<unsigned>(bits + 1);
}

bool VariablePartition::extractSingleVarBound(
    PolyId poly, std::string& var, int& coef, mpz_class& constTerm) const {
    auto termsOpt = kernel_.terms(poly);
    if (!termsOpt) return false;
    mpz_class accumConst = 0;
    std::string sv;
    mpz_class sc = 0;
    for (const auto& t : *termsOpt) {
        if (t.powers.empty()) { accumConst += t.coefficient; continue; }
        if (t.powers.size() != 1 || t.powers[0].second != 1) return false;
        std::string nm(kernel_.varName(t.powers[0].first));
        if (sv.empty()) { sv = nm; sc = t.coefficient; }
        else if (sv == nm) { sc += t.coefficient; }
        else return false;
    }
    if (sv.empty() || (sc != 1 && sc != -1)) return false;
    var = sv;
    coef = (sc == 1) ? 1 : -1;
    constTerm = accumConst;
    return true;
}

PartitionResult VariablePartition::partition(
    const std::vector<NormalizedNiaConstraint>& constraints,
    const DomainStore& domains,
    unsigned maxBitWidth) const {

    PartitionResult result;

    // 1. Collect every variable appearing in the constraint set.
    std::unordered_set<std::string> allVars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel_.variables(c.poly)) {
            allVars.insert(v);
        }
    }

    // 2. Seed with DomainStore bounds.
    for (const auto& v : allVars) {
        VarPartitionInfo info;
        const IntDomain* d = domains.getDomain(v);
        if (d) {
            if (d->hasLower) {
                info.hasLower = true;
                info.lower = d->lower.value;
            }
            if (d->hasUpper) {
                info.hasUpper = true;
                info.upper = d->upper.value;
            }
        }
        result.info[v] = info;
    }

    // 3. Augment with direct constraint scan: single-var bound atoms
    // `±x + c rel 0` translate to var bounds.
    for (const auto& c : constraints) {
        std::string var;
        int coef;
        mpz_class constTerm;
        if (!extractSingleVarBound(c.poly, var, coef, constTerm)) continue;
        if (!result.info.count(var)) continue;
        // Bound: coef*var + constTerm rel 0
        //   coef=1:  var + c rel 0  =>  var rel -c
        //   coef=-1: -var + c rel 0 => var rel c
        mpz_class threshold = (coef == 1) ? -constTerm : constTerm;
        auto& info = result.info[var];
        // For inequalities: Leq/Geq translate. Equality forces a tight bound.
        switch (c.rel) {
            case Relation::Eq:
                // var + c = 0 (coef=1): var = -c. Both bounds = -c.
                // var - c = 0 (coef=-1): var = c. Both bounds = c.
                if (!info.hasLower || threshold > info.lower) {
                    info.hasLower = true; info.lower = threshold;
                }
                if (!info.hasUpper || threshold < info.upper) {
                    info.hasUpper = true; info.upper = threshold;
                }
                break;
            case Relation::Leq:
                if (coef == 1) {
                    // var + c <= 0 => var <= -c (upper)
                    if (!info.hasUpper || threshold < info.upper) {
                        info.hasUpper = true; info.upper = threshold;
                    }
                } else {
                    // -var + c <= 0 => var >= c (lower)
                    if (!info.hasLower || threshold > info.lower) {
                        info.hasLower = true; info.lower = threshold;
                    }
                }
                break;
            case Relation::Geq:
                if (coef == 1) {
                    // var + c >= 0 => var >= -c (lower)
                    if (!info.hasLower || threshold > info.lower) {
                        info.hasLower = true; info.lower = threshold;
                    }
                } else {
                    // -var + c >= 0 => var <= c (upper)
                    if (!info.hasUpper || threshold < info.upper) {
                        info.hasUpper = true; info.upper = threshold;
                    }
                }
                break;
            default:
                // Lt/Gt/Neq: skip; HYB doesn't need strict here.
                break;
        }
    }

    // 4. Classify into B / U based on hasLower && hasUpper && bitWidth.
    for (auto& [v, info] : result.info) {
        if (info.hasLower && info.hasUpper) {
            info.bitWidth = bitsToCover(info.lower, info.upper);
            info.isBounded = (info.bitWidth <= maxBitWidth);
        } else {
            info.bitWidth = 0;
            info.isBounded = false;
        }
        if (info.isBounded) result.bounded.insert(v);
        else                result.unbounded.insert(v);
    }

    return result;
}

double PartitionResult::averageBitWidthBounded() const {
    if (bounded.empty()) return 0.0;
    unsigned sum = 0;
    for (const auto& v : bounded) {
        auto it = info.find(v);
        if (it != info.end()) sum += it->second.bitWidth;
    }
    return static_cast<double>(sum) / bounded.size();
}

unsigned PartitionResult::maxBitWidthBounded() const {
    unsigned mx = 0;
    for (const auto& v : bounded) {
        auto it = info.find(v);
        if (it != info.end()) mx = std::max(mx, it->second.bitWidth);
    }
    return mx;
}

} // namespace xolver
