#pragma once

#include <gmpxx.h>
#include <cstddef>
#include <functional>

namespace xolver {
namespace exact_hash_detail {

inline std::size_t integer(mpz_srcptr value) noexcept {
    const auto size = mpz_size(value);
    std::size_t hash = size;
    hash ^= std::size_t(mpz_sgn(value) < 0) + 0x9e3779b9u + (hash << 6) + (hash >> 2);
    for (std::size_t index = 0; index < size; ++index) {
        const auto limb = mpz_getlimbn(value, static_cast<mp_size_t>(index));
        hash ^= std::hash<mp_limb_t>{}(limb) + 0x9e3779b9u + (hash << 6) + (hash >> 2);
    }
    return hash;
}

} // namespace exact_hash_detail

// Read the exact GMP representation without decimal conversion or allocation.
// Rational keys follow GMP's canonical-form requirement, as does mpq equality.
// Hashes are process-local bucket selectors; callers still compare full values.
struct MpzHash {
    std::size_t operator()(const mpz_class& value) const noexcept {
        return exact_hash_detail::integer(value.get_mpz_t());
    }
};

struct MpqHash {
    std::size_t operator()(const mpq_class& value) const noexcept {
        std::size_t hash = exact_hash_detail::integer(value.get_num_mpz_t());
        hash ^= exact_hash_detail::integer(value.get_den_mpz_t()) +
            0x9e3779b9u + (hash << 6) + (hash >> 2);
        return hash;
    }
};

} // namespace xolver
