#include "theory/arith/nia/reasoners/SmallPrimeModular.h"

#include <map>
#include <vector>

namespace xolver::modular {
namespace {

// The prime schedule. Small primes catch the common modular obstructions; the
// caller caps how many are tried via numPrimes.
constexpr long PRIMES[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53};
constexpr int  NUM_PRIMES = static_cast<int>(sizeof(PRIMES) / sizeof(PRIMES[0]));

// Keep matrices bounded — equality subsystems are normally tiny; a runaway size
// bails to "no claim" (sound: we just don't refute).
constexpr int MAX_DIM = 512;

// gcd of two non-negative mpz.
mpz_class mgcd(const mpz_class& a, const mpz_class& b) {
    mpz_class g;
    mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
    return g;
}

// a mod p reduced into [0, p).
long modp(const mpz_class& a, long p) {
    long v = mpz_class(a % p).get_si();   // |a % p| < p, fits in long
    v %= p;
    if (v < 0) v += p;
    return v;
}

// Modular inverse of a (1 ≤ a < p) modulo prime p, via extended Euclid.
long invp(long a, long p) {
    long t = 0, newt = 1, r = p, newr = a;
    while (newr != 0) {
        long q = r / newr;
        long tmp = t - q * newt; t = newt; newt = tmp;
        tmp = r - q * newr;     r = newr; newr = tmp;
    }
    if (t < 0) t += p;
    return t;   // r == 1 since p is prime and a ≢ 0
}

// Gaussian elimination of the augmented matrix [A | b] over GF(p). Entries are kept
// reduced in [0, p) throughout (p ≤ 53 ⇒ products stay well within `long`). Returns
// true iff the system is INCONSISTENT mod p (an all-zero coefficient row with a
// nonzero right-hand side).
bool inconsistentModP(std::vector<std::vector<long>> aug, int nrows, int ncols, long p) {
    int pivot = 0;
    for (int col = 0; col < ncols && pivot < nrows; ++col) {
        int sel = -1;
        for (int r = pivot; r < nrows; ++r)
            if (aug[r][col] != 0) { sel = r; break; }
        if (sel < 0) continue;
        std::swap(aug[pivot], aug[sel]);
        const long ipv = invp(aug[pivot][col], p);
        for (int c = col; c <= ncols; ++c)
            aug[pivot][c] = (aug[pivot][c] * ipv) % p;
        for (int r = 0; r < nrows; ++r) {
            if (r == pivot) continue;
            const long f = aug[r][col];
            if (f == 0) continue;
            for (int c = col; c <= ncols; ++c)
                aug[r][c] = ((aug[r][c] - f * aug[pivot][c]) % p + p) % p;
        }
        ++pivot;
    }
    for (int r = 0; r < nrows; ++r) {
        bool allZero = true;
        for (int c = 0; c < ncols; ++c)
            if (aug[r][c] != 0) { allZero = false; break; }
        if (allZero && aug[r][ncols] != 0) return true;   // 0 = nonzero ⇒ inconsistent
    }
    return false;
}

}  // namespace

// A gcd-reduced equality row:  Σ coeffs[v]·x_v = rhs  (over Z).
struct Row {
    std::map<int, mpz_class> coeffs;   // primitive (content 1)
    mpz_class rhs;
};

Result decide(const std::vector<omega::Constraint>& cs, int numPrimes) {
    // Collect the equality rows, gcd-reducing each (content division is
    // solution-preserving over Z and a row whose coeff-gcd ∤ its rhs is alone
    // infeasible). Reducing first lets the prime schedule catch prime-POWER
    // obstructions like 4x=2 (the content 4 ∤ 2) that survive every prime mod.
    std::vector<Row> rows;
    std::map<int, int> colOf;
    for (const auto& c : cs) {
        if (c.rel != omega::Constraint::Eq) continue;   // only equalities reduce soundly mod p
        Row row;
        row.rhs = -c.constant;                          // Σ aᵢxᵢ = −constant
        mpz_class g = 0;
        for (const auto& [v, a] : c.coeffs) { row.coeffs[v] = a; g = mgcd(g, mpz_class(abs(a))); }
        if (g == 0) {                                   // no variables: 0 = rhs
            if (row.rhs != 0) return Result::Unsat;     // 0 = nonzero ⇒ infeasible
            continue;                                   // 0 = 0 ⇒ drop
        }
        if (row.rhs % g != 0) return Result::Unsat;     // coeff-gcd ∤ rhs ⇒ infeasible
        for (auto& [v, a] : row.coeffs) a /= g;         // make primitive
        row.rhs /= g;
        for (const auto& [v, a] : row.coeffs) {
            (void)a;
            if (!colOf.count(v)) colOf[v] = static_cast<int>(colOf.size());
        }
        rows.push_back(std::move(row));
    }
    const int nrows = static_cast<int>(rows.size());
    const int ncols = static_cast<int>(colOf.size());
    if (nrows == 0 || ncols == 0) return Result::SatOrUnknown;
    if (nrows > MAX_DIM || ncols > MAX_DIM) return Result::SatOrUnknown;   // bounded; no claim

    int primes = numPrimes < NUM_PRIMES ? numPrimes : NUM_PRIMES;
    if (primes <= 0) primes = NUM_PRIMES;

    for (int pi = 0; pi < primes; ++pi) {
        const long p = PRIMES[pi];
        // Augmented matrix [A | b] mod p: row Σ (aᵢ mod p) xᵢ = (rhs mod p).
        std::vector<std::vector<long>> aug(nrows, std::vector<long>(ncols + 1, 0));
        for (int r = 0; r < nrows; ++r) {
            for (const auto& [v, a] : rows[r].coeffs)
                aug[r][colOf[v]] = modp(a, p);
            aug[r][ncols] = modp(rows[r].rhs, p);
        }
        if (inconsistentModP(std::move(aug), nrows, ncols, p))
            return Result::Unsat;
    }
    return Result::SatOrUnknown;
}

}  // namespace xolver::modular
