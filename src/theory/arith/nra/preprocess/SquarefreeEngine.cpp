#include "theory/arith/nra/preprocess/SquarefreeEngine.h"
#include "theory/arith/nra/backend/LibpolyBackend.h"

namespace xolver {

SquarefreeEngine::SquarefreeEngine(LibpolyBackend& backend)
    : backend_(backend) {}

SquarefreeEngine::Result SquarefreeEngine::compute(UniPolyId f) {
    if (f == NullUniPolyId) {
        return {NullUniPolyId};
    }

    // Compute derivative f'
    // For coefficient vector [c0, c1, ..., cn] (high to low degree):
    // f' has coefficients [0, c0, 2*c1, ..., n*c_{n-1}] (dropped constant term)
    // Actually: if f = c0*x^n + c1*x^{n-1} + ... + cn,
    // then f' = n*c0*x^{n-1} + (n-1)*c1*x^{n-2} + ... + c_{n-1}
    // So f' coefficients are [n*c0, (n-1)*c1, ..., 1*c_{n-1}]

    const auto& coeffs = backend_.getUni(f);
    if (coeffs.size() <= 1) {
        // Constant polynomial: squarefree is itself (or 1 if zero)
        return {f};
    }

    std::vector<mpz_class> derivCoeffs;
    derivCoeffs.reserve(coeffs.size() - 1);
    int degree = static_cast<int>(coeffs.size()) - 1;
    for (int i = 0; i < degree; ++i) {
        mpz_class c = coeffs[i] * (degree - i);
        derivCoeffs.push_back(c);
    }

    // Remove leading zeros from derivative
    while (!derivCoeffs.empty() && derivCoeffs[0] == 0) {
        derivCoeffs.erase(derivCoeffs.begin());
    }

    if (derivCoeffs.empty()) {
        // f' = 0: f is constant, squarefree is f itself
        return {f};
    }

    UniPolyId df = backend_.allocUni(std::move(derivCoeffs));

    // Compute g = gcd(f, f')
    UniPolyId g = backend_.gcdUni(f, df);
    if (g == NullUniPolyId) {
        return {NullUniPolyId};
    }

    // Check if g is constant
    const auto& gCoeffs = backend_.getUni(g);
    bool gIsConstant = (gCoeffs.size() == 1 && gCoeffs[0] != 0);
    if (gIsConstant) {
        // f is already squarefree
        return {f};
    }

    // Compute squarefree = f / g
    UniPolyId squarefree = backend_.exactDivideUni(f, g);
    if (squarefree == NullUniPolyId) {
        return {NullUniPolyId};
    }

    return {squarefree};
}

} // namespace xolver
