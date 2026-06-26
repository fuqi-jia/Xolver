#pragma once
// Detail helpers extracted from NiaSolver.cpp so the split NiaSolver_*.cpp
// translation units can share them. collectVars was a file-static free function;
// fnv1aMix / computeDispatchSignature lived in an anonymous namespace. All three
// are pure functions, so promoting them to inline header functions preserves
// behavior exactly — every call site resolves to the same unqualified xolver::
// name it did before the split.
#include <cstdint>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>
#include "theory/arith/nia/preprocess/NiaNormalizer.h"  // NormalizedNiaConstraint
#include "theory/arith/poly/PolynomialKernel.h"          // PolynomialKernel

namespace xolver {

// Union of variable names appearing across a set of normalized NIA constraints.
inline std::unordered_set<std::string> collectVars(
    const std::vector<NormalizedNiaConstraint>& constraints,
    PolynomialKernel& kernel) {
    std::unordered_set<std::string> vars;
    for (const auto& c : constraints) {
        for (const auto& v : kernel.variables(c.poly)) {
            vars.insert(v);
        }
    }
    return vars;
}

// FNV-1a mixing step used to fingerprint the dispatch-cache state.
inline uint64_t fnv1aMix(uint64_t h, uint64_t x) {
    h ^= x;
    h *= 1099511628211ull;
    return h;
}

// Hash of the relevant solver state (active size, sat trail, interface eq/diseq
// counts) used as the dispatch-cache key.
inline uint64_t computeDispatchSignature(
    size_t activeSize,
    const std::vector<std::pair<uint32_t, bool>>& satTrail,
    size_t ieCount, size_t idCount) {
    uint64_t h = 14695981039346656037ull;  // FNV offset basis
    h = fnv1aMix(h, activeSize);
    h = fnv1aMix(h, satTrail.size());
    for (const auto& p : satTrail) {
        h = fnv1aMix(h, static_cast<uint64_t>(p.first));
        h = fnv1aMix(h, p.second ? 1ull : 0ull);
    }
    h = fnv1aMix(h, ieCount);
    h = fnv1aMix(h, idCount);
    return h;
}

}  // namespace xolver
