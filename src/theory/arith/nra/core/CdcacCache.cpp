#include "theory/arith/nra/core/CdcacCache.h"
#include <numeric>

namespace zolver {

// ============================================================================
// Key comparisons
// ============================================================================

bool SignCacheKey::operator==(const SignCacheKey& o) const {
    return poly == o.poly && varOrder == o.varOrder &&
           prefixSample.varOrder == o.prefixSample.varOrder && policy == o.policy;
}

bool CellCacheKey::operator==(const CellCacheKey& o) const {
    return prefixCell.var == o.prefixCell.var &&
           projectionBasis == o.projectionBasis &&
           varOrder == o.varOrder && policy == o.policy &&
           activeObligations == o.activeObligations;
}

bool ActiveAtomFingerprint::operator<(const ActiveAtomFingerprint& o) const {
    if (atom != o.atom) return atom < o.atom;
    if (lit.var != o.lit.var) return lit.var < o.lit.var;
    if (lit.sign != o.lit.sign) return lit.sign < o.lit.sign;
    return level < o.level;
}

bool ActiveAtomFingerprint::operator==(const ActiveAtomFingerprint& o) const {
    return atom == o.atom && lit.var == o.lit.var && lit.sign == o.lit.sign && polarity == o.polarity &&
           level == o.level && usedAsEC == o.usedAsEC && usedAsGuard == o.usedAsGuard;
}

bool CoveringCacheKey::operator==(const CoveringCacheKey& o) const {
    return parentCell == o.parentCell && activeAtoms == o.activeAtoms;
}

// ============================================================================
// Hash helpers (FNV-1a 64-bit)
// ============================================================================

static uint64_t fnv1a(uint64_t h, const void* data, size_t len) {
    const uint8_t* bytes = static_cast<const uint8_t*>(data);
    for (size_t i = 0; i < len; ++i) {
        h ^= bytes[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static uint64_t hashUint64(uint64_t h, uint64_t v) {
    return fnv1a(h, &v, sizeof(v));
}

uint64_t CdcacCache::hashKey(const SignCacheKey& key) {
    uint64_t h = 14695981039346656037ULL;
    h = hashUint64(h, static_cast<uint64_t>(key.poly));
    h = hashUint64(h, key.varOrder.size());
    for (auto v : key.varOrder) h = hashUint64(h, static_cast<uint64_t>(v));
    h = hashUint64(h, key.prefixSample.varOrder.size());
    h = hashUint64(h, static_cast<uint64_t>(key.policy));
    return h;
}

uint64_t CdcacCache::hashKey(PolyId poly, const SamplePoint& /*prefix*/, VarId var) {
    uint64_t h = 14695981039346656037ULL;
    h = hashUint64(h, static_cast<uint64_t>(poly));
    h = hashUint64(h, static_cast<uint64_t>(var));
    return h;
}

uint64_t CdcacCache::hashProjectionKey(const std::vector<PolyId>& polys, VarId eliminateVar,
                                       const Cell& baseCell, ProjectionPolicyKind policy) {
    uint64_t h = 14695981039346656037ULL;
    h = hashUint64(h, static_cast<uint64_t>(eliminateVar));
    h = hashUint64(h, static_cast<uint64_t>(baseCell.var));
    h = hashUint64(h, static_cast<uint64_t>(policy));
    for (auto p : polys) h = hashUint64(h, static_cast<uint64_t>(p));
    return h;
}

uint64_t CdcacCache::hashKey(const CellCacheKey& key) {
    uint64_t h = 14695981039346656037ULL;
    h = hashUint64(h, static_cast<uint64_t>(key.prefixCell.var));
    h = hashUint64(h, key.projectionBasis.size());
    for (auto p : key.projectionBasis) h = hashUint64(h, static_cast<uint64_t>(p));
    h = hashUint64(h, static_cast<uint64_t>(key.policy));
    return h;
}

uint64_t CdcacCache::hashKey(const CoveringCacheKey& key) {
    uint64_t h = hashKey(key.parentCell);
    h = hashUint64(h, key.activeAtoms.size());
    for (const auto& a : key.activeAtoms) {
        h = hashUint64(h, static_cast<uint64_t>(a.atom));
        h = hashUint64(h, static_cast<uint64_t>(a.lit.var));
        h = hashUint64(h, static_cast<uint64_t>(a.lit.sign));
    }
    return h;
}

uint64_t CdcacCache::hashKey(const std::vector<AtomId>& atoms) {
    uint64_t h = 14695981039346656037ULL;
    for (auto a : atoms) h = hashUint64(h, static_cast<uint64_t>(a));
    return h;
}

// ============================================================================
// CdcacCache implementation
// ============================================================================

std::optional<Sign> CdcacCache::getSign(const SignCacheKey& key) const {
    auto it = signCache_.find(hashKey(key));
    if (it != signCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setSign(const SignCacheKey& key, Sign sign) {
    signCache_[hashKey(key)] = sign;
}

std::optional<RootSet> CdcacCache::getRoots(PolyId poly, const SamplePoint& prefix, VarId var) const {
    auto it = rootCache_.find(hashKey(poly, prefix, var));
    if (it != rootCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setRoots(PolyId poly, const SamplePoint& prefix, VarId var, RootSet roots) {
    rootCache_[hashKey(poly, prefix, var)] = std::move(roots);
}

std::optional<PolicyProjectionResult> CdcacCache::getProjection(
    const std::vector<PolyId>& polys,
    VarId eliminateVar,
    const Cell& baseCell,
    ProjectionPolicyKind policy) const {
    auto it = projectionCache_.find(hashProjectionKey(polys, eliminateVar, baseCell, policy));
    if (it != projectionCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setProjection(
    const std::vector<PolyId>& polys,
    VarId eliminateVar,
    const Cell& baseCell,
    ProjectionPolicyKind policy,
    PolicyProjectionResult result) {
    projectionCache_[hashProjectionKey(polys, eliminateVar, baseCell, policy)] = std::move(result);
}

std::optional<CellCertificateRef> CdcacCache::getCellCert(const CellCacheKey& key) const {
    auto it = cellCertCache_.find(hashKey(key));
    if (it != cellCertCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setCellCert(const CellCacheKey& key, CellCertificateRef cert) {
    cellCertCache_[hashKey(key)] = std::move(cert);
}

std::optional<CoveringCertificateRef> CdcacCache::getCoveringCert(const CoveringCacheKey& key) const {
    auto it = coveringCertCache_.find(hashKey(key));
    if (it != coveringCertCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setCoveringCert(const CoveringCacheKey& key, CoveringCertificateRef cert) {
    coveringCertCache_[hashKey(key)] = std::move(cert);
}

std::optional<std::vector<SatLit>> CdcacCache::getUnsatCore(const std::vector<AtomId>& atoms) const {
    auto it = unsatCoreCache_.find(hashKey(atoms));
    if (it != unsatCoreCache_.end()) return it->second;
    return std::nullopt;
}

void CdcacCache::setUnsatCore(const std::vector<AtomId>& atoms, std::vector<SatLit> core) {
    unsatCoreCache_[hashKey(atoms)] = std::move(core);
}

// ============================================================================
// Scope management (V5 skeleton: push/pop clears cache)
// Full implementation would track entry lifetimes per scope.
// ============================================================================

void CdcacCache::push() {
    // V5 skeleton: clear all caches on push for soundness.
    // Full implementation would use scope-tagged entries.
    clear();
    scopeStack_.push_back(0);
}

void CdcacCache::pop(uint32_t n) {
    // V5 skeleton: clear all caches on pop for soundness.
    clear();
    for (uint32_t i = 0; i < n && !scopeStack_.empty(); ++i) {
        scopeStack_.pop_back();
    }
}

void CdcacCache::clear() {
    signCache_.clear();
    rootCache_.clear();
    projectionCache_.clear();
    cellCertCache_.clear();
    coveringCertCache_.clear();
    unsatCoreCache_.clear();
}

size_t CdcacCache::totalEntries() const {
    return signCache_.size() + rootCache_.size() + projectionCache_.size() +
           cellCertCache_.size() + coveringCertCache_.size() + unsatCoreCache_.size();
}

} // namespace zolver
