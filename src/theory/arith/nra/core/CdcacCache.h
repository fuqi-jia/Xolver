#pragma once

#include "theory/arith/nra/core/CdcacTypes.h"
#include <memory>
#include <unordered_map>
#include <vector>

namespace zolver {

// ------------------------------------------------------------------
// V5: Cache keys
// ------------------------------------------------------------------

struct SignCacheKey {
    PolyId poly = NullPoly;
    std::vector<VarId> varOrder;
    SamplePoint prefixSample;
    ProjectionPolicyKind policy = ProjectionPolicyKind::CollinsConservative;

    bool operator==(const SignCacheKey& o) const;
};

struct CellCacheKey {
    Cell prefixCell;
    std::vector<PolyId> projectionBasis;
    std::vector<VarId> varOrder;
    ProjectionPolicyKind policy = ProjectionPolicyKind::CollinsConservative;
    std::vector<ProjectionObligationId> activeObligations;

    bool operator==(const CellCacheKey& o) const;
};

struct ActiveAtomFingerprint {
    AtomId atom = NullAtom;
    SatLit lit{0, true};
    bool polarity = true;
    NormalizedAtom normalized;
    int level = -1;
    bool usedAsEC = false;
    bool usedAsGuard = false;

    bool operator<(const ActiveAtomFingerprint& o) const;
    bool operator==(const ActiveAtomFingerprint& o) const;
};

struct CoveringCacheKey {
    CellCacheKey parentCell;
    std::vector<ActiveAtomFingerprint> activeAtoms;  // sorted, deduplicated

    bool operator==(const CoveringCacheKey& o) const;
};

// ------------------------------------------------------------------
// V5: Cache value types (move-only safe via shared_ptr)
// ------------------------------------------------------------------

using CellCertificateRef = std::shared_ptr<const CellCertificate>;
using CoveringCertificateRef = std::shared_ptr<const CoveringCertificate>;

// ------------------------------------------------------------------
// V5: CdcacCache — precise keys, move-only safe
// ------------------------------------------------------------------

class CdcacCache {
public:
    // --- signAt cache ---
    std::optional<Sign> getSign(const SignCacheKey& key) const;
    void setSign(const SignCacheKey& key, Sign sign);

    // --- root isolation cache ---
    std::optional<RootSet> getRoots(PolyId poly, const SamplePoint& prefix, VarId var) const;
    void setRoots(PolyId poly, const SamplePoint& prefix, VarId var, RootSet roots);

    // --- projection cache ---
    std::optional<PolicyProjectionResult> getProjection(
        const std::vector<PolyId>& polys,
        VarId eliminateVar,
        const Cell& baseCell,
        ProjectionPolicyKind policy) const;
    void setProjection(
        const std::vector<PolyId>& polys,
        VarId eliminateVar,
        const Cell& baseCell,
        ProjectionPolicyKind policy,
        PolicyProjectionResult result);

    // --- cell certificate cache ---
    std::optional<CellCertificateRef> getCellCert(const CellCacheKey& key) const;
    void setCellCert(const CellCacheKey& key, CellCertificateRef cert);

    // --- covering certificate cache ---
    std::optional<CoveringCertificateRef> getCoveringCert(const CoveringCacheKey& key) const;
    void setCoveringCert(const CoveringCacheKey& key, CoveringCertificateRef cert);

    // --- UNSAT core cache ---
    std::optional<std::vector<SatLit>> getUnsatCore(const std::vector<AtomId>& atoms) const;
    void setUnsatCore(const std::vector<AtomId>& atoms, std::vector<SatLit> core);

    // --- scope management ---
    void push();
    void pop(uint32_t n);
    void clear();

    // --- stats ---
    size_t totalEntries() const;

private:
    // V5: simple unordered_map caches. Future: more sophisticated eviction.
    std::unordered_map<uint64_t, Sign> signCache_;
    std::unordered_map<uint64_t, RootSet> rootCache_;
    std::unordered_map<uint64_t, PolicyProjectionResult> projectionCache_;
    std::unordered_map<uint64_t, CellCertificateRef> cellCertCache_;
    std::unordered_map<uint64_t, CoveringCertificateRef> coveringCertCache_;
    std::unordered_map<uint64_t, std::vector<SatLit>> unsatCoreCache_;

    // Scope stack: number of entries at each push
    std::vector<size_t> scopeStack_;

    // Hash helpers (FNV-1a style)
    static uint64_t hashKey(const SignCacheKey& key);
    static uint64_t hashKey(PolyId poly, const SamplePoint& prefix, VarId var);
    static uint64_t hashProjectionKey(const std::vector<PolyId>& polys, VarId eliminateVar,
                                       const Cell& baseCell, ProjectionPolicyKind policy);
    static uint64_t hashKey(const CellCacheKey& key);
    static uint64_t hashKey(const CoveringCacheKey& key);
    static uint64_t hashKey(const std::vector<AtomId>& atoms);
};

} // namespace zolver
