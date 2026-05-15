#pragma once
#include "expr/types.h"
#include "sat/SatSolver.h"
#include "theory/TheorySolver.h"
#include "theory/combination/ExplainableRollbackUnionFind.h"
#include <vector>
#include <optional>
#include <unordered_set>

namespace nlcolver {

struct SharedEqualitySnapshot {
    size_t ufTrailSize = 0;
    size_t diseqSize = 0;
};

class SharedEqualityManager {
public:
    SharedEqualityManager() = default;

    void assertEquality(SharedTermId a, SharedTermId b, SatLit reasonLit);
    void assertDisequality(SharedTermId a, SharedTermId b, SatLit reasonLit);

    bool same(SharedTermId a, SharedTermId b) const;
    bool diseqKnown(SharedTermId a, SharedTermId b) const;

    std::optional<TheoryConflict> checkDisequalityConflict() const;

    std::vector<SatLit> explainEquality(SharedTermId a, SharedTermId b) const;
    std::vector<SatLit> explainDisequality(SharedTermId a, SharedTermId b) const;

    SharedEqualitySnapshot snapshot() const;
    void rollback(SharedEqualitySnapshot snap);

    void clear();

private:
    ExplainableRollbackUnionFind<SatLit> uf_;

    struct DisequalityEntry {
        SharedTermId a;
        SharedTermId b;
        SatLit reasonLit;
    };
    std::vector<DisequalityEntry> disequalities_;

    static uint64_t pairKey(SharedTermId a, SharedTermId b);
};

} // namespace nlcolver
