#include "evidence/HeapCertificate.h"
#include <set>

namespace xolver::proof {

bool checkGroundSymbolicHeap(const FiniteHeap& model,
                             const std::vector<GroundPointsTo>& atoms,
                             HeapLocation nil) {
    if (model.count(nil) || model.size() != atoms.size()) return false;
    std::set<HeapLocation> footprint;
    for (const auto& atom : atoms) {
        if (atom.address == nil || !footprint.insert(atom.address).second) return false;
        auto cell = model.find(atom.address);
        if (cell == model.end() || cell->second != atom.record) return false;
    }
    return true;
}

bool checkHeapPartition(const FiniteHeap& whole,
                         const std::vector<FiniteHeap>& parts,
                         HeapLocation nil) {
    if (whole.count(nil)) return false;
    std::set<HeapLocation> footprint;
    for (const auto& part : parts) {
        for (const auto& [address, record] : part) {
            if (address == nil || !footprint.insert(address).second) return false;
            auto cell = whole.find(address);
            if (cell == whole.end() || cell->second != record) return false;
        }
    }
    return footprint.size() == whole.size();
}

} // namespace xolver::proof
