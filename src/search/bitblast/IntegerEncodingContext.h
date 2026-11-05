#pragma once

#include "search/bitblast/BitBlastEncoder.h"
#include <memory>
#include <string>
#include <unordered_map>

namespace xolver::bitblast {

// One integer query owns one SAT instance and its literal-keyed gate cache.
// Widening preserves low bits and adds independent high bits. Signed arithmetic
// and source predicates must be rebuilt for the new interpretation; activate
// those predicates with assumptions, never permanent width-dependent clauses.
class IntegerEncodingContext {
public:
    IntegerEncodingContext(std::unique_ptr<SatSolver> solver, uint64_t variableBudget);

    SatSolver& solver() { return *solver_; }
    BitBlastEncoder& encoder() { return encoder_; }
    std::unordered_map<std::string, BitVec>& variables() { return variables_; }
    BitVec& widen(const std::string& name, unsigned width);

private:
    std::unique_ptr<SatSolver> solver_;
    BitBlastEncoder encoder_;
    std::unordered_map<std::string, BitVec> variables_;
};

} // namespace xolver::bitblast
