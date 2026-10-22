#pragma once
#include "contracts/SeparationModel.h"
#include <memory>
#include <ostream>

namespace SOMTParser { class DAGNode; class Sort; }
namespace xolver::sl {
struct NativeDecision {
    Result result = Result::Unknown;
    std::string reason;
    std::shared_ptr<const Interpretation> model;
    uint64_t work = 0;
};
// Native SOMTParser DAG -> SL's typed formula, without NativeTerms/TermExpr.
// Int locations/data support PA terms and heap-independent quantified predicates.
// Spatial quantifiers use fair finite-heap PA compilation and polarity-aware
// instantiation. Unsupported domains/non-PA terms and exhausted resources
// return Unknown. Recursive predicates require a definition environment.
NativeDecision decideNative(
    const std::shared_ptr<SOMTParser::Sort>& location,
    const std::shared_ptr<SOMTParser::Sort>& data,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& assertions,
    const std::vector<std::shared_ptr<SOMTParser::DAGNode>>& declarations,
    Limits = {});
void dumpInterpretation(std::ostream&, const Interpretation&);
std::optional<std::string> nativeValue(
    const std::shared_ptr<SOMTParser::DAGNode>&, const Interpretation&, Limits = {});
} // namespace xolver::sl
