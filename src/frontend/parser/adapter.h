#pragma once
#include "ir/NativeTerms.h"
#include <somtparser/frontend/parser.h>

namespace xolver {
// Parser entry point: retain native node handles and attach query assertions.
// Ground rewrite rules are optional; no ground rewriting crosses quantifiers.
class FrontendAdapter {
public:
    explicit FrontendAdapter(SOMTParser::Parser& parser) : parser_(parser) {}
    std::unique_ptr<NativeTerms> importProblem(bool rewriteGround = true);
    SortId getBoolSortId() const { return boolSortId_; }
private:
    SOMTParser::Parser& parser_;
    SortId boolSortId_ = NullSort;
};
} // namespace xolver
