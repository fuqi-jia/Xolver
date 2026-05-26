#pragma once

#include "expr/ir.h"
#include <string>

namespace zolver {

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir);

} // namespace zolver
