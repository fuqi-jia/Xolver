#pragma once

#include "expr/ir.h"
#include <string>

namespace xolver {

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir);

} // namespace xolver
