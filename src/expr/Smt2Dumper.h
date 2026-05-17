#pragma once

#include "expr/ir.h"
#include <string>

namespace nlcolver {

std::string dumpExprToSMT2(ExprId id, const CoreIr& ir);

} // namespace nlcolver
