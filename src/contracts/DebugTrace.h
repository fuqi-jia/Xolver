#pragma once
#include "base/RuntimeConfig.h"
#include "base/EnvParam.h"

#include "contracts/SatSolver.h"
#include <cstdlib>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace xolver {
namespace debug {

inline bool noDebugEnabled() {
    return xolver::config::read<xolver::config::ReadKind::Boolean>("XOLVER_NO_DEBUG");
}

inline std::string fmtLit(SatLit lit) {
    std::ostringstream os;
    os << (lit.sign ? "+" : "-") << "v" << lit.var;
    return os.str();
}

inline std::string fmtClause(const std::vector<SatLit>& lits) {
    std::ostringstream os;
    os << "{";
    for (size_t i = 0; i < lits.size(); ++i) {
        if (i) os << " ";
        os << fmtLit(lits[i]);
    }
    os << "}";
    return os.str();
}

} // namespace debug
} // namespace xolver

#define NO_DBG if (!xolver::debug::noDebugEnabled()) {} else std::cerr
