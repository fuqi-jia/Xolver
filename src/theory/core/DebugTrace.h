#pragma once

#include "sat/SatSolver.h"
#include <cstdlib>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace nlcolver {
namespace debug {

inline bool noDebugEnabled() {
    const char* v = std::getenv("NLCOLVER_NO_DEBUG");
    return v && std::string(v) != "0";
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
} // namespace nlcolver

#define NO_DBG if (!nlcolver::debug::noDebugEnabled()) {} else std::cerr
