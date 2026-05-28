#pragma once

#include <string>
#include <ostream>

namespace xolver {

enum class Result {
    Sat,
    Unsat,
    Unknown,
};

inline const char* toString(Result r) {
    switch (r) {
        case Result::Sat:     return "sat";
        case Result::Unsat:   return "unsat";
        case Result::Unknown: return "unknown";
    }
    return "unknown";
}

inline std::ostream& operator<<(std::ostream& os, Result r) {
    return os << toString(r);
}

} // namespace xolver
