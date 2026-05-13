#pragma once

#include <cstdint>
#include <limits>

namespace nlcolver {

using ExprId  = uint32_t;
using SortId  = uint32_t;
using VarId   = uint32_t;
using AtomId  = uint32_t;
using PolyId  = uint32_t;
using SatVar  = uint32_t;
using ProofId = uint32_t;
using ClauseId = uint32_t;

constexpr ExprId  NullExpr  = std::numeric_limits<ExprId>::max();
constexpr SortId  NullSort  = std::numeric_limits<SortId>::max();
constexpr VarId   NullVar   = std::numeric_limits<VarId>::max();
constexpr AtomId  NullAtom  = std::numeric_limits<AtomId>::max();
constexpr PolyId  NullPoly  = std::numeric_limits<PolyId>::max();
constexpr ClauseId NullClause = std::numeric_limits<ClauseId>::max();

using ScopeLevel = uint32_t;
constexpr ScopeLevel ScopeRoot = 0;

enum class TheoryId : uint8_t {
    Bool, EUF, LRA, LIA, NRA, NIA, BV, FP, IDL, RDL, Custom
};

enum class Relation : uint8_t {
    Eq, Neq, Lt, Leq, Gt, Geq
};

} // namespace nlcolver
