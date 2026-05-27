#include <doctest/doctest.h>
#include "theory/arith/poly/FlatMonomialMap.h"
#include "expr/types.h"
#include <gmpxx.h>
using namespace zolver;
using Key = FlatMonomialMap<mpq_class>::Key;   // SmallVector<pair<VarId,int>,4>

static Key k(std::initializer_list<std::pair<VarId,int>> xs){ Key key; for(auto&p:xs) key.push_back(p); return key; }

TEST_CASE("FMM: append + canonicalize merges duplicates, strips zero, sorts") {
    FlatMonomialMap<mpq_class> m;
    m.append(k({{VarId{2},1}}), mpq_class(1));
    m.append(k({{VarId{1},1}}), mpq_class(2));
    m.append(k({{VarId{2},1}}), mpq_class(-1));   // merges with first -> 0 -> stripped
    m.canonicalize();
    REQUIRE(m.size() == 1);                        // only var1 term survives
    CHECK(m.begin()->first == k({{VarId{1},1}}));
    CHECK(m.begin()->second == mpq_class(2));
}
TEST_CASE("FMM: operator[] insert-or-accumulate keeps canonical, find works") {
    FlatMonomialMap<mpq_class> m;
    m[k({{VarId{3},2}})] += mpq_class(5);
    m[k({{VarId{1},1}})] += mpq_class(7);
    m[k({{VarId{3},2}})] += mpq_class(1);          // accumulate
    CHECK(m.size() == 2);
    auto it = m.find(k({{VarId{3},2}}));
    REQUIRE(it != m.end());
    CHECK(it->second == mpq_class(6));
    CHECK(m.find(k({{VarId{9},1}})) == m.end());
    // sorted: var1 before var3
    CHECK(m.begin()->first == k({{VarId{1},1}}));
    CHECK(m.rbegin()->first == k({{VarId{3},2}}));
}
TEST_CASE("FMM: operator== is canonical equality; SmallVector ordering ops") {
    Key a = k({{VarId{1},1},{VarId{2},1}});
    Key b = k({{VarId{1},1},{VarId{2},1}});
    Key c = k({{VarId{1},2}});
    // Canonical order = lexicographic on (varId,exp) pairs (same as std::map<vector<...>>):
    // a=[(1,1),(2,1)] vs c=[(1,2)] -> compare (1,1)<(1,2) by exp -> a<c.
    CHECK(a == b); CHECK(!(a == c)); CHECK((a < c)); CHECK(!(c < a));   // exercises SmallVector ==,<
    FlatMonomialMap<mpq_class> m1, m2;
    m1[a] += 3; m2[b] += 3;
    CHECK(m1 == m2);
    m2[c] += 1; CHECK(!(m1 == m2));
}
TEST_CASE("FMM: move is cheap (moved-from empty), copy preserves") {
    FlatMonomialMap<mpq_class> m; m[k({{VarId{1},1}})] += 4;
    FlatMonomialMap<mpq_class> mv = std::move(m);
    CHECK(mv.size() == 1); CHECK(m.size() == 0);   // moved-from empty (vector move)
    FlatMonomialMap<mpq_class> cp = mv;
    CHECK(cp == mv);
}
