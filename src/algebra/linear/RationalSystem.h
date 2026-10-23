#pragma once
#include "base/WorkBudget.h"
#include <gmpxx.h>
#include <vector>
namespace xolver::linear {
struct Solution {bool consistent=false;std::size_t rank=0;std::vector<mpq_class> values;};
// Exact rectangular Gaussian elimination. Free coordinates of the returned
// particular solution are zero. Rank distinguishes uniqueness from consistency.
Solution solve(std::vector<std::vector<mpq_class>>,std::vector<mpq_class>,std::size_t columns,WorkBudget&);
}
