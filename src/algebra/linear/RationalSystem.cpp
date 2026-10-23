#include "algebra/linear/RationalSystem.h"
#include <stdexcept>
namespace xolver::linear {
Solution solve(std::vector<std::vector<mpq_class>> rows,std::vector<mpq_class> rhs,std::size_t columns,WorkBudget& budget) {
    if(rows.size()!=rhs.size())throw std::invalid_argument("linear system row mismatch");
    for(auto& row:rows){if(row.size()!=columns)throw std::invalid_argument("linear system column mismatch");for(auto& v:row){if(v.get_den()==0)throw std::invalid_argument("zero rational denominator");v.canonicalize();}}
    for(auto& v:rhs){if(v.get_den()==0)throw std::invalid_argument("zero rational denominator");v.canonicalize();}
    std::vector<std::size_t> pivots;std::size_t next=0;
    for(std::size_t col=0;col<columns && next<rows.size();++col) {
        std::size_t pivot=next;while(pivot<rows.size() && rows[pivot][col]==0){budget.tick();++pivot;}
        if(pivot==rows.size())continue;
        std::swap(rows[pivot],rows[next]);std::swap(rhs[pivot],rhs[next]);
        const auto factor=rows[next][col];
        for(std::size_t j=col;j<columns;++j){budget.tick();rows[next][j]/=factor;}rhs[next]/=factor;
        for(std::size_t i=0;i<rows.size();++i)if(i!=next && rows[i][col]!=0) {
            const auto q=rows[i][col];
            for(std::size_t j=col;j<columns;++j){budget.tick();rows[i][j]-=q*rows[next][j];}rhs[i]-=q*rhs[next];
        }
        pivots.push_back(col);++next;
    }
    Solution out;out.rank=pivots.size();out.values.resize(columns);
    for(std::size_t i=next;i<rows.size();++i)if(rhs[i]!=0)return out;
    out.consistent=true;for(std::size_t i=0;i<pivots.size();++i)out.values[pivots[i]]=rhs[i];return out;
}
}
