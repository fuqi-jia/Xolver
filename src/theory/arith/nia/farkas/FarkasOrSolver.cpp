#include "theory/arith/nia/farkas/FarkasOrSolver.h"

#include <algorithm>
#include <functional>
#include <unordered_set>

namespace xolver::farkas {

// ---------------------------- buildTable -----------------------------------

SupportTable FarkasOrSolver::buildTable(
    const FarkasProfile& profile, std::size_t maxBProduct) const
{
    SupportTable t;
    if (!profile.good()) return t;

    // Canonical bounded-var order: sort by name for determinism.
    for (const auto& [v, lh] : profile.boundedGlobals) {
        t.boundedVarOrder.push_back(v);
    }
    std::sort(t.boundedVarOrder.begin(), t.boundedVarOrder.end());

    // Build initial finite domain per bounded var: every integer in [lo, hi].
    for (const auto& v : t.boundedVarOrder) {
        auto it = profile.boundedGlobals.find(v);
        const mpz_class& lo = it->second.first;
        const mpz_class& hi = it->second.second;
        std::vector<mpz_class> dom;
        for (mpz_class x = lo; x <= hi; ++x) dom.push_back(x);
        t.initialBDomain[v] = std::move(dom);
    }

    // CT vars.
    t.ctVars.assign(profile.unboundedCT.begin(), profile.unboundedCT.end());
    std::sort(t.ctVars.begin(), t.ctVars.end());

    // Compute cartesian-product size; bail if too large for P2a.
    std::size_t productSize = 1;
    for (const auto& v : t.boundedVarOrder) {
        productSize *= t.initialBDomain[v].size();
        if (productSize > maxBProduct) {
            return SupportTable{};   // signal: too large
        }
    }

    // Enumerate all B-tuples and call P1 for every (block, branch, B).
    std::vector<std::size_t> idx(t.boundedVarOrder.size(), 0);
    bool done = t.boundedVarOrder.empty();   // edge case: no bounded vars
    do {
        std::unordered_map<std::string, mpz_class> B;
        for (std::size_t i = 0; i < t.boundedVarOrder.size(); ++i) {
            const auto& v = t.boundedVarOrder[i];
            B[v] = t.initialBDomain[v][idx[i]];
        }
        for (std::size_t j = 0; j < profile.blocks.size(); ++j) {
            const auto& block = profile.blocks[j];
            for (std::size_t k = 0; k < block.branches.size(); ++k) {
                auto cands = p1_.solveBranch(block.branches[k], B, t.ctVars);
                if (cands.empty()) continue;
                // Keep the first candidate (lowest-support primitive ray).
                SupportRow row;
                row.blockIdx = (int)j;
                row.branchIdx = (int)k;
                for (const auto& [vn, val] : B) row.bTuple[vn] = val;
                row.candidate = cands.front();
                row.candidate.branchIndex = (int)k;
                t.byBlockBranch[{(int)j, (int)k}].push_back(t.rows.size());
                t.rows.push_back(std::move(row));
                ++t.feasibleTotal;
            }
        }
        // Increment idx odometer-style.
        if (done) break;
        if (t.boundedVarOrder.empty()) break;
        std::size_t pos = 0;
        while (pos < idx.size()) {
            ++idx[pos];
            if (idx[pos] < t.initialBDomain[t.boundedVarOrder[pos]].size()) break;
            idx[pos] = 0;
            ++pos;
        }
        if (pos == idx.size()) done = true;
    } while (!done);

    return t;
}

// ---------------------- intersectInterval helper ---------------------------

bool FarkasOrSolver::intersectInterval(
    std::pair<mpq_class, mpq_class>& cur, std::pair<bool, bool>& curFinite,
    const std::pair<mpq_class, mpq_class>& other,
    const std::pair<bool, bool>& otherFinite)
{
    // Lower bound: max of current and other.
    if (otherFinite.first) {
        if (!curFinite.first || other.first > cur.first) {
            cur.first = other.first;
            curFinite.first = true;
        }
    }
    // Upper bound: min of current and other.
    if (otherFinite.second) {
        if (!curFinite.second || other.second < cur.second) {
            cur.second = other.second;
            curFinite.second = true;
        }
    }
    // Empty check.
    if (curFinite.first && curFinite.second && cur.first > cur.second) {
        return false;
    }
    return true;
}

// ---------------------- solveCsp (backtrack + forward-check) ---------------

namespace {

// State carried through backtracking.
struct CspState {
    // Per-bounded-var current domain.
    std::map<std::string, std::vector<mpz_class>> bDom;
    // Per-block current branch domain.
    std::map<int, std::vector<int>> choiceDom;
    // CT interval per CT var.
    std::map<std::string, std::pair<mpq_class, mpq_class>> ctDom;
    std::map<std::string, std::pair<bool, bool>> ctFinite;
};

// For a SupportRow, can it survive given current bDom?  I.e., is its
// B-tuple compatible with the current domains for each bounded var?
bool rowSurvivesBDom(const SupportRow& row, const CspState& s) {
    for (const auto& [v, val] : row.bTuple) {
        auto dit = s.bDom.find(v);
        if (dit == s.bDom.end()) continue;
        if (std::find(dit->second.begin(), dit->second.end(), val)
            == dit->second.end()) {
            return false;
        }
    }
    return true;
}

// For a SupportRow, is its CT-bound compatible with the current ctDom?
// (Only checks single-interval ctBounds; multi-CT residuals are deferred
//  to P3 — for P2a, we assume single-CT-var ctBounds.)
bool rowCtCompatible(const SupportRow& row, const CspState& s) {
    for (const auto& bd : row.candidate.ctBounds) {
        if (!bd.hasInterval) continue;     // residual: P3 handles
        auto it = s.ctDom.find(bd.ctVar);
        if (it == s.ctDom.end()) continue;
        auto fit = s.ctFinite.find(bd.ctVar);
        std::pair<mpq_class, mpq_class> rowI{bd.ctLo, bd.ctHi};
        std::pair<bool, bool> rowF{bd.ctLoFinite, bd.ctHiFinite};
        std::pair<mpq_class, mpq_class> cur = it->second;
        std::pair<bool, bool> curF = fit->second;
        if (!FarkasOrSolver::intersectInterval(cur, curF, rowI, rowF)) {
            return false;
        }
    }
    return true;
}

} // namespace

std::optional<FarkasOrAssignment>
FarkasOrSolver::solveCsp(const SupportTable& table,
                         const FarkasProfile& profile) const
{
    if (table.rows.empty()) return std::nullopt;

    // Build the initial CspState.
    CspState init;
    for (const auto& [v, dom] : table.initialBDomain) init.bDom[v] = dom;
    for (std::size_t j = 0; j < profile.blocks.size(); ++j) {
        std::vector<int> branchIdx;
        for (std::size_t k = 0; k < profile.blocks[j].branches.size(); ++k) {
            branchIdx.push_back((int)k);
        }
        init.choiceDom[(int)j] = std::move(branchIdx);
    }
    for (const auto& v : table.ctVars) {
        init.ctDom[v] = {mpq_class(0), mpq_class(0)};
        init.ctFinite[v] = {false, false};        // unbounded both sides
    }

    // Forward-check: prune choices whose every support row is incompatible
    // with the current B / CT. Returns false on contradiction.
    auto forwardCheck = [&](CspState& s) -> bool {
        bool changed = true;
        while (changed) {
            changed = false;
            for (auto& [blockIdx, branches] : s.choiceDom) {
                std::vector<int> surviving;
                for (int k : branches) {
                    auto it = table.byBlockBranch.find({blockIdx, k});
                    if (it == table.byBlockBranch.end()) continue;
                    bool anySupport = false;
                    for (std::size_t rowIdx : it->second) {
                        const SupportRow& row = table.rows[rowIdx];
                        if (rowSurvivesBDom(row, s) && rowCtCompatible(row, s)) {
                            anySupport = true;
                            break;
                        }
                    }
                    if (anySupport) surviving.push_back(k);
                }
                if (surviving.size() != branches.size()) {
                    branches = std::move(surviving);
                    changed = true;
                }
                if (branches.empty()) return false;
            }
        }
        return true;
    };

    // Recursive backtracker.
    std::optional<FarkasOrAssignment> result;
    std::function<bool(CspState&, std::size_t)> rec;
    rec = [&](CspState& s, std::size_t depth) -> bool {
        if (!forwardCheck(s)) return false;

        // Choose the next unassigned variable: prefer choices with smallest
        // domain (most constrained first).
        int pickBlock = -1;
        std::size_t bestSize = SIZE_MAX;
        for (const auto& [j, doms] : s.choiceDom) {
            if (doms.size() == 1) continue;        // already fixed
            if (doms.size() < bestSize) { pickBlock = j; bestSize = doms.size(); }
        }

        if (pickBlock == -1) {
            // All choice blocks have unique branch. Now pick B if needed.
            std::string pickVar;
            std::size_t bestB = SIZE_MAX;
            for (const auto& [v, dom] : s.bDom) {
                if (dom.size() == 1) continue;
                if (dom.size() < bestB) { pickVar = v; bestB = dom.size(); }
            }
            if (pickVar.empty()) {
                // Full assignment! Emit.
                FarkasOrAssignment a;
                for (const auto& [v, dom] : s.bDom) a.B[v] = dom.front();
                for (const auto& [j, doms] : s.choiceDom) a.choice[j] = doms.front();
                // For each block's chosen branch, look up the support row
                // matching the chosen B and copy ray + lambdaNames.
                for (const auto& [j, k] : a.choice) {
                    auto it = table.byBlockBranch.find({j, k});
                    if (it == table.byBlockBranch.end()) return false;
                    for (std::size_t rowIdx : it->second) {
                        const SupportRow& row = table.rows[rowIdx];
                        bool matches = true;
                        for (const auto& [v, val] : row.bTuple) {
                            if (a.B[v] != val) { matches = false; break; }
                        }
                        if (matches) {
                            a.rayPerBlock[j] = row.candidate.lambdaRay;
                            a.lambdaNamesPerBlock[j] = row.candidate.lambdaNames;
                            // Intersect CT bounds.
                            for (const auto& bd : row.candidate.ctBounds) {
                                if (!bd.hasInterval) continue;
                                auto fit = s.ctFinite.find(bd.ctVar);
                                std::pair<mpq_class, mpq_class> rowI{bd.ctLo, bd.ctHi};
                                std::pair<bool, bool> rowF{bd.ctLoFinite, bd.ctHiFinite};
                                if (!intersectInterval(s.ctDom[bd.ctVar], fit->second,
                                                       rowI, rowF)) {
                                    return false;
                                }
                            }
                            break;
                        }
                    }
                }
                a.ctInterval = s.ctDom;
                a.ctFinite = s.ctFinite;
                result = std::move(a);
                return true;
            }
            // Branch on bounded var.
            auto values = s.bDom[pickVar];   // copy
            for (const auto& w : values) {
                CspState child = s;
                child.bDom[pickVar] = {w};
                if (rec(child, depth + 1)) return true;
            }
            return false;
        }

        // Branch on choice.
        auto branches = s.choiceDom[pickBlock];   // copy
        for (int k : branches) {
            CspState child = s;
            child.choiceDom[pickBlock] = {k};
            if (rec(child, depth + 1)) return true;
        }
        return false;
    };
    CspState s = init;
    rec(s, 0);
    return result;
}

} // namespace xolver::farkas
