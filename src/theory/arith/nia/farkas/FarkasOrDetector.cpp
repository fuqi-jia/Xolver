#include "theory/arith/nia/farkas/FarkasOrDetector.h"

#include <functional>
#include <sstream>
#include <unordered_set>

namespace xolver::farkas {

namespace {

// True if the expression is a numeric zero (any int / rational form).
bool exprIsZero(const CoreIr& ir, ExprId id) {
    const auto& e = ir.get(id);
    if (e.kind == Kind::ConstInt) {
        if (auto* i = std::get_if<int64_t>(&e.payload.value)) return *i == 0;
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            return *s == "0" || *s == "0/1";
        }
    }
    if (e.kind == Kind::ConstReal) {
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            return *s == "0" || *s == "0/1";
        }
    }
    return false;
}

} // namespace

std::optional<std::string> FarkasOrDetector::asVarName(ExprId id) const {
    const auto& e = ir_.get(id);
    if (e.kind != Kind::Variable) return std::nullopt;
    if (auto* s = std::get_if<std::string>(&e.payload.value)) return *s;
    return std::nullopt;
}

std::optional<mpz_class> FarkasOrDetector::asIntConst(ExprId id) const {
    const auto& e = ir_.get(id);
    if (e.kind == Kind::ConstInt || e.kind == Kind::ConstReal) {
        // Frontend lifts QF_NIA integer literals to ConstReal; we accept both
        // when the value is integer-valued (no "/" denominator).
        if (auto* i = std::get_if<int64_t>(&e.payload.value)) {
            return mpz_class(static_cast<long>(*i));
        }
        if (auto* s = std::get_if<std::string>(&e.payload.value)) {
            // Reject only true fractions (e.g. "1/3"); "5" or "-3" are integer.
            if (s->find('/') != std::string::npos) {
                // Try to parse as rational and check denominator == 1.
                try {
                    mpq_class q(*s);
                    if (q.get_den() == 1) return q.get_num();
                } catch (...) {}
                return std::nullopt;
            }
            try { return mpz_class(*s); } catch (...) { return std::nullopt; }
        }
    }
    // Neg(c) → -c
    if (e.kind == Kind::Neg && e.children.size() == 1) {
        if (auto inner = asIntConst(e.children[0])) {
            return -(*inner);
        }
    }
    return std::nullopt;
}

bool FarkasOrDetector::isZeroConst(ExprId id) const {
    return exprIsZero(ir_, id);
}

std::optional<std::string>
FarkasOrDetector::extractLambdaVar(ExprId atomId) const {
    const auto& e = ir_.get(atomId);
    if (e.children.size() != 2) return std::nullopt;
    // Accept any of the canonical "v >= 0" forms after frontend normalization:
    //   Geq(v, 0)        original SMT-LIB shape
    //   Leq(0, v)        flip-encoding (common in Stroeder/VeryMax IR)
    //   Gt(v, -1)        strict-int rewrite to non-strict (rare)
    if (e.kind == Kind::Geq) {
        auto v = asVarName(e.children[0]);
        if (v && isZeroConst(e.children[1])) return v;
    } else if (e.kind == Kind::Leq) {
        auto v = asVarName(e.children[1]);
        if (v && isZeroConst(e.children[0])) return v;
    }
    return std::nullopt;
}

// Walk a polynomial expression tree and check that every leaf monomial fits
// the Farkas template: constant, c·λ_j (degree 1 in λ), or c·λ_j·v_k
// (bilinear λ × non-λ). Add/Sub/Neg are treated transparently as monomial
// distributors; any nested polynomial sub-expression is flattened by
// recursion. Mul is the only operator that consumes a degree-counting
// argument.
bool FarkasOrDetector::monomialsLinearInLambda(
    ExprId polyId,
    const std::vector<std::string>& lambdas) const
{
    std::unordered_set<std::string> lset(lambdas.begin(), lambdas.end());

    // monomialOk: this expr is a single monomial of acceptable shape.
    // Mul children may themselves be Neg/Const/Variable but NOT Add/Sub
    // (a Mul with Add child would be a polynomial-times-polynomial, which
    // is not a single monomial — those go through the polyWalk path).
    std::function<bool(ExprId)> monomialOk;
    // polyWalk: this expr is a polynomial; iterate its monomial summands.
    std::function<bool(ExprId)> polyWalk;

    monomialOk = [&](ExprId id) -> bool {
        const auto& e = ir_.get(id);
        switch (e.kind) {
            case Kind::ConstInt:
            case Kind::ConstReal:
                return true;
            case Kind::Variable:
                return asVarName(id).has_value();
            case Kind::Neg:
                if (e.children.size() != 1) return false;
                return monomialOk(e.children[0]);
            case Kind::Mul: {
                int lDeg = 0, nDeg = 0;
                for (ExprId c : e.children) {
                    const auto& ce = ir_.get(c);
                    if (ce.kind == Kind::ConstInt || ce.kind == Kind::ConstReal) continue;
                    if (ce.kind == Kind::Neg && ce.children.size() == 1) {
                        // Recurse on the negated operand (degree-counted).
                        const auto& ne = ir_.get(ce.children[0]);
                        if (ne.kind == Kind::Variable) {
                            auto vn = asVarName(ce.children[0]);
                            if (!vn) return false;
                            if (lset.count(*vn)) ++lDeg; else ++nDeg;
                            continue;
                        }
                        if (ne.kind == Kind::ConstInt || ne.kind == Kind::ConstReal) continue;
                        return false;
                    }
                    if (ce.kind == Kind::Variable) {
                        auto vn = asVarName(c);
                        if (!vn) return false;
                        if (lset.count(*vn)) ++lDeg; else ++nDeg;
                        continue;
                    }
                    // Mul has a non-monomial child (Add/Sub/...) — reject.
                    return false;
                }
                return lDeg <= 1 && nDeg <= 1;
            }
            default:
                return false;
        }
    };

    polyWalk = [&](ExprId id) -> bool {
        const auto& e = ir_.get(id);
        if (e.kind == Kind::Add) {
            for (ExprId c : e.children) {
                if (!polyWalk(c)) return false;
            }
            return true;
        }
        if (e.kind == Kind::Sub) {
            // Sub(a, b, ...) = a + (-b) + (-c) ... each summand is a sub-poly.
            for (ExprId c : e.children) {
                if (!polyWalk(c)) return false;
            }
            return true;
        }
        if (e.kind == Kind::Neg) {
            // Neg(p) where p might itself be a polynomial.
            if (e.children.size() != 1) return false;
            return polyWalk(e.children[0]);
        }
        // Otherwise treat as single monomial.
        return monomialOk(id);
    };

    return polyWalk(polyId);
}

bool FarkasOrDetector::isLinearInLambdaEquality(
    ExprId atomId, const std::vector<std::string>& lambdas) const
{
    const auto& e = ir_.get(atomId);
    if (e.kind != Kind::Eq) return false;
    if (e.children.size() != 2) return false;
    // Expect `(= poly 0)` form (post-normalization). Both children handled.
    bool rhsZero = isZeroConst(e.children[1]);
    bool lhsZero = isZeroConst(e.children[0]);
    if (!rhsZero && !lhsZero) return false;
    ExprId poly = rhsZero ? e.children[0] : e.children[1];
    return monomialsLinearInLambda(poly, lambdas);
}

bool FarkasOrDetector::isLinearInLambdaInequality(
    ExprId atomId, const std::vector<std::string>& lambdas) const
{
    const auto& e = ir_.get(atomId);
    if (e.kind != Kind::Geq && e.kind != Kind::Leq
        && e.kind != Kind::Gt   && e.kind != Kind::Lt) return false;
    if (e.children.size() != 2) return false;
    // Same shape as equality — one side must be 0 OR a small constant.
    auto rhs = asIntConst(e.children[1]);
    auto lhs = asIntConst(e.children[0]);
    if (!rhs && !lhs) return false;
    ExprId poly = rhs ? e.children[0] : e.children[1];
    return monomialsLinearInLambda(poly, lambdas);
}

FarkasBranch FarkasOrDetector::classifyAnd(ExprId andId) const {
    FarkasBranch br;
    br.originalAnd = andId;
    const auto& e = ir_.get(andId);
    if (e.kind != Kind::And) {
        // Single-atom "branch" — treat as malformed for Farkas purposes.
        br.unclassified.push_back(andId);
        return br;
    }

    // Flatten nested Ands: Stroeder VeryMax encodes some Or-branches as
    // `(and (and a b) (and c d) ...)`. Walk all nested And children and
    // collect atoms into a single flat list.
    std::vector<ExprId> flat;
    std::function<void(ExprId)> collect;
    collect = [&](ExprId aid) {
        const auto& ne = ir_.get(aid);
        if (ne.kind == Kind::And) {
            for (ExprId c : ne.children) collect(c);
        } else {
            flat.push_back(aid);
        }
    };
    collect(andId);

    // First pass: collect λ vars from Geq(v, 0) atoms.
    for (ExprId c : flat) {
        if (auto vn = extractLambdaVar(c)) {
            br.lambdas.push_back(*vn);
        }
    }

    // Deduplicate lambdas in stable order.
    {
        std::unordered_set<std::string> seen;
        std::vector<std::string> kept;
        kept.reserve(br.lambdas.size());
        for (const auto& l : br.lambdas) {
            if (seen.insert(l).second) kept.push_back(l);
        }
        br.lambdas = std::move(kept);
    }

    // Second pass: classify remaining atoms (use the flat list).
    for (ExprId c : flat) {
        if (extractLambdaVar(c)) continue;       // already accounted for
        if (isLinearInLambdaEquality(c, br.lambdas)) {
            br.equalities.push_back(c);
        } else if (isLinearInLambdaInequality(c, br.lambdas)) {
            br.inequalities.push_back(c);
        } else {
            br.unclassified.push_back(c);
        }
    }
    return br;
}

std::optional<FarkasOrBlock>
FarkasOrDetector::tryClassifyOr(ExprId orId) const {
    const auto& e = ir_.get(orId);
    if (e.kind != Kind::Or) return std::nullopt;
    if (e.children.empty()) return std::nullopt;

    FarkasOrBlock block;
    block.originalOr = orId;
    block.branches.reserve(e.children.size());
    for (ExprId c : e.children) {
        block.branches.push_back(classifyAnd(c));
    }
    // Reject if any branch is not Farkas-shaped (Phase 0 conservative gate).
    if (!block.allBranchesFarkas()) return std::nullopt;
    return block;
}

bool FarkasOrDetector::extractBoundsFromAnd(ExprId andId,
                                            FarkasProfile& p) const {
    const auto& e = ir_.get(andId);
    if (e.kind != Kind::And) return false;
    bool any = false;
    // Collect per-var pending (lo, hi).
    std::unordered_map<std::string, std::pair<std::optional<mpz_class>,
                                              std::optional<mpz_class>>> pending;

    auto addLower = [&](const std::string& v, const mpz_class& lo) {
        auto& [pl, ph] = pending[v];
        if (!pl || lo > *pl) pl = lo;
    };
    auto addUpper = [&](const std::string& v, const mpz_class& hi) {
        auto& [pl, ph] = pending[v];
        if (!ph || hi < *ph) ph = hi;
    };

    for (ExprId c : e.children) {
        const auto& ce = ir_.get(c);
        if (ce.children.size() != 2) continue;
        auto lhsName = asVarName(ce.children[0]);
        auto rhsName = asVarName(ce.children[1]);
        auto lhsConst = asIntConst(ce.children[0]);
        auto rhsConst = asIntConst(ce.children[1]);

        // `(<= v K)` or `(<= K v)` etc. → upper / lower bound.
        if (ce.kind == Kind::Leq) {
            if (lhsName && rhsConst) { addUpper(*lhsName, *rhsConst); any = true; }
            else if (lhsConst && rhsName) { addLower(*rhsName, *lhsConst); any = true; }
        } else if (ce.kind == Kind::Geq) {
            if (lhsName && rhsConst) { addLower(*lhsName, *rhsConst); any = true; }
            else if (lhsConst && rhsName) { addUpper(*rhsName, *lhsConst); any = true; }
        } else if (ce.kind == Kind::Lt) {
            // strict (assume integer): v < K → v <= K-1; K < v → v >= K+1
            if (lhsName && rhsConst) { addUpper(*lhsName, *rhsConst - 1); any = true; }
            else if (lhsConst && rhsName) { addLower(*rhsName, *lhsConst + 1); any = true; }
        } else if (ce.kind == Kind::Gt) {
            if (lhsName && rhsConst) { addLower(*lhsName, *rhsConst + 1); any = true; }
            else if (lhsConst && rhsName) { addUpper(*rhsName, *lhsConst - 1); any = true; }
        }
    }

    for (const auto& [v, lh] : pending) {
        if (lh.first && lh.second) {
            const mpz_class& lo = *lh.first;
            const mpz_class& hi = *lh.second;
            if (lo <= hi) {
                // Use find() BEFORE operator[] to avoid auto-insertion of
                // a default-constructed (0,0) that would later be
                // mistaken for an existing bound to intersect with.
                auto it = p.boundedGlobals.find(v);
                if (it == p.boundedGlobals.end()) {
                    p.boundedGlobals.emplace(v, std::make_pair(lo, hi));
                } else {
                    // Tighten existing bounds (intersect).
                    if (lo > it->second.first)  it->second.first  = lo;
                    if (hi < it->second.second) it->second.second = hi;
                }
            }
        }
    }
    return any;
}

void FarkasOrDetector::classifyBilinearCovars(FarkasProfile& p) const {
    std::unordered_set<std::string> lambdaUniverse;
    for (const auto& blk : p.blocks) {
        for (const auto& br : blk.branches) {
            for (const auto& l : br.lambdas) lambdaUniverse.insert(l);
        }
    }
    // Walker: collect all Variable names that appear inside Mul nodes adjacent
    // to λ-vars (= "λ-coefficient" vars).
    std::unordered_set<std::string> coVars;
    std::function<void(ExprId, bool, bool)> walk;
    walk = [&](ExprId id, bool inMul, bool seenLambda) -> void {
        const auto& e = ir_.get(id);
        if (e.kind == Kind::Variable) {
            auto vn = asVarName(id);
            if (!vn) return;
            if (lambdaUniverse.count(*vn)) {
                // Mark all OTHER vars in the surrounding Mul as co-vars.
                // (Handled by the Mul branch below.)
            } else if (inMul && seenLambda) {
                coVars.insert(*vn);
            }
            return;
        }
        if (e.kind == Kind::Mul) {
            // Two-pass: first determine if Mul contains any λ.
            bool hasLam = false;
            for (ExprId c : e.children) {
                const auto& ce = ir_.get(c);
                if (ce.kind == Kind::Variable) {
                    auto vn = asVarName(c);
                    if (vn && lambdaUniverse.count(*vn)) hasLam = true;
                }
            }
            for (ExprId c : e.children) walk(c, true, hasLam);
            return;
        }
        for (ExprId c : e.children) walk(c, false, false);
    };

    for (const auto& blk : p.blocks) {
        for (const auto& br : blk.branches) {
            for (ExprId atom : br.equalities)   walk(atom, false, false);
            for (ExprId atom : br.inequalities) walk(atom, false, false);
        }
    }

    for (const auto& v : coVars) {
        if (p.boundedGlobals.count(v) == 0) {
            p.unboundedCT.insert(v);
        }
    }
}

// P0.5 diagnostic: detect-time per-rejected-branch dump (env-gated). When
// XOLVER_NIA_FARKAS_REJECT_DUMP=1 and the dump file is open (set by
// detect() at start), print for every Or assertion that didn't pass
// allBranchesFarkas(): per-branch lambdas/eqs/ineqs/unclassified counts +
// the kind of each unclassified atom. This is the cheapest possible
// "why didn't it classify" signal.
namespace {
std::FILE* gRejectDumpFile = nullptr;

void openRejectDump() {
    if (!std::getenv("XOLVER_NIA_FARKAS_REJECT_DUMP")) return;
    if (gRejectDumpFile) return;
    const char* path = std::getenv("XOLVER_NIA_FARKAS_REJECT_FILE");
    if (!path || !*path) path = "/tmp/farkas_reject";
    gRejectDumpFile = std::fopen(path, "a");
}

void closeRejectDump() {
    if (gRejectDumpFile) { std::fclose(gRejectDumpFile); gRejectDumpFile = nullptr; }
}
} // namespace

FarkasProfile FarkasOrDetector::detect() const {
    FarkasProfile p;
    openRejectDump();

    // Pre-pass: build Tseitin / Boolean-Purification var-definition map.
    // The frontend's purify-bool pass replaces an Or-branch's And with a
    // fresh Bool var `boolpur_K` and adds a separate `(= boolpur_K (and …))`
    // assertion. To see the ORIGINAL Or-of-And we need to substitute the
    // proxy with its definition. We collect all `(= Variable Expr)` atoms
    // whose Variable has Bool sort.
    std::unordered_map<std::string, ExprId> tseitinDefs;
    auto addDef = [&](ExprId eqId) {
        const auto& e = ir_.get(eqId);
        if (e.kind != Kind::Eq || e.children.size() != 2) return;
        const auto& lhs = ir_.get(e.children[0]);
        const auto& rhs = ir_.get(e.children[1]);
        // Either side may be the Variable proxy.
        if (lhs.kind == Kind::Variable && rhs.kind != Kind::Variable) {
            auto* s = std::get_if<std::string>(&lhs.payload.value);
            if (s) tseitinDefs[*s] = e.children[1];
        } else if (rhs.kind == Kind::Variable && lhs.kind != Kind::Variable) {
            auto* s = std::get_if<std::string>(&rhs.payload.value);
            if (s) tseitinDefs[*s] = e.children[0];
        }
    };
    for (ExprId aid : ir_.assertions()) {
        const auto& a = ir_.get(aid);
        if (a.kind == Kind::Eq) addDef(aid);
    }

    // Resolve a child of an Or: if it's a proxy Variable, swap with the
    // defining ExprId; otherwise pass through.
    auto resolve = [&](ExprId childId) -> ExprId {
        const auto& c = ir_.get(childId);
        if (c.kind != Kind::Variable) return childId;
        if (auto* s = std::get_if<std::string>(&c.payload.value)) {
            auto it = tseitinDefs.find(*s);
            if (it != tseitinDefs.end()) return it->second;
        }
        return childId;
    };

    // Track which Eq atoms were consumed as Tseitin definitions for blocks
    // we accepted; those Eqs should NOT be added to outerAssertions (the
    // residual LIA solver would otherwise re-enforce the proxy↔body
    // equivalence, which is redundant once the Or was substituted).
    std::unordered_set<std::string> usedDefs;

    for (ExprId aid : ir_.assertions()) {
        const auto& a = ir_.get(aid);

        if (a.kind == Kind::Or) {
            // Build substituted-children Or in-place: walk children, resolve
            // each, classify as a branch.
            FarkasOrBlock block;
            block.originalOr = aid;
            block.branches.reserve(a.children.size());
            std::vector<std::string> resolvedProxies;  // for cleanup if accepted
            for (ExprId c : a.children) {
                ExprId resolved = resolve(c);
                const auto& re = ir_.get(c);
                if (re.kind == Kind::Variable) {
                    if (auto* s = std::get_if<std::string>(&re.payload.value)) {
                        if (tseitinDefs.count(*s)) resolvedProxies.push_back(*s);
                    }
                }
                block.branches.push_back(classifyAnd(resolved));
            }
            if (block.allBranchesFarkas()) {
                for (const auto& v : resolvedProxies) usedDefs.insert(v);
                p.blocks.push_back(std::move(block));
                continue;
            }
            // P0.5: dump why this block was rejected. Helps fix classifyAnd.
            if (gRejectDumpFile) {
                static const char* kindNames[] = {
                    "ConstBool","ConstInt","ConstReal","ConstBV","ConstFP",
                    "Variable","UFApply",
                    "Not","And","Or","Implies","Xor","Ite",
                    "Add","Sub","Neg","Mul","Div","Mod","Abs","Pow",
                    "Eq","Distinct","Lt","Leq","Gt","Geq",
                    "BvNot","BvAnd","BvOr","BvAdd","BvMul",
                    "Forall","Exists",
                    "ToInt","ToReal","IsInt",
                    "Select","Store","ConstArray",
                    "Constructor","Selector","Tester",
                    "Unknown"
                };
                auto kname = [&](Kind k) -> const char* {
                    unsigned i = static_cast<unsigned>(k);
                    return i < sizeof(kindNames)/sizeof(kindNames[0]) ? kindNames[i] : "??";
                };
                std::fprintf(gRejectDumpFile, "REJECT Or id=%u branches=%zu\n",
                             aid, block.branches.size());
                for (std::size_t j = 0; j < block.branches.size(); ++j) {
                    const auto& br = block.branches[j];
                    std::fprintf(gRejectDumpFile,
                                 "  branch[%zu] λ=%zu eq=%zu ineq=%zu UNCLASS=%zu farkasShape=%d\n",
                                 j, br.lambdas.size(), br.equalities.size(),
                                 br.inequalities.size(), br.unclassified.size(),
                                 br.farkasShape() ? 1 : 0);
                    // List λ names (first 6).
                    if (!br.lambdas.empty()) {
                        std::fprintf(gRejectDumpFile, "    λ:");
                        for (std::size_t li = 0; li < br.lambdas.size() && li < 6; ++li) {
                            std::fprintf(gRejectDumpFile, " %s", br.lambdas[li].c_str());
                        }
                        std::fprintf(gRejectDumpFile, "\n");
                    }
                    // Per unclassified atom: kind + child kinds.
                    for (std::size_t ui = 0; ui < br.unclassified.size() && ui < 8; ++ui) {
                        ExprId uid = br.unclassified[ui];
                        const auto& ue = ir_.get(uid);
                        std::fprintf(gRejectDumpFile, "    U[%zu] id=%u kind=%s children=%zu",
                                     ui, uid, kname(ue.kind), ue.children.size());
                        if (!ue.children.empty()) {
                            std::fprintf(gRejectDumpFile, " [");
                            for (std::size_t ci = 0; ci < ue.children.size() && ci < 6; ++ci) {
                                const auto& ce = ir_.get(ue.children[ci]);
                                std::fprintf(gRejectDumpFile, "%s%s",
                                             ci ? "," : "", kname(ce.kind));
                            }
                            std::fprintf(gRejectDumpFile, "]");
                        }
                        std::fprintf(gRejectDumpFile, "\n");
                    }
                }
                std::fflush(gRejectDumpFile);
            }
        }
        if (a.kind == Kind::And) {
            extractBoundsFromAnd(aid, p);
        }
        // Skip Tseitin equivalences whose proxies we consumed (avoid
        // double-counting in the residual).
        if (a.kind == Kind::Eq && a.children.size() == 2) {
            for (ExprId side : a.children) {
                const auto& se = ir_.get(side);
                if (se.kind == Kind::Variable) {
                    if (auto* s = std::get_if<std::string>(&se.payload.value)) {
                        if (usedDefs.count(*s)) goto skip_outer;
                    }
                }
            }
        }
        p.outerAssertions.push_back(aid);
        skip_outer:;
    }
    classifyBilinearCovars(p);
    closeRejectDump();
    return p;
}

std::string FarkasOrDetector::dump(const FarkasProfile& p) const {
    static const char* kindName[] = {
        "ConstBool","ConstInt","ConstReal","ConstBV","ConstFP",
        "Variable","UFApply",
        "Not","And","Or","Implies","Xor","Ite",
        "Add","Sub","Neg","Mul","Div","Mod","Abs","Pow",
        "Eq","Distinct","Lt","Leq","Gt","Geq",
        "BvNot","BvAnd","BvOr","BvAdd","BvMul",
        "Forall","Exists",
        "ToInt","ToReal","IsInt",
        "Select","Store","ConstArray",
        "Constructor","Selector","Tester",
        "Unknown"
    };
    auto knameOf = [&](Kind k) -> const char* {
        unsigned idx = static_cast<unsigned>(k);
        if (idx < sizeof(kindName) / sizeof(kindName[0])) return kindName[idx];
        return "??";
    };
    std::ostringstream os;
    os << "FarkasOr Profile:\n";
    os << "  blocks            = " << p.blocks.size() << "\n";
    os << "  total branches    = " << p.branchTotal() << "\n";
    os << "  outer assertions  = " << p.outerAssertions.size() << "\n";
    // P0 debug: show top-level kind of each outer assertion so we can see
    // why Or-shaped assertions got rejected.
    auto varName = [&](ExprId id) -> std::string {
        const auto& e = ir_.get(id);
        if (e.kind == Kind::Variable) {
            if (auto* s = std::get_if<std::string>(&e.payload.value)) return *s;
        }
        return "";
    };
    for (std::size_t i = 0; i < p.outerAssertions.size(); ++i) {
        ExprId aid = p.outerAssertions[i];
        const auto& a = ir_.get(aid);
        os << "    outer[" << i << "] id=" << aid << " kind=" << knameOf(a.kind);
        if (a.kind == Kind::And || a.kind == Kind::Or) {
            os << " children=" << a.children.size() << " [";
            for (std::size_t j = 0; j < a.children.size() && j < 8; ++j) {
                if (j) os << ", ";
                os << knameOf(ir_.get(a.children[j]).kind);
                auto vn = varName(a.children[j]);
                if (!vn.empty()) os << "(" << vn << ")";
            }
            if (a.children.size() > 8) os << ", ...";
            os << "]";
        } else if (a.kind == Kind::Eq && a.children.size() == 2) {
            // For Tseitin equivalences: `(= V expr)` show the variable name.
            auto lhsName = varName(a.children[0]);
            auto rhsName = varName(a.children[1]);
            os << " [" << knameOf(ir_.get(a.children[0]).kind);
            if (!lhsName.empty()) os << "(" << lhsName << ")";
            os << " == " << knameOf(ir_.get(a.children[1]).kind);
            if (!rhsName.empty()) os << "(" << rhsName << ")";
            os << "]";
        }
        os << "\n";
    }
    os << "  bounded globals   = " << p.boundedGlobals.size();
    if (!p.boundedGlobals.empty()) {
        os << " { ";
        bool first = true;
        for (const auto& [v, lh] : p.boundedGlobals) {
            if (!first) os << ", ";
            os << v << " in [" << lh.first.get_str()
               << ", " << lh.second.get_str() << "]";
            first = false;
        }
        os << " }";
    }
    os << "\n";
    os << "  unbounded CT-like = " << p.unboundedCT.size();
    if (!p.unboundedCT.empty()) {
        os << " {";
        bool first = true;
        for (const auto& v : p.unboundedCT) {
            os << (first ? " " : ", ") << v;
            first = false;
        }
        os << " }";
    }
    os << "\n";

    for (std::size_t i = 0; i < p.blocks.size(); ++i) {
        const auto& blk = p.blocks[i];
        os << "  block[" << i << "] originalOr=" << blk.originalOr
           << " branches=" << blk.branches.size() << "\n";
        for (std::size_t j = 0; j < blk.branches.size(); ++j) {
            const auto& br = blk.branches[j];
            os << "    branch[" << j << "] originalAnd=" << br.originalAnd
               << " lambdas=" << br.lambdas.size()
               << " eqs=" << br.equalities.size()
               << " ineqs=" << br.inequalities.size()
               << " unclassified=" << br.unclassified.size();
            if (!br.lambdas.empty()) {
                os << " {";
                bool first = true;
                for (const auto& l : br.lambdas) {
                    os << (first ? " " : ", ") << l;
                    first = false;
                }
                os << " }";
            }
            os << "\n";
        }
    }
    return os.str();
}

} // namespace xolver::farkas
