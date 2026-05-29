#include "theory/arith/bit_blast/EagerBitBlastSolver.h"
#include "theory/arith/bit_blast/BitBlastEncoder.h"
#include "theory/arith/bit_blast/PolyBitBlaster.h"
#include "theory/arith/bit_blast/BitVec.h"
#include "theory/arith/bit_blast/SpaceEstimator.h"
#include "sat/SatSolver.h"
#include <functional>
#include <unordered_set>
#include <cstdlib>
#include <iostream>
#include <chrono>

namespace xolver::bitblast {

EagerBitBlastSolver::EagerBitBlastSolver()
    : kernel_(createPolynomialKernel()),
      converter_(std::make_unique<PolynomialConverter>(*kernel_)) {}

bool EagerBitBlastSolver::relationHolds(const mpz_class& v, Relation rel) {
    switch (rel) {
        case Relation::Eq:  return v == 0;
        case Relation::Neq: return v != 0;
        case Relation::Lt:  return v <  0;
        case Relation::Leq: return v <= 0;
        case Relation::Gt:  return v >  0;
        case Relation::Geq: return v >= 0;
    }
    return false;
}

bool EagerBitBlastSolver::isBoolTyped(ExprId eid, const CoreIr& ir) const {
    const CoreExpr& e = ir.get(eid);
    switch (e.kind) {
        case Kind::ConstBool: case Kind::Not: case Kind::And: case Kind::Or:
        case Kind::Implies:   case Kind::Xor:
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
            return true;
        case Kind::Eq: case Kind::Distinct:
            return !e.children.empty() && isBoolTyped(e.children[0], ir);
        case Kind::Ite:
            return e.children.size() == 3 && isBoolTyped(e.children[1], ir);
        case Kind::Variable:
            return e.sort == ir.boolSortId();
        default:
            return false;  // ConstInt / Add / Mul / ... are integer-typed
    }
}

bool EagerBitBlastSolver::isArithAtom(ExprId eid, const CoreIr& ir) const {
    const CoreExpr& e = ir.get(eid);
    switch (e.kind) {
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
            return true;
        case Kind::Eq: case Kind::Distinct:
            return !e.children.empty() && !isBoolTyped(e.children[0], ir);
        default:
            return false;
    }
}

void EagerBitBlastSolver::tryExtractBound(PolyId diff, Relation rel) {
    // Extract a bound on x from a single-variable linear atom `a*x + c rel 0`
    // with |a| == 1. Conservative: records nothing unless certain (a loose/absent
    // bound just falls back to the cascade width — never unsound).
    auto vars = kernel_->variables(diff);
    if (vars.size() != 1) return;
    const std::string& x = vars[0];
    auto degOpt = kernel_->degree(diff, x);
    if (!degOpt || *degOpt != 1) return;
    auto coeffsOpt = kernel_->getIntegerCoefficients(diff, x);
    if (!coeffsOpt || coeffsOpt->size() != 2) return;
    mpz_class a = (*coeffsOpt)[0];   // coeff of x
    mpz_class c = (*coeffsOpt)[1];   // constant
    if (a != 1 && a != -1) return;

    bool hasLo = false, hasHi = false;
    mpz_class lo, hi;
    if (a == 1) {
        mpz_class B = -c;            // x + c rel 0  =>  x rel (-c)
        switch (rel) {
            case Relation::Leq: hi = B;     hasHi = true; break;
            case Relation::Geq: lo = B;     hasLo = true; break;
            case Relation::Lt:  hi = B - 1; hasHi = true; break;
            case Relation::Gt:  lo = B + 1; hasLo = true; break;
            case Relation::Eq:  lo = hi = B; hasLo = hasHi = true; break;
            case Relation::Neq: break;
        }
    } else {                         // a == -1: -x + c rel 0
        mpz_class B = c;
        switch (rel) {
            case Relation::Leq: lo = B;     hasLo = true; break;   // x >= c
            case Relation::Geq: hi = B;     hasHi = true; break;   // x <= c
            case Relation::Lt:  lo = B + 1; hasLo = true; break;   // x > c
            case Relation::Gt:  hi = B - 1; hasHi = true; break;   // x < c
            case Relation::Eq:  lo = hi = B; hasLo = hasHi = true; break;
            case Relation::Neq: break;
        }
    }
    if (hasLo) { auto it = lb_.find(x); if (it == lb_.end() || lo > it->second) lb_[x] = lo; }
    if (hasHi) { auto it = ub_.find(x); if (it == ub_.end() || hi < it->second) ub_[x] = hi; }
}

bool EagerBitBlastSolver::collect(const CoreIr& ir, const std::vector<ExprId>& assertions) {
    std::unordered_set<std::string> intVarSet;
    std::unordered_set<ExprId> visited;
    bool ok = true;

    // Convert an arith atom into its (diff, rel) parts (single relation, or a
    // chain for n-ary Eq, or all pairwise Neq for Distinct). Collect its vars.
    auto addPair = [&](ExprId l, ExprId r, Relation rel, AtomCs& cs) {
        auto cc = converter_->convertConstraint(l, r, rel, ir);
        switch (cc.status) {
            case PolyConstraintStatus::Constraint:
                cs.parts.push_back({cc.diff, rel});
                for (const auto& v : kernel_->variables(cc.diff)) intVarSet.insert(v);
                tryExtractBound(cc.diff, rel);
                break;
            case PolyConstraintStatus::Tautology:
                cs.parts.push_back({NullPoly, Relation::Eq});   // marker: always-true (0==0)
                break;
            case PolyConstraintStatus::Conflict:
                cs.parts.push_back({NullPoly, Relation::Neq});  // marker: always-false (0!=0)
                break;
            default:
                if (std::getenv("NIA_EAGER_BB_DIAG"))
                    std::cerr << "[EAGER-BB] addPair reject status=" << (int)cc.status
                              << " l=" << l << " r=" << r << " rel=" << (int)rel << "\n";
                ok = false;  // non-polynomial / failure -> eager bit-blast not applicable
                break;
        }
    };

    std::function<void(ExprId)> walk = [&](ExprId eid) {
        if (!ok || !visited.insert(eid).second) return;
        const CoreExpr& e = ir.get(eid);
        switch (e.kind) {
            case Kind::ConstBool:
                return;
            case Kind::Variable:
                // A walked Variable is a boolean (arith vars live inside atoms,
                // collected via convertConstraint). Non-bool bare var => reject.
                if (e.sort != ir.boolSortId()) {
                    if (std::getenv("NIA_EAGER_BB_DIAG"))
                        std::cerr << "[EAGER-BB] collect reject non-bool Variable eid=" << eid
                                  << " sort=" << e.sort << "\n";
                    ok = false;
                }
                return;
            case Kind::Not: case Kind::And: case Kind::Or:
            case Kind::Implies: case Kind::Xor: case Kind::Ite:
                for (ExprId c : e.children) walk(c);
                return;
            case Kind::Eq: case Kind::Distinct:
                if (isArithAtom(eid, ir)) {
                    AtomCs cs;
                    const auto& ch = e.children;
                    if (e.kind == Kind::Eq) {
                        for (size_t i = 0; i + 1 < ch.size(); ++i)
                            addPair(ch[i], ch[i + 1], Relation::Eq, cs);
                    } else {  // Distinct: all pairwise !=
                        for (size_t i = 0; i < ch.size(); ++i)
                            for (size_t j = i + 1; j < ch.size(); ++j)
                                addPair(ch[i], ch[j], Relation::Neq, cs);
                    }
                    atomCs_[eid] = std::move(cs);
                } else {
                    for (ExprId c : e.children) walk(c);  // boolean iff / distinct
                }
                return;
            case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
                AtomCs cs;
                if (e.children.size() == 2) addPair(e.children[0], e.children[1], relOf(e.kind), cs);
                else { if (std::getenv("NIA_EAGER_BB_DIAG")) std::cerr << "[EAGER-BB] collect reject rel-arity=" << e.children.size() << " kind=" << (int)e.kind << "\n"; ok = false; }
                atomCs_[eid] = std::move(cs);
                return;
            }
            default:
                if (std::getenv("NIA_EAGER_BB_DIAG"))
                    std::cerr << "[EAGER-BB] collect reject kind=" << (int)e.kind << " eid=" << eid << "\n";
                ok = false;  // UF / array / quantifier / real / BV / datatype
                return;
        }
    };

    for (ExprId a : assertions) walk(a);
    if (!ok) return false;
    intVars_.assign(intVarSet.begin(), intVarSet.end());
    return true;
}

Relation EagerBitBlastSolver::relOf(Kind k) {
    switch (k) {
        case Kind::Lt:  return Relation::Lt;
        case Kind::Leq: return Relation::Leq;
        case Kind::Gt:  return Relation::Gt;
        case Kind::Geq: return Relation::Geq;
        case Kind::Eq:  return Relation::Eq;
        default:        return Relation::Neq;
    }
}

EagerBitBlastSolver::Result EagerBitBlastSolver::solve(const CoreIr& ir,
                                            const std::vector<ExprId>& assertions) {
    Result out;
    if (assertions.empty()) return out;
    atomCs_.clear();
    intVars_.clear();
    lb_.clear();
    ub_.clear();
    static const bool diag = std::getenv("NIA_EAGER_BB_DIAG") != nullptr;
    if (!collect(ir, assertions)) return out;   // unsupported construct -> Unknown
    if (diag) std::cerr << "[EAGER-BB] collect done: intVars=" << intVars_.size()
                        << " atoms=" << atomCs_.size() << "\n";

    uint64_t budget = 2000000ull;   // var-budget cap: bail huge encodes (overflow) fast
    if (const char* e = std::getenv("XOLVER_NIA_EAGER_BITBLAST_BUDGET")) {
        char* end = nullptr; long long v = std::strtoll(e, &end, 10);
        if (end != e && v > 0) budget = static_cast<uint64_t>(v);
    }
    // Time-box the arm so it cannot eat the budget the CDCL(T) main loop needs
    // on UNSAT cases (eager bit-blast can never prove UNSAT here, so it would churn
    // widths forever). Per-solve conflict limit bounds a single hard solve;
    // wall-clock deadline bounds the whole cascade. Both env-tunable.
    long long budgetMs = 3000;
    if (const char* e = std::getenv("XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS")) {
        char* end = nullptr; long long v = std::strtoll(e, &end, 10);
        if (end != e && v >= 0) budgetMs = v;
    }
    int confLimit = 50000;
    if (const char* e = std::getenv("XOLVER_NIA_EAGER_BITBLAST_CONFLICTS")) {
        char* end = nullptr; long long v = std::strtoll(e, &end, 10);
        if (end != e && v > 0) confLimit = static_cast<int>(v);
    }
    const auto t0 = std::chrono::steady_clock::now();
    auto elapsedMs = [&]() {
        return std::chrono::duration_cast<std::chrono::milliseconds>(
                   std::chrono::steady_clock::now() - t0).count();
    };
    const unsigned widths[] = {4, 8, 16, 24, 32};

    for (unsigned K : widths) {
        if (budgetMs > 0 && elapsedMs() >= budgetMs) {
            if (diag) std::cerr << "[EAGER-BB] wall-clock budget hit before width=" << K << "\n";
            break;
        }
        auto sat = createSatSolver();
        BitBlastEncoder enc(*sat);
        enc.setVarBudget(budget);

        // Per-var width (BLAN collector discipline): both-sided-bounded vars get
        // their EXACT width (the value provably fits — bound atom still encoded);
        // unbounded vars get the cascade width K. This is the dominant size win on
        // bound-heavy formulas (Farkas templates: invariant coeffs in [-1,1]).
        std::unordered_map<std::string, BitVec> varBits;
        for (const auto& v : intVars_) {
            unsigned w = K;
            auto il = lb_.find(v), iu = ub_.find(v);
            if (il != lb_.end() && iu != ub_.end() && il->second <= iu->second)
                w = SpaceEstimator::bitsToCover(il->second, iu->second);
            varBits[v] = enc.mkVar(w);
        }
        PolyBitBlaster blaster(enc, *kernel_, varBits);

        std::unordered_map<ExprId, SatLit> memo;
        std::unordered_map<ExprId, SatLit> boolVars;
        bool encodeOk = true;
        long long encodeOps = 0;

        std::function<SatLit(ExprId)> encode = [&](ExprId eid) -> SatLit {
            if (!encodeOk) return enc.constFalse();
            // In-encode time guard: a single huge formula's encode must not blow
            // the wall-clock budget (it's only checked between widths otherwise).
            if (budgetMs > 0 && ((++encodeOps & 0x3FFF) == 0) && elapsedMs() >= budgetMs) {
                encodeOk = false;
                return enc.constFalse();
            }
            auto m = memo.find(eid);
            if (m != memo.end()) return m->second;
            const CoreExpr& e = ir.get(eid);
            SatLit r = enc.constFalse();
            switch (e.kind) {
                case Kind::ConstBool: {
                    auto* b = std::get_if<bool>(&e.payload.value);
                    r = (b && *b) ? enc.constTrue() : enc.constFalse();
                    break;
                }
                case Kind::Variable: {
                    auto it = boolVars.find(eid);
                    if (it != boolVars.end()) r = it->second;
                    else { SatLit l = enc.mkVar(1).bits[0]; boolVars[eid] = l; r = l; }
                    break;
                }
                case Kind::Not:
                    r = encode(e.children[0]).negated();
                    break;
                case Kind::And: {
                    r = enc.constTrue();
                    for (ExprId c : e.children) r = enc.andGate(r, encode(c));
                    break;
                }
                case Kind::Or: {
                    r = enc.constFalse();
                    for (ExprId c : e.children) r = enc.orGate(r, encode(c));
                    break;
                }
                case Kind::Implies: {
                    // right-assoc: (=> a b c) = a -> (b -> c)
                    r = encode(e.children.back());
                    for (size_t i = e.children.size() - 1; i-- > 0;)
                        r = enc.orGate(encode(e.children[i]).negated(), r);
                    break;
                }
                case Kind::Xor: {
                    r = encode(e.children[0]);
                    for (size_t i = 1; i < e.children.size(); ++i)
                        r = enc.xorGate(r, encode(e.children[i]));
                    break;
                }
                case Kind::Ite:
                    r = enc.iteGate(encode(e.children[0]), encode(e.children[1]),
                                    encode(e.children[2]));
                    break;
                case Kind::Eq: case Kind::Distinct:
                case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
                    if (isArithAtom(eid, ir)) {
                        r = enc.constTrue();
                        auto it = atomCs_.find(eid);
                        if (it == atomCs_.end()) { encodeOk = false; break; }
                        for (const auto& part : it->second.parts) {
                            SatLit pl;
                            if (part.first == NullPoly)
                                pl = (part.second == Relation::Eq) ? enc.constTrue()
                                                                   : enc.constFalse();
                            else
                                pl = enc.relZero(blaster.encodePoly(part.first), part.second);
                            r = enc.andGate(r, pl);
                        }
                    } else if (e.kind == Kind::Eq) {  // boolean iff chain
                        r = enc.constTrue();
                        for (size_t i = 0; i + 1 < e.children.size(); ++i)
                            r = enc.andGate(r, enc.xorGate(encode(e.children[i]),
                                                           encode(e.children[i + 1])).negated());
                    } else {  // boolean distinct: all pairwise differ
                        r = enc.constTrue();
                        const auto& ch = e.children;
                        for (size_t i = 0; i < ch.size(); ++i)
                            for (size_t j = i + 1; j < ch.size(); ++j)
                                r = enc.andGate(r, enc.xorGate(encode(ch[i]), encode(ch[j])));
                    }
                    break;
                }
                default:
                    encodeOk = false;
                    break;
            }
            memo[eid] = r;
            return r;
        };

        for (ExprId a : assertions) {
            SatLit l = encode(a);
            if (!encodeOk) break;
            enc.assertLit(l);
        }
        if (!encodeOk) return out;            // unsupported mid-encode -> Unknown
        if (enc.overflowed()) {               // budget blown; wider K only worse
            if (diag) std::cerr << "[EAGER-BB] overflow at width=" << K << " -> stop\n";
            break;
        }

        if (confLimit > 0) sat->limit("conflicts", confLimit);
        long long encMs = elapsedMs();
        auto res = sat->solve();
        if (diag) std::cerr << "[EAGER-BB] width=" << K << " vars=" << enc.varCount()
                            << " sat=" << (res == SatSolver::SolveResult::Sat ? "Y" :
                                          res == SatSolver::SolveResult::Unsat ? "N" : "?")
                            << " encMs=" << encMs << " solveMs=" << (elapsedMs() - encMs) << "\n";
        if (res != SatSolver::SolveResult::Sat) continue;   // wider K (never claim UNSAT)

        // Candidate model -> EXACT integer re-validation over all assertions.
        std::unordered_map<std::string, mpz_class> model;
        for (const auto& v : intVars_) model[v] = readBitVec(*sat, varBits.at(v));
        std::unordered_map<ExprId, bool> boolModel;
        for (const auto& kv : boolVars) boolModel[kv.first] = litValue(*sat, kv.second);

        std::function<bool(ExprId)> ev = [&](ExprId eid) -> bool {
            const CoreExpr& e = ir.get(eid);
            switch (e.kind) {
                case Kind::ConstBool: { auto* b = std::get_if<bool>(&e.payload.value); return b && *b; }
                case Kind::Variable: { auto it = boolModel.find(eid); return it != boolModel.end() && it->second; }
                case Kind::Not: return !ev(e.children[0]);
                case Kind::And: { for (ExprId c : e.children) if (!ev(c)) return false; return true; }
                case Kind::Or:  { for (ExprId c : e.children) if (ev(c)) return true; return false; }
                case Kind::Implies: {
                    for (size_t i = 0; i + 1 < e.children.size(); ++i) if (!ev(e.children[i])) return true;
                    return ev(e.children.back());
                }
                case Kind::Xor: { bool x = false; for (ExprId c : e.children) x ^= ev(c); return x; }
                case Kind::Ite: return ev(e.children[0]) ? ev(e.children[1]) : ev(e.children[2]);
                case Kind::Eq: case Kind::Distinct:
                case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq: {
                    if (isArithAtom(eid, ir)) {
                        auto it = atomCs_.find(eid);
                        if (it == atomCs_.end()) return false;
                        for (const auto& part : it->second.parts) {
                            if (part.first == NullPoly) {
                                if (part.second != Relation::Eq) return false;  // conflict marker
                                continue;                                       // tautology marker
                            }
                            auto val = kernel_->evalInteger(part.first, model);
                            if (!val || !relationHolds(*val, part.second)) return false;
                        }
                        return true;
                    } else if (e.kind == Kind::Eq) {
                        for (size_t i = 0; i + 1 < e.children.size(); ++i)
                            if (ev(e.children[i]) != ev(e.children[i + 1])) return false;
                        return true;
                    } else {
                        const auto& ch = e.children;
                        for (size_t i = 0; i < ch.size(); ++i)
                            for (size_t j = i + 1; j < ch.size(); ++j)
                                if (ev(ch[i]) == ev(ch[j])) return false;
                        return true;
                    }
                }
                default: return false;
            }
        };

        bool valid = true;
        for (ExprId a : assertions) if (!ev(a)) { valid = false; break; }
        if (diag) std::cerr << "[EAGER-BB] width=" << K << " candidate valid=" << valid << "\n";
        if (valid) { out.status = Status::Sat; out.model = std::move(model); return out; }
        // SAT but candidate failed exact validation (narrow-width artifact) -> wider K.
    }
    return out;   // Unknown
}

} // namespace xolver::bitblast
