#include "theory/arith/bit_blast/EagerBitBlastSolver.h"
#include "util/EnvParam.h"
#include "util/SolveClock.h"
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
    // The CoreExpr already carries the resolved sort -- trust it when known.
    // Lt/Leq/Gt/Geq/Distinct ALWAYS return Bool by SMT-LIB semantics regardless
    // of operand types, so the historic "peek children[0]" trick mis-classified
    // `Eq(Distinct(int,int), bool_var)` as an arith atom and routed Distinct
    // through PolynomialConverter (-> UnsupportedNonPolynomial). The sort-based
    // check resolves this for every Bool-returning expression in one place.
    if (e.sort == ir.boolSortId()) return true;
    switch (e.kind) {
        case Kind::ConstBool: case Kind::Not: case Kind::And: case Kind::Or:
        case Kind::Implies:   case Kind::Xor:
        case Kind::Lt: case Kind::Leq: case Kind::Gt: case Kind::Geq:
        case Kind::Distinct:
            return true;
        case Kind::Eq:
            // Eq returns Bool but its "is-arith-atom" status depends on whether
            // its first child is bool-typed -- only an Eq over Bool children is
            // a boolean iff; Eq over ints is an arith atom.
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
                break;
            case PolyConstraintStatus::Tautology:
                cs.parts.push_back({NullPoly, Relation::Eq});   // marker: always-true (0==0)
                break;
            case PolyConstraintStatus::Conflict:
                cs.parts.push_back({NullPoly, Relation::Neq});  // marker: always-false (0!=0)
                break;
            default:
                if (std::getenv("NIA_EAGER_BB_DIAG")) {
                    auto kindStr = [](Kind k) -> const char* {
                        switch (k) {
                          case Kind::ConstInt: return "ConstInt"; case Kind::ConstReal: return "ConstReal";
                          case Kind::ConstBool: return "ConstBool"; case Kind::Variable: return "Variable";
                          case Kind::Add: return "Add"; case Kind::Sub: return "Sub"; case Kind::Mul: return "Mul";
                          case Kind::Div: return "Div"; case Kind::Mod: return "Mod"; case Kind::Pow: return "Pow";
                          case Kind::Neg: return "Neg"; case Kind::Abs: return "Abs";
                          case Kind::ToInt: return "ToInt"; case Kind::ToReal: return "ToReal";
                          case Kind::Eq: return "Eq"; case Kind::Distinct: return "Distinct";
                          case Kind::Lt: return "Lt"; case Kind::Leq: return "Leq";
                          case Kind::Gt: return "Gt"; case Kind::Geq: return "Geq";
                          case Kind::Not: return "Not"; case Kind::And: return "And"; case Kind::Or: return "Or";
                          case Kind::Implies: return "Implies"; case Kind::Xor: return "Xor"; case Kind::Ite: return "Ite";
                          default: return "?";
                        }
                    };
                    std::function<void(ExprId, int)> dump = [&](ExprId e, int depth) {
                        if (depth > 6) { std::cerr << "..."; return; }
                        const CoreExpr& n = ir.get(e);
                        std::cerr << "(" << kindStr(n.kind) << "[" << e << "/sort" << n.sort;
                        if (n.kind == Kind::Variable) {
                            if (auto* s = std::get_if<std::string>(&n.payload.value))
                                std::cerr << "/'" << *s << "'";
                        } else if (n.kind == Kind::ConstInt || n.kind == Kind::ConstReal) {
                            if (auto* i = std::get_if<int64_t>(&n.payload.value)) std::cerr << "/" << *i;
                            else if (auto* s = std::get_if<std::string>(&n.payload.value)) std::cerr << "/" << *s;
                        }
                        std::cerr << "]";
                        for (ExprId c : n.children) { std::cerr << " "; dump(c, depth + 1); }
                        std::cerr << ")";
                    };
                    std::cerr << "[EAGER-BB] boolSortId=" << ir.boolSortId() << " intSortId=" << ir.intSortId() << "\n";
                    std::cerr << "[EAGER-BB] addPair reject status=" << (int)cc.status
                              << " rel=" << (int)rel << " l="; dump(l, 0);
                    std::cerr << " r="; dump(r, 0);
                    std::cerr << "\n";
                }
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

    // Bound extraction is POLARITY-AWARE: only atoms that are TOP-LEVEL POSITIVE
    // CONJUNCTS (reachable from an assertion root through And nodes only) are
    // genuinely asserted, so only those may set variable bounds (-> offset width)
    // and be skipped in the encoding. An atom under not/or/ite/implies is NOT
    // guaranteed true — extracting a bound from it (e.g. `(= rfc0 0)` under
    // `(not ...)`) would wrongly pin rfc0=0 and produce an invalid model.
    std::unordered_set<ExprId> topSeen;
    std::function<void(ExprId)> markTop = [&](ExprId eid) {
        if (!topSeen.insert(eid).second) return;
        const CoreExpr& e = ir.get(eid);
        if (e.kind == Kind::And) { for (ExprId c : e.children) markTop(c); return; }
        auto it = atomCs_.find(eid);
        if (it == atomCs_.end()) return;                 // not an asserted arith atom
        if (it->second.parts.size() != 1) return;
        PolyId diff = it->second.parts[0].first;
        if (diff == NullPoly) return;
        tryExtractBound(diff, it->second.parts[0].second);
    };
    for (ExprId a : assertions) markTop(a);
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

    // Var-budget cap (encode SIZE): bounds a single attempt's encoding so a huge
    // formula bails (overflow->Unknown) instead of OOM. Competition has 30GB, so
    // 20M fresh vars (~a few GB of CNF) is safe; the per-attempt cap keeps any one
    // width from exploding while the cascade/wall-clock control total time.
    uint64_t budget = 20000000ull;
    {
        long long v = env::paramLong("XOLVER_NIA_EAGER_BITBLAST_BUDGET", 20000000);
        if (v > 0) budget = static_cast<uint64_t>(v);
    }
    // Wall-clock budget for the WHOLE arm. This is the single biggest QF_NIA
    // recovery throttle: a small budget cuts off slow-SAT before the deciding
    // width's solve. Competition gives 1200s, so default 120s lets the cascade
    // reach the deciding width while leaving ~1000s+ for the CDCL(T) UNSAT path.
    // Raising is SOUND (the arm only finds validated SAT or yields). Per-attempt
    // is still bounded by confLimit + var budget, so this does not break short
    // (dev-timeout) runs on small formulas.
    // Percentage-based portfolio scheduling (user direction 2026-06-05):
    // give EAGER a fraction of the total solve wall-clock so the remainder
    // goes to the CDCL(T) NIA reasoners (which are the only path that can
    // prove UNSAT). Without this EAGER burned the FULL timeout on UNSAT
    // cases (it never returns Unsat by design) and CDCL(T) never got a
    // chance -- measured iter-13: 4 of 10 small UNSAT cases (40 %) became
    // solvable just by giving CDCL(T) some of EAGER's budget. SAT cases
    // continue to land in the same widths so SAT wins are preserved
    // (leipzig 164 ms, SAT14/86 123 ms, mcm/113 7.7 s).
    //
    // XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT (default 33): percentage of the
    // remaining wall-clock budget given to EAGER. NO upper bound clamp -- the
    // user explicitly disallowed it (the past mistake was a hardcoded small
    // budget that made bit-blast useless because the timeout was 3 s; never
    // again). When the wallclock IS set, EAGER simply takes that share of the
    // remaining time, however large.
    //
    // Without XOLVER_WALLCLOCK_MS (e.g. dev runs under bash `timeout` only),
    // there's no internal deadline. Fall back to XOLVER_NIA_EAGER_BITBLAST_
    // BUDGET_MS (default 120s, the historical value) -- this is the dev-cycle
    // budget knob from before the percentage path; no behavior change on those
    // runs.
    //
    // Sound per the no-budget-band-aid memory: this is intelligent portfolio
    // scheduling (allocate ARM budgets by percentage), not a downgrade-to-
    // Unknown floor on a crash. EAGER still returns Unknown when its share is
    // up, exactly as before -- the change is HOW MUCH budget the arm gets.
    long long budgetMs =
        env::paramLong("XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS", 120000);
    if (budgetMs < 0) budgetMs = 120000;
    long pct = env::paramLong("XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT", 33);
    if (pct < 1) pct = 1;
    if (pct > 100) pct = 100;
    if (wall::hasDeadline()) {
        long remaining = wall::remainingMs();
        budgetMs = (static_cast<long long>(remaining) * pct) / 100;
    }
    // Per-WIDTH conflict cap: bounds one SAT solve so a single hard width can't
    // run unbounded. Competition-sized (1M) so a genuinely hard deciding width
    // gets a real chance, while still capping a futile width.
    int confLimit = static_cast<int>(
        env::paramLong("XOLVER_NIA_EAGER_BITBLAST_CONFLICTS", 1000000));
    if (confLimit <= 0) confLimit = 1000000;
    const auto t0 = std::chrono::steady_clock::now();
    auto elapsedMs = [&]() {
        return std::chrono::duration_cast<std::chrono::milliseconds>(
                   std::chrono::steady_clock::now() - t0).count();
    };
    const unsigned widths[] = {4, 8, 16, 24, 32, 48, 64};
    // Consecutive-UNSAT cap: when the inner SAT solver returns UNSAT at
    // several widths in a row WITHOUT ever finding a SAT candidate, the
    // formula is highly likely integer-genuinely-UNSAT (e.g. VeryMax
    // Farkas-Or termination-proving cases). Eager bit-blast cannot SOUNDLY
    // declare UNSAT (a width-K UNSAT verdict only says no model with bits
    // ≤ K exists). But continuing to escalate just burns budget. Bail out
    // early to Unknown so downstream stages get their share of wall-clock.
    // Default cap = 4 (UNSAT at K=4,8,16,24 → bail before K=32). Tunable.
    int consecutiveUnsat = 0;
    static const int kMaxConsecutiveUnsat = static_cast<int>(
        env::paramLong("XOLVER_NIA_EAGER_BITBLAST_UNSAT_CAP", 4));

    for (unsigned K : widths) {
        if (budgetMs > 0 && elapsedMs() >= budgetMs) {
            if (diag) std::cerr << "[EAGER-BB] wall-clock budget hit before width=" << K << "\n";
            break;
        }
        if (kMaxConsecutiveUnsat > 0 && consecutiveUnsat >= kMaxConsecutiveUnsat) {
            if (diag) std::cerr << "[EAGER-BB] consecutive-UNSAT cap hit ("
                                << consecutiveUnsat << "/" << kMaxConsecutiveUnsat
                                << ") — bail to Unknown\n";
            break;
        }
        auto sat = createSatSolver();
        // XOLVER_NIA_BITBLAST_NOPRE (default-OFF, same env as the regular
        // nia.bit-blast). Disable CaDiCaL's heavy preprocessing on the eager
        // bit-blast's INTERNAL solve. Profiled in the QF_NIA LassoRanker /
        // AProVE termination cluster (Track A1 timeout taxonomy): a single
        // EagerBitBlastSolver::solve burns the budget inside
        // CaDiCaL::Closure::extract_and_gates -> extract_gates ->
        // preprocess_quickly — same pathology the regular bit-blast had.
        // Sound: eager bit-blast is candidate-only (validator-gated), and
        // preprocessing only affects SAT speed, not its verdict.
        static const bool nopre =
            std::getenv("XOLVER_NIA_BITBLAST_NOPRE") != nullptr;
        if (nopre) {
            sat->configure("elim",      0);
            sat->configure("subsume",   0);
            sat->configure("vivify",    0);
            sat->configure("probe",     0);
            sat->configure("ternary",   0);
            sat->configure("transred",  0);
            sat->configure("decompose", 0);
        }
        BitBlastEncoder enc(*sat);
        enc.setVarBudget(budget);

        // Per-var width (BLAN collector discipline): both-sided-bounded vars get
        // their EXACT width (value provably fits — bound atom still encoded);
        // unbounded vars get the cascade width K. Bounds are POLARITY-AWARE (only
        // top-level positive conjuncts set them — see markTop in collect), so a
        // negated atom like `(not (= rfc0 0))` never wrongly pins rfc0.
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
                    size_t orIdx = 0;
                    for (ExprId c : e.children) {
                        if (diag && (orIdx % 100) == 0 && e.children.size() > 50)
                            std::cerr << "[EAGER-BB-OR] alt=" << orIdx << "/" << e.children.size()
                                      << " satVars=" << enc.varCount() << "\n";
                        ++orIdx;
                        r = enc.orGate(r, encode(c));
                    }
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

        size_t aIdx = 0;
        for (ExprId a : assertions) {
            if (diag && (aIdx % 100) == 0)
                std::cerr << "[EAGER-BB-ENC] K=" << K << " assertion=" << aIdx
                          << "/" << assertions.size()
                          << " satVars=" << enc.varCount() << "\n";
            ++aIdx;
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
        if (res == SatSolver::SolveResult::Unsat) {
            ++consecutiveUnsat;
            continue;   // wider K (never claim UNSAT)
        }
        consecutiveUnsat = 0;  // reset on any non-Unsat (Unknown counts as continue too)
        if (res != SatSolver::SolveResult::Sat) continue;

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
        if (valid) {
            out.status = Status::Sat;
            out.model = std::move(model);
            // Export Bool model keyed by variable name. Without this, the
            // caller's ModelConverter::evalBool sees missing Bool vars and
            // defaults them to false — wrong Ite-branch selection during
            // reconstruct (test_model_consistency.cpp:104).
            for (const auto& kv : boolVars) {
                const CoreExpr& bex = ir.get(kv.first);
                if (bex.kind != Kind::Variable) continue;
                auto* nm = std::get_if<std::string>(&bex.payload.value);
                if (!nm) continue;
                out.boolModel[*nm] = boolModel[kv.first];
            }
            return out;
        }
        // SAT but candidate failed exact validation (narrow-width artifact) -> wider K.
    }
    return out;   // Unknown
}

} // namespace xolver::bitblast
