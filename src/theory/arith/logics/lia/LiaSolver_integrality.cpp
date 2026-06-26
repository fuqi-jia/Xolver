#include "util/MpqUtils.h"
#include "theory/arith/logics/lia/LiaSolver.h"
#include "util/MpqUtils.h"
#include "util/EnvParam.h"
#include "theory/core/TheoryAtomRegistry.h"
#include "theory/core/TheoryLemmaDatabase.h"
#include "theory/core/TheoryAtomTypes.h"
#include "theory/arith/Reasoner.h"
#include "theory/arith/kernel/linear/SimplexDiseqSplitter.h"
#include "theory/arith/kernel/linear/LinearConstraintNormalizer.h"
#include "theory/arith/logics/lia/GomoryCut.h"
#include "theory/arith/logics/lia/LiaSolverDetail.h"  // isIntegerLinearForm / roundNearest (shared across split TUs)
#include "theory/arith/logics/nia/reasoners/DioReasoner.h"
#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <filesystem>
#include <cstdlib>
#include <sstream>
#include <map>

namespace xolver {

// NOTE: This translation unit was split out of LiaSolver.cpp for readability.
// It compiles into the same xolver_core target and shares the class's
// private state via the declarations in the corresponding header.
// Behavior is byte-identical to the pre-split definitions.

std::optional<TheoryConflict> LiaSolver::checkDioTighten() const {
    auto lcm2 = [](const mpz_class& a, const mpz_class& b) -> mpz_class {
        if (a == 0 || b == 0) return (a == 0) ? abs(b) : abs(a);
        mpz_class g; mpz_gcd(g.get_mpz_t(), a.get_mpz_t(), b.get_mpz_t());
        return abs(a / g * b);
    };
    // Convert `lhs (==) rhs` into the integer form Σc·v + cst (cst = -rhs·d).
    auto toIntForm = [&](const LinearFormKey& lhs, const mpq_class& rhs, DioLinForm& out) -> bool {
        mpz_class d = 1;
        for (const auto& [v, c] : lhs.terms) { (void)v; d = lcm2(d, c.get_den()); }
        d = lcm2(d, rhs.get_den());
        for (const auto& [v, c] : lhs.terms) {
            mpq_class s = c * d;  // now integral
            out.coeffs.emplace_back(v, s.get_num());
        }
        mpq_class r = rhs * d;
        out.cst = -r.get_num();
        return !out.coeffs.empty();
    };

    std::vector<DioLinForm> cons;
    std::map<std::string, DioVarBound> bounds;

    auto addSingleVarBound = [&](const std::string& v, const mpq_class& coeffQ,
                                 const mpq_class& rhsQ, Relation rel, SatLit lit) {
        mpz_class d = lcm2(coeffQ.get_den(), rhsQ.get_den());
        mpq_class aq = coeffQ * d, rq = rhsQ * d;  // materialize (now integral)
        mpz_class a = aq.get_num();
        mpz_class r = rq.get_num();
        if (a == 0) return;
        if (rel == Relation::Lt) { rel = Relation::Leq; r -= 1; }      // integer strict→non-strict
        else if (rel == Relation::Gt) { rel = Relation::Geq; r += 1; }
        if (a < 0) {                                                    // normalize a>0
            a = -a; r = -r;
            if (rel == Relation::Leq) rel = Relation::Geq;
            else if (rel == Relation::Geq) rel = Relation::Leq;
        }
        DioVarBound& bb = bounds[v];
        auto setHi = [&](const mpz_class& ub) {
            if (!bb.hasHi || ub < bb.hi) { bb.hasHi = true; bb.hi = ub; bb.hiReasons = {lit}; } };
        auto setLo = [&](const mpz_class& lb) {
            if (!bb.hasLo || lb > bb.lo) { bb.hasLo = true; bb.lo = lb; bb.loReasons = {lit}; } };
        if (rel == Relation::Leq) {
            mpz_class ub; mpz_fdiv_q(ub.get_mpz_t(), r.get_mpz_t(), a.get_mpz_t()); setHi(ub);
        } else if (rel == Relation::Geq) {
            mpz_class lb; mpz_cdiv_q(lb.get_mpz_t(), r.get_mpz_t(), a.get_mpz_t()); setLo(lb);
        } else if (rel == Relation::Eq) {
            if (r % a == 0) { mpz_class val = r / a; setLo(val); setHi(val); }
        }
        // Neq single-var is an exclusion, not an interval — ignored by the hull.
    };

    for (const auto& a : activeAtoms_) {
        Relation rel = a.rel;
        if (!a.value) {                                                // negated atom
            switch (rel) {
                case Relation::Eq:  rel = Relation::Neq; break;
                case Relation::Neq: rel = Relation::Eq;  break;
                case Relation::Leq: rel = Relation::Gt;  break;
                case Relation::Geq: rel = Relation::Lt;  break;
                case Relation::Lt:  rel = Relation::Geq; break;
                case Relation::Gt:  rel = Relation::Leq; break;
            }
        }
        // Push the constraint as Eq / Neq / Leq / Geq (strict → integer
        // non-strict on the cleared-denominator form). tightenConflict folds the
        // Leq/Geq complementary pairs into lattice equalities.
        DioLinForm f; f.reason = a.lit;
        if (toIntForm(a.lhs, a.rhs, f)) {
            switch (rel) {
                case Relation::Eq:  f.rel = Relation::Eq;  cons.push_back(std::move(f)); break;
                case Relation::Neq: f.rel = Relation::Neq; cons.push_back(std::move(f)); break;
                case Relation::Leq: f.rel = Relation::Leq; cons.push_back(std::move(f)); break;
                case Relation::Geq: f.rel = Relation::Geq; cons.push_back(std::move(f)); break;
                case Relation::Lt:  f.rel = Relation::Leq; f.cst += 1; cons.push_back(std::move(f)); break;  // f<0 ⟺ f+1≤0
                case Relation::Gt:  f.rel = Relation::Geq; f.cst -= 1; cons.push_back(std::move(f)); break;  // f>0 ⟺ f-1≥0
            }
        }
        if (a.lhs.terms.size() == 1)
            addSingleVarBound(a.lhs.terms[0].first, a.lhs.terms[0].second, a.rhs, rel, a.lit);
    }
    for (const auto& d : disequalities_) {                              // separately-tracked ≠
        DioLinForm f; f.reason = d.lit; f.rel = Relation::Neq;
        if (toIntForm(d.lhs, d.rhs, f)) cons.push_back(std::move(f));
    }

    auto conflictOpt = DioReasoner::tightenConflict(cons, bounds);
    if (!conflictOpt) return std::nullopt;
    return TheoryConflict{*conflictOpt};
}

TheoryCheckResult LiaSolver::handleDisequalities(TheoryLemmaStorage& lemmaDb) {
    return handleSimplexDisequalities(
        disequalities_, gs_, lemmaDb,
        [this](const DiseqInfo& d) -> TheoryCheckResult {
            // If the disequality is forced to be false by current bounds
            // (auxVar is fixed to 0), return a precise conflict.
            auto val = gs_.value(d.auxVar);
            auto proved = gs_.proveFixedValue(d.auxVar);
            if (proved && proved->first.isZero()) {
                TheoryConflict tc;
                for (const auto& br : proved->second) {
                    tc.clause.push_back(br.reason);
                }
                tc.clause.push_back(d.lit);
                bool ok = normalizeTheoryClause(tc.clause);
                assert(ok && "complementary literal in disequality conflict");
                (void)ok;
                return TheoryCheckResult::mkConflict(std::move(tc));
            }

            if (d.rhs.get_den() != 1) {
                return TheoryCheckResult::consistent();
            }

            mpz_class g = 0;
            for (const auto& t : d.lhs.terms) {
                const mpq_class& c = t.second;
                if (c.get_den() != 1) {
                    g = 1;
                    break;
                }
                mpz_class a = c.get_num();
                if (a < 0) a = -a;
                if (a == 0) continue;
                if (g == 0) {
                    g = a;
                } else {
                    mpz_class tmp;
                    mpz_gcd(tmp.get_mpz_t(), g.get_mpz_t(), a.get_mpz_t());
                    g = tmp;
                }
            }

            mpz_class c = d.rhs.get_num();

            if (g == 0) {
                if (c == 0) {
                    auto tc = TheoryConflict{{d.lit}};
                    bool ok = normalizeTheoryClause(tc.clause);
                    assert(ok && "complementary literal in gcd conflict");
                    (void)ok;
                    return TheoryCheckResult::mkConflict(std::move(tc));
                }
                return TheoryCheckResult::consistent();
            }

            if (c % g != 0) {
                return TheoryCheckResult::consistent();
            }

            assert(registry_ != nullptr);
            mpq_class leRhs = mpq_class(c - g, 1);
            mpq_class geRhs = mpq_class(c + g, 1);

            auto lit1 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Leq, leRhs, TheoryId::LIA);
            auto lit2 = registry_->getOrCreateLinearBoundAtom(
                d.lhs, Relation::Geq, geRhs, TheoryId::LIA);

            return TheoryCheckResult::mkLemma(
                TheoryLemma{{d.lit.negated(), lit1, lit2}});
        });
}

TheoryCheckResult LiaSolver::checkIntegrality(TheoryLemmaStorage& lemmaDb, TheoryEffort effort) {
    // Cap Gomory cuts per solve so branch-and-bound still terminates AND the
    // tableau doesn't bloat into degeneracy (too many near-degenerate cut rows
    // make the anti-cycling pivot rule blow past the iteration cap -> unknown,
    // the CAV coef-size regression).
    //
    // Default 4 ("cut-and-branch"): measured on the QF_LIA panda regressors
    // (dillig 25-*/45-*, Bromberger *.slack), every cut a fractional SAT node
    // generates perturbs the branching search and mints a fresh bound atom that
    // enlarges the boolean search — on SAT instances cuts are pure overhead and
    // the old default of 32 turned 16-20s base solves into >30s timeouts. A
    // small budget concentrates cuts near the root (where they tighten the
    // initial relaxation, helping UNSAT) and then lets branch-and-bound run
    // undisturbed. Tunable via XOLVER_LIA_CUT_MAXPERSOLVE; raise it for
    // UNSAT-heavy divisions if a differential shows more root cuts help there.
    static const int kMaxCutsPerSolve = []() {
        int v = env::paramInt("XOLVER_LIA_CUT_MAXPERSOLVE", 4);
        return v >= 0 ? v : 4;
    }();
    int bestVar = -1;
    mpq_class bestFrac(-1);

    for (int v : integerVars_) {
        auto val = gs_.value(v);
        if (val.b != 0 || val.a.get_den() != 1) {
            mpq_class frac;
            if (val.b != 0) {
                // Delta-rational: value is a + b·δ where δ is infinitesimal.
                // If b > 0, value is just above a (frac ≈ 1).
                // If b < 0, value is just below a (frac ≈ 0).
                // Use 1/2 as a representative fractional distance.
                frac = mpq_class(1, 2);
            } else {
                // Compute fractional part = |val.a - floor(val.a)|
                mpz_class num = val.a.get_num();
                mpz_class den = val.a.get_den();
                mpz_class f = num / den;  // truncates toward zero
                mpz_class r = num % den;
                mpz_class floorVal;
                if (r == 0) {
                    floorVal = f;
                } else if (num >= 0) {
                    floorVal = f;
                } else {
                    floorVal = f - 1;
                }
                frac = val.a - mpq_class(floorVal, 1);
                if (frac < 0) frac = -frac;
            }
            if (frac > bestFrac) {
                bestFrac = frac;
                bestVar = v;
            }
        }
    }

    if (bestVar != -1) {
        // XOLVER_LIA_REPAIR: before splitting, try to round the LRA relaxation
        // to a nearby integer point and exact-validate it. Only at Full effort
        // (a real, complete relaxation model is in hand). A success short-cuts
        // potentially deep branch-and-bound to an immediate SAT.
        // Soundness gate: repair validates only the LIA atoms + disequalities,
        // NOT Nelson-Oppen interface (dis)equalities. In a combined logic a
        // rounded point could violate an asserted x=y and produce a wrong SAT,
        // so repair only fires when no interface constraints are active (always
        // the case in pure QF_LIA).
        if (repairEnabled_ && effort == TheoryEffort::Full &&
            interfaceEqualities_.empty() && interfaceDisequalities_.empty() &&
            tryIntegralityRepair()) {
            return TheoryCheckResult::consistent();
        }
        // XOLVER_LIA_CUTS / XOLVER_LIA_GMI_CUTS: try a Gomory (or GMI) cut before
        // splitting. A cut tightens the relaxation without branching; capped per
        // solve so branch-and-bound still terminates. Only at Full effort (a real
        // model). GMI implies the cut path so it can be enabled standalone.
        if ((cutsEnabled_ || gmiCutsEnabled_) && effort == TheoryEffort::Full &&
            cutsThisSolve_ < kMaxCutsPerSolve) {
            if (auto cut = generateGomoryCut(bestVar)) {
                if (!lemmaDb.contains(*cut)) {
                    ++cutsThisSolve_;
                    return TheoryCheckResult::mkLemma(std::move(*cut));
                }
            }
        }
        assert(registry_ != nullptr);
        return TheoryCheckResult::mkLemma(buildBranchSplitLemma(bestVar, gs_.value(bestVar)));
    }
    return TheoryCheckResult::consistent();
}

bool LiaSolver::pointSatisfiesAll(
    const std::unordered_map<std::string, mpq_class>& pt) const {
    auto eval = [&](const LinearFormKey& lhs, mpq_class& out) -> bool {
        out = 0;
        for (const auto& [name, coeff] : lhs.terms) {
            auto it = pt.find(name);
            if (it == pt.end()) return false;  // value unknown -> cannot validate
            out += coeff * it->second;
        }
        return true;
    };
    for (const auto& a : activeAtoms_) {
        mpq_class f;
        if (!eval(a.lhs, f)) return false;
        Relation rel = a.value ? a.rel : negateRelation(a.rel);
        bool ok;
        switch (rel) {
            case Relation::Eq:  ok = (f == a.rhs); break;
            case Relation::Neq: ok = (f != a.rhs); break;
            case Relation::Lt:  ok = (f <  a.rhs); break;
            case Relation::Leq: ok = (f <= a.rhs); break;
            case Relation::Gt:  ok = (f >  a.rhs); break;
            case Relation::Geq: ok = (f >= a.rhs); break;
            default:            ok = false; break;
        }
        if (!ok) return false;
    }
    for (const auto& d : disequalities_) {
        mpq_class f;
        if (!eval(d.lhs, f)) return false;
        if (f == d.rhs) return false;  // disequality violated
    }
    return true;
}

bool LiaSolver::tryIntegralityRepair() {
    // Collect (name, floor, ceil, nearest) for every original integer variable.
    struct VarRound {
        std::string name;
        mpq_class lo, hi, nearest;
    };
    std::vector<VarRound> vr;
    vr.reserve(integerVars_.size());
    for (int v : integerVars_) {
        std::string name = manager_.getVarName(v);
        if (name.empty()) continue;            // aux/slack vars are determined
        const mpq_class& a = gs_.value(v).a;
        mpz_class fl, cl;
        mpz_fdiv_q(fl.get_mpz_t(), a.get_num().get_mpz_t(), a.get_den().get_mpz_t());
        mpz_cdiv_q(cl.get_mpz_t(), a.get_num().get_mpz_t(), a.get_den().get_mpz_t());
        vr.push_back({name, mpq_class(fl), mpq_class(cl), mpq_class(roundNearest(a))});
    }
    if (vr.empty()) return false;

    auto tryPoint = [&](const std::unordered_map<std::string, mpq_class>& pt) -> bool {
        if (!pointSatisfiesAll(pt)) return false;
        repairModel_ = pt;
        return true;
    };
    auto buildUniform = [&](int which) {  // 0=nearest, 1=floor, 2=ceil
        std::unordered_map<std::string, mpq_class> pt;
        pt.reserve(vr.size());
        for (const auto& r : vr) pt[r.name] = (which == 1 ? r.lo : which == 2 ? r.hi : r.nearest);
        return pt;
    };

    bool ok = false;
    // 1) Round-to-nearest, then the all-floor / all-ceil corners.
    if (tryPoint(buildUniform(0)) || tryPoint(buildUniform(1)) || tryPoint(buildUniform(2))) {
        ok = true;
    } else {
        // 2) One-variable flip neighbourhood around the nearest point: flip each
        //    single variable to its other neighbour (floor<->ceil). Bounded by
        //    #vars, catches the common "one coordinate rounded the wrong way".
        auto base = buildUniform(0);
        for (const auto& r : vr) {
            mpq_class other = (base[r.name] == r.lo) ? r.hi : r.lo;
            if (other == base[r.name]) continue;  // already integral
            mpq_class saved = base[r.name];
            base[r.name] = other;
            if (tryPoint(base)) { ok = true; break; }
            base[r.name] = saved;
        }
    }
    return ok;
}

bool LiaSolver::isSimplexVarInteger(int idx) const {
    std::string nm = manager_.getVarName(idx);
    if (!nm.empty()) {
        // Original variable: integer iff registered as an integer variable.
        return integerVars_.count(idx) > 0;
    }
    // Auxiliary variable s = Σ c_k * v_k - rhs: integer iff every c_k and rhs
    // are integers and every v_k is an integer variable.
    LinearFormKey form;
    mpq_class auxRhs;
    if (!manager_.auxForm(idx, form, auxRhs)) return false;
    if (auxRhs.get_den() != 1) return false;
    for (const auto& [vn, c] : form.terms) {
        if (c.get_den() != 1) return false;
        int vi = manager_.findVarIndex(vn);
        if (vi < 0 || integerVars_.count(vi) == 0) return false;
    }
    return true;
}

std::optional<TheoryLemma> LiaSolver::generateGomoryCut(int xi) {
    if (!registry_) return std::nullopt;
    if (!gs_.isBasic(xi)) return std::nullopt;     // need a tableau row
    int r = gs_.basicRowOfVar(xi);
    const SparseRow& row = gs_.tableau().row(r);

    DeltaRational beta = gs_.value(xi);
    if (beta.b != 0) return std::nullopt;          // delta-valued: skip
    mpq_class f0 = gmiFractionalPart(beta.a);
    if (f0 == 0) return std::nullopt;              // not actually fractional

    // x_i = beta_i + Σ_j chat_j y_j, y_j = (x_j - bound_j), each nonbasic at a
    // bound. chat_j = +a_ij at lower, -a_ij at upper.
    struct NbInfo { int var; bool atLower; mpq_class bound; SatLit reason; };
    std::vector<GmiNonbasicTerm> terms;
    std::vector<NbInfo> nb;
    for (const auto& e : row.entries) {
        int xj = e.col;
        const mpq_class& aij = e.coeff;
        if (aij == 0) continue;
        auto st = gs_.varState(xj);
        DeltaRational vj = gs_.value(xj);
        bool atLower = st.lower.bound.isFinite() && vj == st.lower.bound.value;
        bool atUpper = !atLower && st.upper.bound.isFinite() && vj == st.upper.bound.value;
        if (!atLower && !atUpper) return std::nullopt;       // free nonbasic: no y >= 0
        const BoundInfo& bi = atLower ? st.lower : st.upper;
        if (bi.bound.value.b != 0) return std::nullopt;      // strict/delta bound: skip
        if (!bi.reason.has_value()) return std::nullopt;     // need reason for explanation
        mpq_class boundVal = bi.bound.value.a;
        mpq_class chat = atLower ? aij : -aij;
        bool yInt = isSimplexVarInteger(xj) && (boundVal.get_den() == 1);
        terms.push_back({chat, yInt});
        nb.push_back({xj, atLower, boundVal, *bi.reason});
    }
    if (terms.empty()) return std::nullopt;

    // GMI (XOLVER_LIA_GMI_CUTS) folds continuous nonbasics into the cut instead
    // of bailing; the pure fractional cut requires every term integer. Both
    // return the same {gamma>=0, rhs>0} shape, so the back-substitution below is
    // shared. The coefficient bit-cap further down rejects any blown-up cut
    // (GMI's f0/(1-f0) factor can compound rationals) so the exact simplex never
    // bogs down.
    auto cutOpt = gmiCutsEnabled_ ? deriveGmiCut(f0, terms)
                                  : deriveGomoryCut(f0, terms);
    if (!cutOpt) return std::nullopt;              // non-integer term / vacuous

    // Re-express Σ gamma_j y_j >= R over original variables:
    //   Σ tau_j x_j >= R + Σ tau_j bound_j (+ aux form-constant adjustment),
    //   tau_j = +gamma_j (at lower) / -gamma_j (at upper).
    std::unordered_map<std::string, mpq_class> coeff;
    mpq_class rhsFinal = cutOpt->rhs;
    std::vector<SatLit> reasons;
    for (size_t j = 0; j < nb.size(); ++j) {
        const mpq_class& gamma = cutOpt->gamma[j];
        if (gamma == 0) continue;                  // absent term: bound not needed
        mpq_class tau = nb[j].atLower ? gamma : mpq_class(-gamma);
        rhsFinal += tau * nb[j].bound;
        std::string nm = manager_.getVarName(nb[j].var);
        if (!nm.empty()) {
            coeff[nm] += tau;
        } else {
            LinearFormKey form;
            mpq_class auxRhs;
            if (!manager_.auxForm(nb[j].var, form, auxRhs)) return std::nullopt;
            for (const auto& [vn, c] : form.terms) coeff[vn] += tau * c;
            rhsFinal += tau * auxRhs;
        }
        reasons.push_back(nb[j].reason);
    }

    LinearFormKey cutForm;
    for (const auto& [vn, c] : coeff) if (c != 0) cutForm.terms.push_back({vn, c});
    if (cutForm.terms.empty()) return std::nullopt;  // degenerate constant cut
    std::sort(cutForm.terms.begin(), cutForm.terms.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    // Cut-coefficient size cap: reject blown-up cuts. On large-coefficient
    // instances (CAV coef-size) the Gomory fractional parts compound into huge
    // rationals; such cuts bog down the exact-rational simplex (it hits its
    // iteration cap -> unknown) without improving the bound. Rejecting them lets
    // the solver fall back to branching, which is fast. Tunable for A/B.
    {
        static const int kMaxBits = []() {
            int v = env::paramInt("XOLVER_LIA_CUT_MAXBITS", 8);
            return v > 0 ? v : 8;
        }();
        auto bits = [](const mpq_class& q) -> size_t {
            return std::max(mpz_sizeinbase(q.get_num().get_mpz_t(), 2),
                            mpz_sizeinbase(q.get_den().get_mpz_t(), 2));
        };
        size_t mx = bits(rhsFinal);
        for (const auto& [vn, c] : cutForm.terms) mx = std::max(mx, bits(c));
        if (mx > static_cast<size_t>(kMaxBits)) return std::nullopt;
    }

    SatLit cutLit = registry_->getOrCreateLinearBoundAtom(
        cutForm, Relation::Geq, rhsFinal, TheoryId::LIA);

    // Explanation-aware lemma: (Σ reasons) -> cut, i.e. clause {¬reasons, cutLit}.
    std::vector<SatLit> clause;
    clause.reserve(reasons.size() + 1);
    for (SatLit rr : reasons) clause.push_back(rr.negated());
    clause.push_back(cutLit);
    std::sort(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        return a.var < b.var || (a.var == b.var && a.sign < b.sign);
    });
    clause.erase(std::unique(clause.begin(), clause.end(), [](SatLit a, SatLit b) {
        return a.var == b.var && a.sign == b.sign;
    }), clause.end());
    return TheoryLemma{clause};
}

TheoryLemma LiaSolver::buildBranchSplitLemma(int var, const DeltaRational& val) {
    mpq_class q = val.a;
    mpz_class num = q.get_num();
    mpz_class den = q.get_den();

    mpq_class floorVal;
    mpq_class ceilVal;

    if (den == 1) {
        if (val.b > 0) {
            // value = a + epsilon, strictly greater than a
            floorVal = q;
            ceilVal = mpq_class(num + 1, 1);
        } else if (val.b < 0) {
            // value = a - epsilon, strictly less than a
            floorVal = mpq_class(num - 1, 1);
            ceilVal = q;
        } else {
            floorVal = q;
            ceilVal = q;
        }
    } else {
        mpz_class f = num / den;
        mpz_class r = num % den;
        if (r == 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f, 1);
        } else if (num >= 0) {
            floorVal = mpq_class(f, 1);
            ceilVal = mpq_class(f + 1, 1);
        } else {
            floorVal = mpq_class(f - 1, 1);
            ceilVal = mpq_class(f, 1);
        }
    }

    std::string name = manager_.getVarName(var);
    if (name.empty()) {
        return TheoryLemma{};
    }

    LinearFormKey form;
    form.terms.push_back({name, mpq_class(1)});

    auto litLo = registry_->getOrCreateLinearBoundAtom(form, Relation::Leq, floorVal, TheoryId::LIA);
    auto litHi = registry_->getOrCreateLinearBoundAtom(form, Relation::Geq, ceilVal, TheoryId::LIA);

    return TheoryLemma{{litLo, litHi}};
}

} // namespace xolver
