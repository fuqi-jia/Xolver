#include "theory/arith/nra/NraSquareSolver.h"

#include "theory/arith/poly/PolynomialKernel.h"
#include "theory/arith/poly/RationalPolynomial.h"

#include <cstdio>
#include <cstdlib>
#include <map>
#include <string>
#include <unordered_set>
#include <utility>

namespace xolver {

bool rationalSqrt(const mpq_class& c, mpq_class& root) {
    if (sgn(c) < 0) return false;
    mpz_class num = c.get_num();
    mpz_class den = c.get_den();   // > 0 in canonical form
    mpz_class sn, sd;
    mpz_sqrt(sn.get_mpz_t(), num.get_mpz_t());   // floor sqrt
    mpz_sqrt(sd.get_mpz_t(), den.get_mpz_t());
    if (sn * sn != num) return false;
    if (sd * sd != den) return false;
    root = mpq_class(sn, sd);
    root.canonicalize();
    return true;
}

std::vector<SquareEquality> detectSquareEqualities(
    const std::vector<std::pair<PolyId, Relation>>& eqs, PolynomialKernel& kernel) {
    std::vector<SquareEquality> out;
    for (size_t i = 0; i < eqs.size(); ++i) {
        if (eqs[i].second != Relation::Eq) continue;
        const PolyId p = eqs[i].first;
        const std::vector<std::string> vars = kernel.variables(p);
        if (vars.size() != 1) continue;                 // must be univariate in x
        auto co = kernel.getIntegerCoefficients(p, vars[0]);  // high -> low degree
        if (!co || co->size() != 3) continue;           // not exactly degree 2
        if ((*co)[1] != 0) continue;                    // an x^1 term -> not a pure square eq
        const mpz_class& A = (*co)[0];                  // x^2 coefficient
        const mpz_class& B0 = (*co)[2];                 // constant term
        if (A == 0) continue;
        mpq_class c(-B0, A);                             // x^2 = -B0 / A
        c.canonicalize();
        SquareEquality sq;
        sq.var = kernel.getOrCreateVar(vars[0]);
        sq.squaredValue = c;
        sq.constraintIndex = i;
        out.push_back(std::move(sq));
    }
    return out;
}

PolyId substituteVarWithVar(PolyId p, VarId from, VarId to, PolynomialKernel& kernel) {
    if (from == to) return p;
    const PolyId divisor = kernel.sub(kernel.mkVar(from), kernel.mkVar(to));  // from - to
    auto pr = kernel.pseudoRemainderWithScale(p, divisor, from);
    // (from - to) is monic in `from`, so the pseudo-remainder is exact substitution
    // (scaleFactor 1, exponent 0). Fall back to p if the kernel could not reduce.
    return pr.ok() ? pr.remainder : p;
}

CollapsedRoots collapseAlgebraicRoots(const std::vector<SquareRoot>& roots) {
    CollapsedRoots out;
    // Key an algebraic generator by its (c, sign): equal => the SAME real number.
    std::map<std::pair<mpq_class, int>, VarId> repByKey;
    for (const auto& r : roots) {
        if (!r.feasible) { out.feasible = false; continue; }
        if (r.isRational) { out.rationalVars[r.var] = r.rationalValue; continue; }
        const std::pair<mpq_class, int> key{r.squaredValue, r.sign};
        auto it = repByKey.find(key);
        if (it == repByKey.end()) {
            repByKey.emplace(key, r.var);
            out.generators.push_back(r.var);
            out.genSquared[r.var] = r.squaredValue;
            out.genSign[r.var] = r.sign;
            out.aliasOf[r.var] = r.var;            // representative aliases to itself
        } else {
            out.aliasOf[r.var] = it->second;       // collapse onto the representative
        }
    }
    return out;
}

int signOfRootExpr(const mpq_class& a, const mpq_class& b, const mpq_class& c) {
    const int sa = sgn(a);
    const int sb = sgn(b);
    if (sa == 0) return sb;          // pure constant b
    if (sb == 0) return sa;          // pure a*sqrt(c), sqrt(c) > 0
    if (sa > 0 && sb > 0) return 1;
    if (sa < 0 && sb < 0) return -1;
    // Mixed signs: a*sqrt(c) + b. Sign = sign(a) * sign(a^2*c - b^2).
    //   a>0,b<0:  >0 iff a*sqrt(c) > |b| iff a^2*c > b^2  => sign(disc)
    //   a<0,b>0:  >0 iff b > |a|*sqrt(c) iff b^2 > a^2*c  => -sign(disc) = sign(a)*sign(disc)
    const mpq_class disc = a * a * c - b * b;
    return sa * sgn(disc);
}

std::optional<int> signOfPolyAtGenerator(const RationalPolynomial& rp, VarId genVar,
                                         const mpq_class& c, int genSign) {
    mpq_class aGen = 0;   // coefficient of genVar after reduction mod genVar^2 = c
    mpq_class b = 0;      // constant part
    for (const auto& [key, coeff] : rp.terms()) {
        int deg = 0;
        for (const auto& [v, e] : key) {
            if (v != genVar) return std::nullopt;   // not univariate in the generator
            deg += e;
        }
        mpq_class cp = 1;                            // c^(deg/2)
        for (int j = 0; j < deg / 2; ++j) cp *= c;
        if (deg % 2 == 0) b += coeff * cp;
        else aGen += coeff * cp;                     // genVar^deg -> cp * genVar
    }
    // genVar = genSign * sqrt(c), so the sqrt(c) coefficient is aGen * genSign.
    const mpq_class a = (genSign < 0) ? -aGen : aGen;
    return signOfRootExpr(a, b, c);
}

PolyId substituteVarWithPoly(PolyId p, VarId var, PolyId valuePoly, PolynomialKernel& kernel) {
    // Horner evaluation p(var := valuePoly) = sum_i co[i] * valuePoly^i, using only
    // add/mul (NOT pseudo-remainder, which mis-handles a value poly whose variables
    // outrank `var` and can return 0).
    auto rp = RationalPolynomial::fromPolyId(p, kernel);
    if (!rp) return p;
    std::vector<RationalPolynomial> co = rp->coefficients(var);  // [c0, c1, ..., cd]
    if (co.size() <= 1) return p;                                // var absent
    PolyId result = co.back().toPolyId(kernel);
    for (int i = static_cast<int>(co.size()) - 2; i >= 0; --i)
        result = kernel.add(kernel.mul(result, valuePoly), co[i].toPolyId(kernel));
    return result;
}

namespace {

// Sign-bound hint: a strict/non-strict single-variable bound "x rel 0" (b == 0)
// fixes whether x is taken as the + or - square root. Returns 0 if not such a bound.
int signHintFromBound(PolyId p, Relation rel, PolynomialKernel& kernel, VarId& boundVar) {
    const auto vars = kernel.variables(p);
    if (vars.size() != 1) return 0;
    auto co = kernel.getIntegerCoefficients(p, vars[0]);
    if (!co || co->size() != 2) return 0;     // not degree 1
    if ((*co)[1] != 0) return 0;              // a*x + b, need b == 0
    const int a = ((*co)[0] > 0) ? 1 : -1;
    boundVar = kernel.getOrCreateVar(vars[0]);
    // a*x rel 0  =>  x rel' 0.
    if (rel == Relation::Gt || rel == Relation::Geq) return a > 0 ? +1 : -1;  // x > / >= 0
    if (rel == Relation::Lt || rel == Relation::Leq) return a > 0 ? -1 : +1;
    return 0;
}

}  // namespace

// One attempt of the cascade with a fixed instantiation `seed` of free parameters
// (empty = no instantiation). Factored out so trySquareCascade can retry over a few
// candidate rationals for a single free geometric parameter (e.g. the base length in
// an IsoTriangle construction): once that parameter is rational, the remaining
// `v^2 = f(param)` equalities collapse to univariate squares the cascade already
// handles. Every attempt re-VALIDATES the whole model, so a seeded sat is still sound.
static bool attemptSquareCascade(const std::vector<std::pair<PolyId, Relation>>& cons,
                      PolynomialKernel& kernel,
                      const std::unordered_map<VarId, mpq_class>& seed,
                      std::vector<std::pair<VarId, RealValue>>* modelOut,
                      std::unordered_set<VarId>* unresolvedOut = nullptr) {
    // --- collect equalities / inequalities / sign hints --------------------------
    std::vector<PolyId> eqs;
    std::unordered_map<VarId, int> signHint;
    for (const auto& [p, rel] : cons) {
        if (rel == Relation::Eq) { eqs.push_back(p); continue; }
        VarId bv;
        int h = signHintFromBound(p, rel, kernel, bv);
        if (h != 0 && !signHint.count(bv)) signHint[bv] = h;
    }

    std::unordered_map<VarId, mpq_class> rationalVal = seed;   // free-parameter instantiation
    std::unordered_map<VarId, VarId> aliasOf;              // algebraic var -> generator
    std::unordered_map<VarId, RationalPolynomial> derivedVal;  // derived var -> EXACT value (in gen)
    VarId genVar = NullVar; mpq_class genC; int genSign = +1;

    auto degIn = [&](PolyId p, VarId v) -> int {
        auto d = kernel.degree(p, kernel.varName(v));
        return d ? *d : 0;
    };
    // Reduce a polynomial univariate in genVar modulo genVar^2 = c to aGen*genVar + b.
    // Pure term-wise (no libpoly pseudo-remainder — that crash class is exactly what
    // the cascade must dodge). Terms mentioning any other variable are skipped.
    auto reduceUni = [&](const RationalPolynomial& rp) -> std::pair<mpq_class, mpq_class> {
        mpq_class aGen = 0, b = 0;
        for (const auto& [key, coeff] : rp.terms()) {
            int deg = 0; bool other = false;
            for (const auto& [v, e] : key) { if (v != genVar) other = true; else deg += e; }
            if (other) continue;
            mpq_class cp = 1;
            for (int j = 0; j < deg / 2; ++j) cp *= genC;
            if (deg % 2 == 0) b += coeff * cp; else aGen += coeff * cp;
        }
        return {aGen, b};
    };
    // Exact PolyId-level substitution of rationals (scale > 0, sign-safe) + aliases
    // (monic divisor, exact). The DERIVED variables are substituted later in
    // RationalPolynomial space so their rational coefficients survive (toPolyId
    // clears denominators).
    auto applySubst = [&](PolyId p) -> PolyId {
        for (const auto& [v, val] : rationalVal)
            if (degIn(p, v) > 0)
                if (auto q = kernel.substituteRational(p, v, val)) p = *q;
        for (const auto& [v, g] : aliasOf)
            if (degIn(p, v) > 0) p = substituteVarWithVar(p, v, g, kernel);
        return p;
    };
    // Horner substitution of a variable by a RationalPolynomial value (exact, and
    // ORDERING-INDEPENDENT — unlike the kernel's pseudo-remainder, which silently
    // mis-substitutes depending on libpoly's variable order).
    auto substRpDerived = [&](RationalPolynomial rp, VarId var, const RationalPolynomial& val) {
        std::vector<RationalPolynomial> co = rp.coefficients(var);
        if (co.size() <= 1) return rp;
        RationalPolynomial result = co.back();
        for (int i = static_cast<int>(co.size()) - 2; i >= 0; --i)
            result = result * val + co[i];
        result.normalize();
        return result;
    };
    // Apply ALL known substitutions (rationals, aliases, derived) in exact
    // RationalPolynomial space.
    auto applySubstRp = [&](RationalPolynomial rp) -> RationalPolynomial {
        for (const auto& [v, val] : rationalVal) rp = rp.substituteRational(v, val);
        for (const auto& [v, g] : aliasOf) {
            RationalPolynomial gv; gv.addVar(g, 1, mpq_class(1)); gv.normalize();
            rp = substRpDerived(rp, v, gv);
        }
        for (const auto& [v, mv] : derivedVal) rp = substRpDerived(rp, v, mv);
        rp.normalize();
        return rp;
    };


    // --- iterative triangular solve of square + linear equalities ----------------
    std::vector<char> done(eqs.size(), 0);
    bool progress = true;
    while (progress) {
        progress = false;
        for (size_t j = 0; j < eqs.size(); ++j) {
            if (done[j]) continue;
            PolyId p = applySubst(eqs[j]);
            const auto vars = kernel.variables(p);
            if (vars.empty()) {
                if (!kernel.isZero(p)) return false;   // 0 = nonzero  => UNSAT branch
                done[j] = 1; progress = true; continue;
            }
            if (vars.size() != 1) continue;            // still multi-var; revisit later
            const std::string& vn = vars[0];
            const VarId x = kernel.getOrCreateVar(vn);
            auto co = kernel.getIntegerCoefficients(p, vn);
            if (!co) continue;
            if (co->size() == 2) {                     // a*x + b = 0  (linear)
                const mpz_class& a = (*co)[0];
                const mpz_class& b = (*co)[1];
                if (a == 0) continue;
                rationalVal[x] = mpq_class(-b, a);
                rationalVal[x].canonicalize();
                done[j] = 1; progress = true;
            } else if (co->size() == 3 && (*co)[1] == 0) {   // a*x^2 + b = 0
                const mpz_class& a = (*co)[0];
                const mpz_class& b = (*co)[2];
                if (a == 0) continue;
                mpq_class c(-b, a); c.canonicalize();
                if (sgn(c) < 0) return false;          // x^2 < 0 => UNSAT branch
                const int s = signHint.count(x) ? signHint[x] : +1;
                mpq_class root;
                if (rationalSqrt(c, root)) {
                    rationalVal[x] = mpq_class(s) * root;
                } else if (genVar == NullVar) {
                    genVar = x; genC = c; genSign = s;
                } else if (c == genC && s == genSign) {
                    aliasOf[x] = genVar;
                } else {
                    // RATIONAL-MULTIPLE generator: if c = r^2 * genC then sqrt(c) =
                    // r*sqrt(genC) lives in the SAME field Q(sqrt genC), so x = s*sqrt(c)
                    // = (s*r*genSign) * gen  (gen = genSign*sqrt(genC)). Record x as a
                    // rational multiple of the generator (via derivedVal), NOT a new
                    // generator — collapses e.g. sqrt(2) and sqrt(1/2) onto one generator.
                    mpq_class ratio = c / genC; ratio.canonicalize();
                    mpq_class r;
                    if (rationalSqrt(ratio, r)) {
                        const mpq_class scale = mpq_class(s) * r * mpq_class(genSign);
                        RationalPolynomial mv; mv.addVar(genVar, 1, scale); mv.normalize();
                        derivedVal[x] = std::move(mv);
                    } else {
                        return false;                  // genuinely 2nd distinct generator
                    }
                }
                done[j] = 1; progress = true;
            }
            // higher degree / multi-term: leave for the derived-var phase
        }
    }

    auto onlyGen = [&](const RationalPolynomial& q) {
        for (VarId v : q.variables()) if (v != genVar) return false;
        return true;
    };
    // --- derive remaining variables from linear-in-them equalities ---------------
    // Iterate to a fixpoint so CHAINS resolve (e.g. w2 = v12+v13 then m = 1/w2):
    // each newly-derived variable is substituted into the rest on the next pass.
    bool dprogress = true;
    while (dprogress) {
    dprogress = false;
    for (size_t j = 0; j < eqs.size(); ++j) {
        if (done[j]) continue;
        auto rp0 = RationalPolynomial::fromPolyId(eqs[j], kernel);
        if (!rp0) continue;
        RationalPolynomial rps = applySubstRp(*rp0);   // exact rationals + aliases + derived
        // pick the unassigned variable that is NOT the generator
        VarId d = NullVar;
        for (VarId v : rps.variables()) {
            if (v == genVar) continue;
            if (d != NullVar) { d = NullVar; break; }   // more than one unassigned -> give up
            d = v;
        }
        if (d == NullVar) continue;
        std::vector<RationalPolynomial> co = rps.coefficients(d);   // [C, A] low->high
        if (co.size() != 2) continue;                              // must be linear in d
        if (!onlyGen(co[1]) || !onlyGen(co[0])) continue;
        // d = -C / A. Reduce A, C mod genVar^2 = genC to A = aA*g + bA, C = cA*g + cB,
        // then RATIONALIZE by the conjugate of A:  -C/A = -C*conj(A) / (A*conj(A)),
        // where A*conj(A) = bA^2 - aA^2*genC is RATIONAL, and -C*conj(A) reduces (mod
        // g^2=genC) to P0 + P1*g. So d = (P0 + P1*g)/denom is a POLYNOMIAL in g — even
        // when A itself still depends on the generator (the sqrt cancels). This is what
        // lets the cascade derive m for the whole Geogebra cluster, not just the case
        // where A happens to collapse to a constant.
        RationalPolynomial mv;
        if (genVar != NullVar) {
            auto rA = reduceUni(co[1]);
            auto rC = reduceUni(co[0]);
            const mpq_class aA = rA.first, bA = rA.second, cA = rC.first, cB = rC.second;
            const mpq_class denom = bA * bA - aA * aA * genC;       // A * conj(A)
            if (sgn(denom) == 0) continue;                         // A vanishes at the root
            const mpq_class P0 = cA * aA * genC - cB * bA;          // -C*conj(A), const part
            const mpq_class P1 = cB * aA - cA * bA;                 // -C*conj(A), g coeff
            if (sgn(P1) != 0) mv.addVar(genVar, 1, P1 / denom);
            mv.addConstant(P0 / denom);
        } else {
            if (!co[1].isConstant() || !co[0].isConstant()) continue;
            const mpq_class A = co[1].constantValue();
            if (sgn(A) == 0) continue;
            mv.addConstant(-co[0].constantValue() / A);
        }
        mv.normalize();
        derivedVal[d] = std::move(mv);
        done[j] = 1;
        dprogress = true;
    }
    }

    // Report the still-unresolved variables (in some constraint but assigned no value)
    // so the caller can guide a multi-parameter instantiation.
    if (unresolvedOut) {
        unresolvedOut->clear();
        std::unordered_set<VarId> assigned;
        for (const auto& kv : rationalVal) assigned.insert(kv.first);
        for (const auto& kv : aliasOf)     assigned.insert(kv.first);
        for (const auto& kv : derivedVal)  assigned.insert(kv.first);
        if (genVar != NullVar) assigned.insert(genVar);
        for (const auto& [p, rel] : cons)
            for (const auto& vn : kernel.variables(p)) {
                VarId v = kernel.getOrCreateVar(vn);
                if (!assigned.count(v)) unresolvedOut->insert(v);
            }
    }

    // --- VALIDATE every original constraint over the single generator ------------
    auto signOfReduced = [&](PolyId p) -> std::optional<int> {
        auto rp = RationalPolynomial::fromPolyId(p, kernel);
        if (!rp) return std::nullopt;
        RationalPolynomial r = applySubstRp(*rp);   // rationals + aliases + derived (exact)
        if (r.isConstant()) return sgn(r.constantValue());
        if (genVar == NullVar) return std::nullopt;
        return signOfPolyAtGenerator(r, genVar, genC, genSign);
    };
    for (const auto& [p, rel] : cons) {
        auto s = signOfReduced(p);
        if (!s) return false;                       // inconclusive => bail (sound)
        bool ok = false;
        switch (rel) {
            case Relation::Eq:  ok = (*s == 0); break;
            case Relation::Neq: ok = (*s != 0); break;
            case Relation::Lt:  ok = (*s < 0);  break;
            case Relation::Leq: ok = (*s <= 0); break;
            case Relation::Gt:  ok = (*s > 0);  break;
            case Relation::Geq: ok = (*s >= 0); break;
        }
        if (!ok) return false;                         // model violates a constraint
    }

    // Defer the SIMPLE single-algebraic case (no collapsed alias, no derived var) to
    // the existing CDCAC path, which already solves it and formats getModel correctly.
    // The cascade's unique value is the COLLAPSE (equal roots) + DERIVATION that the
    // ≥2-algebraic Lazard tower bails on (the Geogebra cluster).
    if (aliasOf.empty() && derivedVal.empty()) return false;

    // --- build the complete model (every var) so the Solver's validator accepts it --
    if (modelOut) {
        modelOut->clear();
        for (const auto& [v, val] : rationalVal)
            modelOut->emplace_back(v, RealValue::fromMpq(val));
        // TIGHT rational bracket for sqrt(genC): for a non-square genC, genC != 1, so
        //   genC < 1  =>  genC < sqrt(genC) < 1
        //   genC > 1  =>  1   < sqrt(genC) < genC
        // A tight isolating interval keeps the downstream algebraic-number refinement
        // cheap (a loose [0, genC+1] forces many bisections of a big-coefficient poly).
        const mpq_class sqLo = (genC < 1) ? genC : mpq_class(1);
        const mpq_class sqHi = (genC < 1) ? mpq_class(1) : genC;
        auto genRealValue = [&]() {
            const mpz_class num = genC.get_num(), den = genC.get_den();
            AlgebraicNumber an;
            an.coefficients = {-num, mpz_class(0), den};   // den*x^2 - num, root genSign*sqrt(genC)
            if (genSign > 0) { an.lower = sqLo; an.upper = sqHi; }
            else { an.lower = -sqHi; an.upper = -sqLo; }
            return RealValue::fromAlgebraic(std::move(an));
        };
        if (genVar != NullVar) {
            modelOut->emplace_back(genVar, genRealValue());
            for (const auto& [v, g] : aliasOf) modelOut->emplace_back(v, genRealValue());  // = generator
        }
        // Derived d = ap*gen + bp  (a number in Q(sqrt genC)). With gen = genSign*sqrt(genC),
        // d = Aeff*sqrt(genC) + bp where Aeff = ap*genSign.
        for (const auto& [d, mv] : derivedVal) {
            auto rd = reduceUni(mv);
            const mpq_class ap = rd.first, bp = rd.second;
            if (sgn(ap) == 0) { modelOut->emplace_back(d, RealValue::fromMpq(bp)); continue; }
            const mpq_class Aeff = (genSign < 0) ? -ap : ap;   // coefficient of sqrt(genC)
            // minimal poly: x^2 - 2 bp x + (bp^2 - Aeff^2 genC).
            mpq_class c0 = bp * bp - Aeff * Aeff * genC, c1 = mpq_class(-2) * bp, c2 = 1;
            mpz_class L = c0.get_den();
            mpz_lcm(L.get_mpz_t(), L.get_mpz_t(), c1.get_den().get_mpz_t());
            mpz_lcm(L.get_mpz_t(), L.get_mpz_t(), c2.get_den().get_mpz_t());
            mpz_class a0 = mpq_class(c0 * L).get_num(), a1 = mpq_class(c1 * L).get_num(),
                      a2 = mpq_class(c2 * L).get_num();
            mpz_class g = a0;                              // GCD-reduce to keep coefficients small
            mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), a1.get_mpz_t());
            mpz_gcd(g.get_mpz_t(), g.get_mpz_t(), a2.get_mpz_t());
            if (sgn(g) != 0 && g != 1) { a0 /= g; a1 /= g; a2 /= g; }
            AlgebraicNumber an;
            an.coefficients = {a0, a1, a2};
            // d in [bp + Aeff*sqLo, bp + Aeff*sqHi] (ordered by sign of Aeff). Excludes the
            // conjugate root bp - Aeff*sqrt(genC) since sqLo > 0.
            if (sgn(Aeff) > 0) { an.lower = bp + Aeff * sqLo; an.upper = bp + Aeff * sqHi; }
            else { an.lower = bp + Aeff * sqHi; an.upper = bp + Aeff * sqLo; }
            modelOut->emplace_back(d, RealValue::fromAlgebraic(std::move(an)));
        }
    }
    return true;
}

bool trySquareCascade(const std::vector<std::pair<PolyId, Relation>>& cons,
                      PolynomialKernel& kernel,
                      std::vector<std::pair<VarId, RealValue>>* modelOut) {
    // First, the un-seeded cascade (pure triangular square systems).
    std::unordered_set<VarId> u0;
    if (attemptSquareCascade(cons, kernel, {}, modelOut, &u0)) return true;

    // FREE-PARAMETER instantiation. Many geometric sat instances fix every variable
    // to a square root of a LINEAR expression in one free parameter p (e.g. an
    // IsoTriangle base length): v17^2 = v14^2 + 9/16, v18^2 = 4 v14^2, ... — none of
    // these is univariate until p is fixed, so the un-seeded cascade finds no seed.
    // Try p := a few small rationals (sign-respecting); once p is rational every such
    // equality is a univariate square the cascade solves, and the full model is
    // re-validated (sound: only a genuinely satisfying instantiation returns true).
    static const mpq_class kCands[] = {
        mpq_class(1), mpq_class(1, 2), mpq_class(2), mpq_class(1, 4), mpq_class(3, 2),
        mpq_class(3), mpq_class(1, 3), mpq_class(3, 4), mpq_class(5, 4), mpq_class(2, 3),
        // NEGATIVE candidates: a free parameter is often a coordinate, not a length,
        // and can be negative (e.g. an IsoTriangle apex below the base, Bottema4_2a).
        mpq_class(-1), mpq_class(-1, 2), mpq_class(-2), mpq_class(-1, 4), mpq_class(-3, 2),
        mpq_class(-3),
    };
    // Candidate free parameters: variables that occur in some equality. Cap the search
    // so a hard instance stays cheap.
    std::vector<VarId> params;
    {
        std::unordered_set<std::string> seenName;
        for (const auto& [p, rel] : cons) {
            if (rel != Relation::Eq) continue;
            for (const auto& vn : kernel.variables(p)) {
                if (seenName.insert(vn).second) params.push_back(kernel.getOrCreateVar(vn));
                if (params.size() >= 10) break;
            }
            if (params.size() >= 10) break;
        }
    }
    int budget = 4000;   // total attempt cap (each attempt is ~microseconds)
    for (VarId f1 : params) {
        for (const mpq_class& c1 : kCands) {
            if (--budget < 0) return false;
            std::unordered_map<VarId, mpq_class> seed1{{f1, c1}};
            std::unordered_set<VarId> u1;
            if (attemptSquareCascade(cons, kernel, seed1, modelOut, &u1)) return true;
            // Second free parameter (e.g. a coupled construction like RegHexagon: once
            // the base v9 is fixed, v10^2 = 4 v9 - 7 is a square but v11/v13 stay coupled).
            // Only nest when seeding f1 ALSO unlocked solving some other variable
            // (|u1| + 1 < |u0|), so non-square instances never pay for the inner loop.
            if (u0.size() < 2 || u1.size() + 1 >= u0.size()) continue;
            for (VarId f2 : params) {
                if (f2 == f1 || !u1.count(f2)) continue;
                for (const mpq_class& c2 : kCands) {
                    if (--budget < 0) return false;
                    std::unordered_map<VarId, mpq_class> seed2{{f1, c1}, {f2, c2}};
                    if (attemptSquareCascade(cons, kernel, seed2, modelOut)) return true;
                }
            }
        }
    }
    return false;
}

SquareRoot solveSquareRoot(const SquareEquality& sq, int signHint) {
    SquareRoot r;
    r.var = sq.var;
    r.squaredValue = sq.squaredValue;
    r.sign = (signHint < 0) ? -1 : +1;
    r.isRational = false;
    r.rationalValue = 0;
    r.feasible = (sgn(sq.squaredValue) >= 0);          // c < 0 => no real root
    if (!r.feasible) return r;
    mpq_class root;
    if (rationalSqrt(sq.squaredValue, root)) {
        r.isRational = true;
        r.rationalValue = mpq_class(r.sign) * root;
    }
    return r;
}

}  // namespace xolver
