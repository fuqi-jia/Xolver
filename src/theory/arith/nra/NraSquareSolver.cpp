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
    // Generator LIST: each entry is an INDEPENDENT square root sqrt(c_i) with
    // genVar_i = sign_i*sqrt(c_i), spanning its own block of the algebraic model.
    // Different geometric sub-constructions can live in different quadratic fields
    // (e.g. Q(sqrt 3) for one block and Q(sqrt 5) for another) with no sqrt(c_i c_j)
    // cross-term linking them: a constraint touching a SINGLE generator reduces over
    // it; one mixing two generators is rejected by validation (sound).
    struct GenInfo { VarId var; mpq_class c; int sign; };
    std::vector<GenInfo> gens;
    auto genIndexOf = [&](VarId v) -> int {
        for (size_t i = 0; i < gens.size(); ++i) if (gens[i].var == v) return static_cast<int>(i);
        return -1;
    };
    // Which generator does this polynomial live over? Returns the single generator
    // index if it uses exactly one (and no non-generator variable), -1 if none
    // (constant/rational), or -2 if it uses a non-generator variable OR two+ distinct
    // generators (a residual unknown or a genuine cross-term field — the caller bails).
    auto solePolyGen = [&](const RationalPolynomial& q) -> int {
        int found = -1;
        for (VarId v : q.variables()) {
            int gi = genIndexOf(v);
            if (gi < 0) return -2;                  // a non-generator variable survives
            if (found < 0) found = gi;
            else if (found != gi) return -2;        // two distinct generators (cross-term)
        }
        return found;
    };

    auto degIn = [&](PolyId p, VarId v) -> int {
        auto d = kernel.degree(p, kernel.varName(v));
        return d ? *d : 0;
    };
    // Reduce a polynomial univariate in g.var modulo g.var^2 = g.c to aGen*g.var + b.
    // Pure term-wise (no libpoly pseudo-remainder — that crash class is exactly what
    // the cascade must dodge). Terms mentioning any other variable are skipped.
    auto reduceUni = [&](const RationalPolynomial& rp, const GenInfo& g) -> std::pair<mpq_class, mpq_class> {
        mpq_class aGen = 0, b = 0;
        for (const auto& [key, coeff] : rp.terms()) {
            int deg = 0; bool other = false;
            for (const auto& [v, e] : key) { if (v != g.var) other = true; else deg += e; }
            if (other) continue;
            mpq_class cp = 1;
            for (int j = 0; j < deg / 2; ++j) cp *= g.c;
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
        // FIXPOINT: a derived value may itself reference a variable resolved only on a
        // later pass (linear elimination stores v in terms of OTHER unresolved vars),
        // so repeat the substitutions until no assigned variable remains. Capped at 64
        // iterations so a cyclic/mutual definition terminates (leaving a residual var,
        // which the per-constraint validation then bails on — sound).
        for (int iter = 0; iter < 64; ++iter) {
            for (const auto& [v, val] : rationalVal) rp = rp.substituteRational(v, val);
            for (const auto& [v, g] : aliasOf) {
                RationalPolynomial gv; gv.addVar(g, 1, mpq_class(1)); gv.normalize();
                rp = substRpDerived(rp, v, gv);
            }
            for (const auto& [v, mv] : derivedVal) rp = substRpDerived(rp, v, mv);
            rp.normalize();
            bool more = false;
            for (VarId v : rp.variables())
                if (rationalVal.count(v) || aliasOf.count(v) || derivedVal.count(v)) { more = true; break; }
            if (!more) break;
        }
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
                } else {
                    // Place sqrt(c) into the generator LIST. Against each existing
                    // generator g_i = sign_i*sqrt(c_i): an exact (c, sign) match aliases
                    // x onto it; a rational-multiple (c = r^2 * c_i) records x as the
                    // rational multiple x = (s*r*sign_i)*g_i in the SAME field (collapses
                    // sqrt(2) and sqrt(1/2)). If x matches NO existing generator it starts
                    // a NEW, independent generator (its own block) — no longer a bail, so
                    // block-separable systems spanning Q(sqrt c_1), Q(sqrt c_2), ... solve.
                    bool placed = false;
                    for (const auto& g : gens) {
                        if (c == g.c && s == g.sign) { aliasOf[x] = g.var; placed = true; break; }
                        mpq_class ratio = c / g.c; ratio.canonicalize();
                        mpq_class r;
                        if (rationalSqrt(ratio, r)) {
                            const mpq_class scale = mpq_class(s) * r * mpq_class(g.sign);
                            RationalPolynomial mv; mv.addVar(g.var, 1, scale); mv.normalize();
                            derivedVal[x] = std::move(mv); placed = true; break;
                        }
                    }
                    if (!placed) gens.push_back({x, c, s});   // new independent generator
                }
                done[j] = 1; progress = true;
            }
            // higher degree / multi-term: leave for the derived-var phase
        }
    }

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

        // (A) EXACTLY ONE non-generator variable, linear, coefficients over a SINGLE
        // generator: derive its EXACT value in Q(sqrt c_i) by rationalizing -C/A.
        do {
            VarId d = NullVar; bool multi = false;
            for (VarId v : rps.variables()) {
                if (genIndexOf(v) >= 0) continue;            // a generator, not the unknown
                if (d != NullVar) { multi = true; break; }   // more than one unassigned
                d = v;
            }
            if (multi || d == NullVar) break;
            std::vector<RationalPolynomial> co = rps.coefficients(d);   // [C, A] low->high
            if (co.size() != 2) break;                                 // must be linear in d
            const int gA = solePolyGen(co[1]);                         // generator of A
            const int gC = solePolyGen(co[0]);                         // generator of C
            if (gA == -2 || gC == -2) break;                           // non-gen var or cross-term
            if (gA >= 0 && gC >= 0 && gA != gC) break;                 // A, C in different fields
            const int gi = (gA >= 0) ? gA : gC;                        // common generator (or -1)
            // d = -C / A. Reduce A, C mod g.var^2 = g.c to A = aA*g + bA, C = cA*g + cB,
            // then RATIONALIZE by the conjugate of A:  -C/A = -C*conj(A) / (A*conj(A)),
            // where A*conj(A) = bA^2 - aA^2*g.c is RATIONAL, and -C*conj(A) reduces (mod
            // g^2=g.c) to P0 + P1*g. So d = (P0 + P1*g)/denom is a POLYNOMIAL in g — even
            // when A itself still depends on the generator (the sqrt cancels). This is
            // what lets the cascade derive m for the whole Geogebra cluster, not just the
            // case where A happens to collapse to a constant.
            RationalPolynomial mv;
            if (gi >= 0) {
                const GenInfo& g = gens[gi];
                auto rA = reduceUni(co[1], g);
                auto rC = reduceUni(co[0], g);
                const mpq_class aA = rA.first, bA = rA.second, cA = rC.first, cB = rC.second;
                const mpq_class denom = bA * bA - aA * aA * g.c;       // A * conj(A)
                if (sgn(denom) == 0) break;                            // A vanishes at root
                const mpq_class P0 = cA * aA * g.c - cB * bA;          // -C*conj(A), const
                const mpq_class P1 = cB * aA - cA * bA;                // -C*conj(A), g coeff
                if (sgn(P1) != 0) mv.addVar(g.var, 1, P1 / denom);
                mv.addConstant(P0 / denom);
            } else {
                if (!co[1].isConstant() || !co[0].isConstant()) break;
                const mpq_class A = co[1].constantValue();
                if (sgn(A) == 0) break;
                mv.addConstant(-co[0].constantValue() / A);
            }
            mv.normalize();
            derivedVal[d] = std::move(mv);
            done[j] = 1; dprogress = true;
        } while (false);
        if (done[j]) continue;

        // (A2) GENERAL QUADRATIC in a single non-generator variable d:
        //   a*d^2 + b*d + c = 0   with a, b, c each REDUCIBLE to a rational over the (at
        // most one) generator that coefficient uses. Solve by the quadratic formula
        // d = (-b +/- sqrt(D))/(2a), D = b^2 - 4ac. A perfect-square D gives a rational
        // root; otherwise sqrt(D) becomes an algebraic generator — collapsed onto an
        // existing one if D = r^2*c_i, else a FRESH independent generator (an auxiliary
        // sqrt that is not itself a problem variable). This closes the law-of-cosines /
        // circle-intersection patterns the PURE-square solver (no d^1 term) misses.
        do {
            VarId d = NullVar; bool multi = false;
            for (VarId v : rps.variables()) {
                if (genIndexOf(v) >= 0) continue;
                if (d != NullVar) { multi = true; break; }
                d = v;
            }
            if (multi || d == NullVar) break;
            std::vector<RationalPolynomial> co = rps.coefficients(d);   // [c, b, a] low->high
            if (co.size() != 3) break;                                 // must be quadratic in d
            // Each coefficient must reduce to a RATIONAL over the single generator it
            // uses; an irrational (a*g) coefficient would nest radicals — not handled.
            auto reduceToRational = [&](const RationalPolynomial& q, mpq_class& outv) -> bool {
                const int gi = solePolyGen(q);
                if (gi == -2) return false;                            // non-gen var or cross-term
                if (gi == -1) { if (!q.isConstant()) return false; outv = q.constantValue(); return true; }
                auto r = reduceUni(q, gens[gi]);
                if (sgn(r.first) != 0) return false;                   // irrational a*g part
                outv = r.second; return true;
            };
            mpq_class a, b, c;
            if (!reduceToRational(co[2], a) || !reduceToRational(co[1], b) || !reduceToRational(co[0], c)) break;
            if (sgn(a) == 0) break;                                    // not actually quadratic
            const mpq_class D = b * b - 4 * a * c;                     // discriminant
            if (sgn(D) < 0) break;                                     // no real root in this branch
            const mpq_class twoA = 2 * a;
            const int want = signHint.count(d) ? signHint[d] : 0;
            mpq_class rootD;
            if (rationalSqrt(D, rootD)) {                              // two RATIONAL roots
                const mpq_class rPlus = (-b + rootD) / twoA, rMinus = (-b - rootD) / twoA;
                mpq_class chosen = rPlus;
                if (want > 0) chosen = (sgn(rPlus) >= 0) ? rPlus : rMinus;
                else if (want < 0) chosen = (sgn(rPlus) <= 0) ? rPlus : rMinus;
                RationalPolynomial mv; mv.addConstant(chosen); mv.normalize();
                derivedVal[d] = std::move(mv);
                done[j] = 1; dprogress = true;
                break;
            }
            // sqrt(D) irrational: place it. sqrt(D) = gFactor * gvar where gvar is the
            // (possibly collapsed) generator: for gvar = gsign*sqrt(c_i) and D = r^2*c_i,
            // sqrt(D) = r*sqrt(c_i) = r*gsign*gvar, so gFactor = r*gsign (r=1 on exact).
            VarId gvar = NullVar; mpq_class gFactor;
            for (const auto& g : gens) {
                if (D == g.c) { gvar = g.var; gFactor = mpq_class(g.sign); break; }
                mpq_class ratio = D / g.c; ratio.canonicalize();
                mpq_class r;
                if (rationalSqrt(ratio, r)) { gvar = g.var; gFactor = r * mpq_class(g.sign); break; }
            }
            if (gvar == NullVar) {                                     // fresh generator +sqrt(D)
                gvar = kernel.getOrCreateVar("__sqd_q" + std::to_string(j));
                gens.push_back({gvar, D, +1});
                gFactor = mpq_class(1);
            }
            const mpq_class cnst = -b / twoA, gcoefPlus = gFactor / twoA;
            auto buildRoot = [&](int pm) {
                RationalPolynomial mv; mv.addConstant(cnst);
                mv.addVar(gvar, 1, mpq_class(pm) * gcoefPlus); mv.normalize();
                return mv;
            };
            RationalPolynomial mvPlus = buildRoot(+1), mvMinus = buildRoot(-1), chosen = mvPlus;
            if (want != 0) {                                           // pick the sign-respecting root
                const int gi = genIndexOf(gvar);
                auto sP = signOfPolyAtGenerator(mvPlus, gens[gi].var, gens[gi].c, gens[gi].sign);
                auto sM = signOfPolyAtGenerator(mvMinus, gens[gi].var, gens[gi].c, gens[gi].sign);
                if (sP && *sP == want) chosen = mvPlus;
                else if (sM && *sM == want) chosen = mvMinus;
            }
            derivedVal[d] = std::move(chosen);
            done[j] = 1; dprogress = true;
        } while (false);
        if (done[j]) continue;

        // (A3) DENESTING square: a*d^2 + c = 0 (no linear term, a rational) where c is
        // IRRATIONAL over a single generator g, i.e. d^2 = V = p + q*sqrt(g.c) lives in
        // Q(sqrt g.c). Solve sqrt(V) WITHIN the same field: V = (r + t*sqrt(g.c))^2 has a
        // rational solution iff p^2 - q^2*g.c is a rational square and the resulting
        // r^2, t^2 are rational squares (classic radical denesting). This keeps d in the
        // EXISTING generator — no new field — and is what carries e.g. Odom-GoldenRatio's
        // v19^2 = (3 - sqrt5)/8  ->  v19 = (sqrt5 - 1)/4, which the pure-square solver
        // (rational radicand only) and the general-quadratic branch (rational coeffs
        // only) both reject.
        do {
            VarId d = NullVar; bool multi = false;
            for (VarId v : rps.variables()) {
                if (genIndexOf(v) >= 0) continue;
                if (d != NullVar) { multi = true; break; }
                d = v;
            }
            if (multi || d == NullVar) break;
            std::vector<RationalPolynomial> co = rps.coefficients(d);   // [c, b, a] low->high
            if (co.size() != 3) break;
            auto toRat = [&](const RationalPolynomial& q, mpq_class& outv) -> bool {
                const int gi = solePolyGen(q);
                if (gi == -2) return false;
                if (gi == -1) { if (!q.isConstant()) return false; outv = q.constantValue(); return true; }
                auto rr = reduceUni(q, gens[gi]);
                if (sgn(rr.first) != 0) return false;
                outv = rr.second; return true;
            };
            mpq_class a, b;
            if (!toRat(co[2], a) || sgn(a) == 0) break;       // leading must be rational, nonzero
            if (!toRat(co[1], b) || sgn(b) != 0) break;       // PURE square (no linear term)
            const int gi = solePolyGen(co[0]);                // constant must be over ONE generator
            if (gi < 0) break;                                // rational (A2) or cross-term -> skip
            const GenInfo& g = gens[gi];
            auto rc = reduceUni(co[0], g);                    // co[0] = rc.first*genVar + rc.second
            // d^2 = V = -co[0]/a. With genVar = g.sign*sqrt(g.c):
            //   V = (-rc.second/a) + (-rc.first*g.sign/a)*sqrt(g.c) = p + qv*sqrt(g.c).
            const mpq_class p = -rc.second / a;
            const mpq_class qv = (-rc.first * mpq_class(g.sign)) / a;
            if (sgn(qv) == 0) break;                          // V rational -> pure-square path
            // Denest sqrt(V) = r + t*sqrt(g.c): r^2 + t^2*g.c = p, 2rt = qv. Then r^2, t^2*g.c
            // are the roots of z^2 - p z + (qv^2 g.c)/4 = 0, real iff Delta = p^2 - qv^2 g.c >= 0.
            const mpq_class Delta = p * p - qv * qv * g.c;
            if (sgn(Delta) < 0) break;
            mpq_class w;
            if (!rationalSqrt(Delta, w)) break;               // Delta not a rational square
            const mpq_class z1 = (p + w) / 2, z2 = (p - w) / 2;
            mpq_class r, t; bool denested = false;
            for (int sw = 0; sw < 2 && !denested; ++sw) {
                const mpq_class r2 = sw ? z2 : z1;            // candidate r^2
                const mpq_class t2c = sw ? z1 : z2;          // candidate t^2 * g.c
                if (sgn(r2) < 0 || sgn(t2c) < 0) continue;
                mpq_class t2 = t2c / g.c, r0, t0;
                if (rationalSqrt(r2, r0) && rationalSqrt(t2, t0)) {
                    r = r0; t = (sgn(qv) < 0) ? -t0 : t0;     // 2 r0 t0 = |qv|; match qv's sign
                    if (2 * r * t == qv) denested = true;
                }
            }
            if (!denested) break;
            // sqrt(V) = r + t*sqrt(g.c) = r + t*g.sign*genVar.
            const mpq_class gvCoef = t * mpq_class(g.sign);
            auto build = [&](int pm) {
                RationalPolynomial mv; mv.addConstant(mpq_class(pm) * r);
                mv.addVar(g.var, 1, mpq_class(pm) * gvCoef); mv.normalize();
                return mv;
            };
            RationalPolynomial mvP = build(+1), mvM = build(-1), chosen = mvP;
            const int want = signHint.count(d) ? signHint[d] : 0;
            if (want != 0) {
                auto sP = signOfPolyAtGenerator(mvP, g.var, g.c, g.sign);
                auto sM = signOfPolyAtGenerator(mvM, g.var, g.c, g.sign);
                if (sP && *sP == want) chosen = mvP;
                else if (sM && *sM == want) chosen = mvM;
            }
            derivedVal[d] = std::move(chosen);
            done[j] = 1; dprogress = true;
        } while (false);
        if (done[j]) continue;

        // (B) COUPLED LINEAR ELIMINATION. The equation may still have two+ unresolved
        // variables, but be linear in ONE of them with a CONSTANT (rational) leading
        // coefficient. Solve that variable as a polynomial in the OTHERS; a later
        // fixpoint pass resolves those in turn, triangularizing a coupled linear
        // subsystem (e.g. two midpoint/centroid equations sharing two coordinates that
        // neither single-var rationalization nor a free-parameter seed can split).
        // SOUNDNESS: the final per-constraint validation reduces over a single
        // generator and BAILS (-> nullopt -> return false) if any non-generator
        // variable survives, so an under-determined elimination is never accepted as
        // SAT — the pivot choice only needs to be CONSISTENT, not unique.
        for (VarId v : rps.variables()) {
            if (genIndexOf(v) >= 0) continue;
            std::vector<RationalPolynomial> co = rps.coefficients(v);
            if (co.size() != 2) continue;          // not linear in v
            if (!co[1].isConstant()) continue;     // need a rational constant coefficient
            const mpq_class A = co[1].constantValue();
            if (sgn(A) == 0) continue;
            RationalPolynomial mv = co[0];
            mv *= (mpq_class(-1) / A);              // v = -C / A  (C still in other vars)
            mv.normalize();
            derivedVal[v] = std::move(mv);
            done[j] = 1; dprogress = true;
            break;
        }
    }
    }

    // Flatten every derived value to the generator/rationals: coupled linear
    // elimination may have stored a variable in terms of OTHERS that were resolved only
    // on a later pass. applySubstRp is a fixpoint, so one application per entry fully
    // resolves each chain (a residual var here means a cyclic/under-determined system,
    // which the validation below rejects).
    for (auto& kv : derivedVal) kv.second = applySubstRp(kv.second);

    // Report the still-unresolved variables (in some constraint but assigned no value)
    // so the caller can guide a multi-parameter instantiation.
    if (unresolvedOut) {
        unresolvedOut->clear();
        std::unordered_set<VarId> assigned;
        for (const auto& kv : rationalVal) assigned.insert(kv.first);
        for (const auto& kv : aliasOf)     assigned.insert(kv.first);
        for (const auto& kv : derivedVal)  assigned.insert(kv.first);
        for (const auto& g : gens)         assigned.insert(g.var);
        for (const auto& [p, rel] : cons)
            for (const auto& vn : kernel.variables(p)) {
                VarId v = kernel.getOrCreateVar(vn);
                if (!assigned.count(v)) unresolvedOut->insert(v);
            }
    }

    // --- VALIDATE every original constraint over its (single) generator ----------
    // A constraint that reduces to a value over exactly ONE generator is decided
    // exactly; one that still mentions a non-generator variable OR mixes two
    // generators (a sqrt(c_i)*sqrt(c_j) cross-term) is inconclusive -> bail (sound).
    auto signOfReduced = [&](PolyId p) -> std::optional<int> {
        auto rp = RationalPolynomial::fromPolyId(p, kernel);
        if (!rp) return std::nullopt;
        RationalPolynomial r = applySubstRp(*rp);   // rationals + aliases + derived (exact)
        if (r.isConstant()) return sgn(r.constantValue());
        // Reduce EVERY monomial modulo all gen_i^2 = c_i. An even power of a generator
        // (e.g. v8^2 -> 3/4) collapses to a RATIONAL contribution, so a constraint that
        // merely squares one generator while using another is still block-separable —
        // it is NOT a cross-term. After reduction the value is b + sum_i a_i*gen_i; only
        // a monomial with ODD powers of TWO DISTINCT generators (a real sqrt(c_i)*sqrt(c_j)
        // term) or a surviving non-generator variable is undecidable here -> bail.
        mpq_class b = 0;
        std::map<int, mpq_class> aGen;                 // gen index -> coeff of that generator
        for (const auto& [key, coeff] : r.terms()) {
            mpq_class m = coeff;
            int oddGen = -1; bool twoOdd = false, nonGen = false;
            for (const auto& [v, e] : key) {
                const int gi = genIndexOf(v);
                if (gi < 0) { nonGen = true; break; }
                for (int k = 0; k < e / 2; ++k) m *= gens[gi].c;   // gen^even -> c^(e/2)
                if (e % 2 == 1) { if (oddGen < 0) oddGen = gi; else twoOdd = true; }
            }
            if (nonGen || twoOdd) return std::nullopt;  // residual var or genuine cross-term
            if (oddGen < 0) b += m; else aGen[oddGen] += m;
        }
        std::vector<std::pair<int, mpq_class>> nz;
        for (const auto& [gi, a] : aGen) if (sgn(a) != 0) nz.push_back({gi, a});
        if (nz.empty()) return sgn(b);
        if (nz.size() == 1) {                          // b + a*gen  (gen = sign*sqrt(c))
            const GenInfo& g = gens[nz[0].first];
            return signOfRootExpr(nz[0].second * mpq_class(g.sign), b, g.c);
        }
        return std::nullopt;   // sum of 2+ independent surds: sign undecided in this kernel
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
        // Per-generator algebraic value g_i = sign_i*sqrt(c_i) with a TIGHT isolating
        // bracket: for non-square c, c != 1, so c<1 => c < sqrt(c) < 1 and c>1 =>
        // 1 < sqrt(c) < c. A tight interval keeps the downstream refinement cheap.
        auto genRealValue = [&](const GenInfo& g) {
            const mpq_class sqLo = (g.c < 1) ? g.c : mpq_class(1);
            const mpq_class sqHi = (g.c < 1) ? mpq_class(1) : g.c;
            const mpz_class num = g.c.get_num(), den = g.c.get_den();
            AlgebraicNumber an;
            an.coefficients = {-num, mpz_class(0), den};   // den*x^2 - num, root sign*sqrt(c)
            if (g.sign > 0) { an.lower = sqLo; an.upper = sqHi; }
            else { an.lower = -sqHi; an.upper = -sqLo; }
            return RealValue::fromAlgebraic(std::move(an));
        };
        // Emit only the PROBLEM-variable generators: an auxiliary sqrt(D) minted by the
        // quadratic branch ("__sqd_*") is not a real variable, and the derived values
        // that use it carry self-contained AlgebraicNumbers (built below), so it must
        // not leak into the model the Solver's validator consumes.
        for (const auto& g : gens)
            if (kernel.varName(g.var).rfind("__sqd_", 0) != 0)
                modelOut->emplace_back(g.var, genRealValue(g));
        for (const auto& [v, gv] : aliasOf) {
            const int gi = genIndexOf(gv);
            if (gi >= 0) modelOut->emplace_back(v, genRealValue(gens[gi]));
        }
        // Derived d = ap*g + bp in Q(sqrt c_i) for the SINGLE generator g_i it uses.
        // With g = sign_i*sqrt(c_i), d = Aeff*sqrt(c_i) + bp where Aeff = ap*sign_i.
        for (const auto& [d, mv] : derivedVal) {
            const int gi = solePolyGen(mv);
            if (gi < 0) {
                if (mv.isConstant()) { modelOut->emplace_back(d, RealValue::fromMpq(mv.constantValue())); continue; }
                return false;            // spans 2+ generators (cross-term): give up (sound)
            }
            const GenInfo& g = gens[gi];
            auto rd = reduceUni(mv, g);
            const mpq_class ap = rd.first, bp = rd.second;
            if (sgn(ap) == 0) { modelOut->emplace_back(d, RealValue::fromMpq(bp)); continue; }
            const mpq_class sqLo = (g.c < 1) ? g.c : mpq_class(1);
            const mpq_class sqHi = (g.c < 1) ? mpq_class(1) : g.c;
            const mpq_class Aeff = (g.sign < 0) ? -ap : ap;   // coefficient of sqrt(c_i)
            // minimal poly: x^2 - 2 bp x + (bp^2 - Aeff^2 c_i).
            mpq_class c0 = bp * bp - Aeff * Aeff * g.c, c1 = mpq_class(-2) * bp, c2 = 1;
            mpz_class L = c0.get_den();
            mpz_lcm(L.get_mpz_t(), L.get_mpz_t(), c1.get_den().get_mpz_t());
            mpz_lcm(L.get_mpz_t(), L.get_mpz_t(), c2.get_den().get_mpz_t());
            mpz_class a0 = mpq_class(c0 * L).get_num(), a1 = mpq_class(c1 * L).get_num(),
                      a2 = mpq_class(c2 * L).get_num();
            mpz_class gg = a0;                             // GCD-reduce to keep coefficients small
            mpz_gcd(gg.get_mpz_t(), gg.get_mpz_t(), a1.get_mpz_t());
            mpz_gcd(gg.get_mpz_t(), gg.get_mpz_t(), a2.get_mpz_t());
            if (sgn(gg) != 0 && gg != 1) { a0 /= gg; a1 /= gg; a2 /= gg; }
            AlgebraicNumber an;
            an.coefficients = {a0, a1, a2};
            // d in [bp + Aeff*sqLo, bp + Aeff*sqHi] (ordered by sign of Aeff). Excludes the
            // conjugate root bp - Aeff*sqrt(c_i) since sqLo > 0.
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
