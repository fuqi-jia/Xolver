#pragma once

// DerivedFact.h — shared derivation infrastructure for the theory-check
// presolve fixpoint (Capabilities 1–7, 9, 11).
//
// Every capability that reasons over active arithmetic atoms emits one or more
// DerivedFacts, each carrying a ReasonNode that records the SAT literals and/or
// upstream DerivedFacts it depends on.  When a conflict or lemma is finally
// produced, DerivationLedger::flattenReasons walks the reason DAG to recover a
// flat vector of base SAT literals — the clause the SAT solver receives.
//
// Soundness contract (see plan §"Soundness Invariants"): the presolve fixpoint
// never returns SAT directly.  It may emit DerivedConflict (UNSAT direction,
// always backed by exact reasoning), DerivedBound / DerivedSubst / etc.
// (consumed by downstream complete engines), or DerivedCaseSplit (a lemma the
// SAT solver branches on).

#include "expr/types.h"
#include "sat/SatSolver.h"
#include "theory/arith/poly/RationalPolynomial.h"
#include "theory/arith/nra/core/CdcacValue.h"   // AlgebraicRoot, RealAlg
#include "theory/core/TheoryAtomTypes.h"          // TheoryConflict, TheoryLemma

#include <gmpxx.h>
#include <optional>
#include <variant>
#include <vector>

namespace nlcolver {

// ---------------------------------------------------------------------------
// BoundEndpoint — a single endpoint of an interval.
//
// Rational and ±Inf endpoints carry exact, comparable values.  Algebraic
// endpoints reuse the existing CDCAC AlgebraicRoot (defining poly + rational
// isolating bracket).  Exact comparison of algebraic endpoints requires a
// libpoly backend; IntervalSet treats algebraic endpoints conservatively (it
// widens rather than tightens) so that no false UNSAT can ever be produced.
// ---------------------------------------------------------------------------
struct BoundEndpoint {
    enum class Kind { NegInf, PosInf, Rational, Algebraic };
    Kind kind = Kind::NegInf;
    mpq_class rationalValue;       // valid when kind == Rational
    AlgebraicRoot algebraicValue;  // valid when kind == Algebraic

    static BoundEndpoint negInf() { BoundEndpoint e; e.kind = Kind::NegInf; return e; }
    static BoundEndpoint posInf() { BoundEndpoint e; e.kind = Kind::PosInf; return e; }
    static BoundEndpoint rational(mpq_class q) {
        BoundEndpoint e; e.kind = Kind::Rational; e.rationalValue = std::move(q); return e;
    }
    static BoundEndpoint algebraic(AlgebraicRoot r) {
        BoundEndpoint e; e.kind = Kind::Algebraic; e.algebraicValue = std::move(r); return e;
    }

    bool isNegInf()    const { return kind == Kind::NegInf; }
    bool isPosInf()    const { return kind == Kind::PosInf; }
    bool isRational()  const { return kind == Kind::Rational; }
    bool isAlgebraic() const { return kind == Kind::Algebraic; }

    // A rational LOWER approximation of this endpoint's value (for widening).
    // Exact for Rational; uses the isolating bracket's lower bound for Algebraic.
    // Undefined for ±Inf (callers must check first).
    mpq_class rationalLowerApprox() const {
        if (kind == Kind::Rational) return rationalValue;
        return algebraicValue.lower;
    }
    // A rational UPPER approximation (for widening).
    mpq_class rationalUpperApprox() const {
        if (kind == Kind::Rational) return rationalValue;
        return algebraicValue.upper;
    }
};

// ---------------------------------------------------------------------------
// Interval — [lower, upper] with per-endpoint open/closed flags.
// ---------------------------------------------------------------------------
struct Interval {
    BoundEndpoint lower = BoundEndpoint::negInf();
    BoundEndpoint upper = BoundEndpoint::posInf();
    bool lowerOpen = true;   // open at lower endpoint (always true for -Inf)
    bool upperOpen = true;   // open at upper endpoint (always true for +Inf)
};

// ---------------------------------------------------------------------------
// IntervalSet — a sorted, disjoint union of intervals over Int or Real.
// ---------------------------------------------------------------------------
class IntervalSet {
public:
    enum class Domain { Int, Real };
    Domain domain = Domain::Real;
    std::vector<Interval> intervals;

    IntervalSet() = default;
    explicit IntervalSet(Domain d) : domain(d) {}

    static IntervalSet universe(Domain d) {
        IntervalSet s(d);
        s.intervals.push_back(Interval{});  // (-Inf, +Inf)
        return s;
    }
    static IntervalSet empty(Domain d) { return IntervalSet(d); }

    // Closed/open rational interval [a,b] (or with open flags).
    static IntervalSet fromRational(Domain d, const mpq_class& a, bool aOpen,
                                    const mpq_class& b, bool bOpen) {
        IntervalSet s(d);
        Interval iv;
        iv.lower = BoundEndpoint::rational(a); iv.lowerOpen = aOpen;
        iv.upper = BoundEndpoint::rational(b); iv.upperOpen = bOpen;
        s.intervals.push_back(std::move(iv));
        return s;
    }
    // [a, +Inf)
    static IntervalSet lowerBound(Domain d, const mpq_class& a, bool aOpen) {
        IntervalSet s(d);
        Interval iv;
        iv.lower = BoundEndpoint::rational(a); iv.lowerOpen = aOpen;
        iv.upper = BoundEndpoint::posInf(); iv.upperOpen = true;
        s.intervals.push_back(std::move(iv));
        return s;
    }
    // (-Inf, b]
    static IntervalSet upperBound(Domain d, const mpq_class& b, bool bOpen) {
        IntervalSet s(d);
        Interval iv;
        iv.lower = BoundEndpoint::negInf(); iv.lowerOpen = true;
        iv.upper = BoundEndpoint::rational(b); iv.upperOpen = bOpen;
        s.intervals.push_back(std::move(iv));
        return s;
    }

    bool isEmpty() const { return intervals.empty(); }
    bool isUniverse() const {
        return intervals.size() == 1 &&
               intervals[0].lower.isNegInf() && intervals[0].upper.isPosInf();
    }

    // Intersection.  Exact for rational/±Inf endpoints.  Algebraic endpoints
    // are widened (treated as the loosest rational bracket bound) so the result
    // is always a SUPERSET of the true intersection — sound for UNSAT.
    IntervalSet intersect(const IntervalSet& other) const;

    // Int-domain helpers (valid only when domain == Int) -------------------
    // True iff every interval has finite integer endpoints (no ±Inf side that
    // admits infinitely many integers).
    bool isFiniteInt() const;
    // The explicit, sorted list of integer points (valid iff isFiniteInt()).
    std::vector<mpz_class> integerPoints() const;
};

// ---------------------------------------------------------------------------
// Derived payloads — one per kind of consequence a capability can emit.
// ---------------------------------------------------------------------------
struct DerivedSubst        { VarId var; RationalPolynomial value; };   // Cap. 1
struct DerivedPolySubst    { VarId var; RationalPolynomial value; };   // Cap. 2
struct DerivedLinearCombo  { RationalPolynomial linearConsequence; };  // Cap. 3
struct DerivedBound        { VarId var; IntervalSet interval; };       // Cap. 4, 11
struct DerivedFixedValue   { VarId var; mpq_class value; };            // Cap. 5
struct DerivedCongruence   { VarId var; mpz_class modulus; mpz_class residue; }; // Cap. 5
struct DerivedComposedBound{ RationalPolynomial poly; Relation rel; }; // Cap. 7 (poly rel 0)
struct DerivedCaseSplit    { TheoryLemma lemma; };                     // Cap. 6
struct DerivedConflict     { TheoryConflict conflict; };               // Caps. 1,3,4,5,9,11
struct DerivedSatisfied    { SatLit atom; };                           // Caps. 1,2,4

using DerivedPayload = std::variant<
    DerivedSubst, DerivedPolySubst, DerivedLinearCombo, DerivedBound,
    DerivedFixedValue, DerivedCongruence, DerivedComposedBound,
    DerivedCaseSplit, DerivedConflict, DerivedSatisfied>;

// ---------------------------------------------------------------------------
// ReasonNode / DerivedFact / DerivationLedger — reason-DAG tracking.
// ---------------------------------------------------------------------------
struct ReasonNode {
    std::vector<SatLit> baseLiterals;     // SAT literals directly involved
    std::vector<size_t> upstreamIndices;  // indices of upstream DerivedFacts
};

struct DerivedFact {
    DerivedPayload payload;
    ReasonNode reasons;
};

class DerivationLedger {
public:
    size_t append(DerivedFact f) {
        facts_.push_back(std::move(f));
        return facts_.size() - 1;
    }
    const DerivedFact& at(size_t i) const { return facts_.at(i); }
    size_t size() const { return facts_.size(); }

    // Walk the reason DAG rooted at `index`, collecting all base SAT literals
    // (deduplicated).  Cycles are impossible (upstream indices are strictly
    // smaller), but a visited-set guards against accidental self-reference.
    std::vector<SatLit> flattenReasons(size_t index) const;

    // Flatten the reasons attached directly to a ReasonNode (not yet appended).
    std::vector<SatLit> flattenReasons(const ReasonNode& node) const;

private:
    std::vector<DerivedFact> facts_;
};

} // namespace nlcolver
