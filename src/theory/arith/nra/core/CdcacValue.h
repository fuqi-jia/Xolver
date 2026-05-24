#pragma once
#include "theory/arith/nra/core/CdcacCommon.h"

namespace nlcolver {

struct AlgebraicRoot {
    UniPolyId definingPoly = NullUniPolyId;
    int rootIndex = -1;
    mpq_class lower;
    mpq_class upper;
    std::vector<RootOrigin> origins;
};

struct RealAlg {
    enum class Kind { Rational, AlgebraicRoot };
    Kind kind = Kind::Rational;
    mpq_class rational;
    AlgebraicRoot root;

    static RealAlg fromRational(mpq_class q) {
        RealAlg r;
        r.kind = Kind::Rational;
        r.rational = std::move(q);
        return r;
    }
    static RealAlg fromAlgebraic(AlgebraicRoot ar) {
        RealAlg r;
        r.kind = Kind::AlgebraicRoot;
        r.root = std::move(ar);
        return r;
    }

    bool isRational() const { return kind == Kind::Rational; }
    bool isAlgebraic() const { return kind == Kind::AlgebraicRoot; }
};

struct SamplePoint {
    std::vector<VarId> varOrder;
    std::vector<RealAlg> values;

    size_t numVars() const { return varOrder.size(); }
    bool empty() const { return varOrder.empty(); }

    void push(VarId v, RealAlg val) {
        varOrder.push_back(v);
        values.push_back(std::move(val));
    }
    void pop() {
        if (!varOrder.empty()) {
            varOrder.pop_back();
            values.pop_back();
        }
    }
    void clear() {
        varOrder.clear();
        values.clear();
    }
};

struct RootSet {
    std::vector<RealAlg> roots;
    int numRoots() const { return static_cast<int>(roots.size()); }
    bool empty() const { return roots.empty(); }
    bool crashOccurred = false;
};

struct Bound {
    enum class Kind { NegInf, PosInf, Rational, AlgebraicRoot } kind;
    RealAlg value;
    bool open = true;

    static Bound negInf() {
        return {Kind::NegInf, RealAlg::fromRational(0), true};
    }
    static Bound posInf() {
        return {Kind::PosInf, RealAlg::fromRational(0), true};
    }
    static Bound rational(mpq_class q, bool isOpen) {
        return {Kind::Rational, RealAlg::fromRational(std::move(q)), isOpen};
    }
    static Bound algebraic(AlgebraicRoot ar, bool isOpen) {
        return {Kind::AlgebraicRoot, RealAlg::fromAlgebraic(std::move(ar)), isOpen};
    }

    bool isNegInf() const { return kind == Kind::NegInf; }
    bool isPosInf() const { return kind == Kind::PosInf; }
    bool isRational() const { return kind == Kind::Rational; }
    bool isAlgebraic() const { return kind == Kind::AlgebraicRoot; }
};

struct ExtRealAlg {
    bool isNegInf = false;
    bool isPosInf = false;
    RealAlg value;

    static ExtRealAlg negInfinity() {
        ExtRealAlg e;
        e.isNegInf = true;
        return e;
    }
    static ExtRealAlg posInfinity() {
        ExtRealAlg e;
        e.isPosInf = true;
        return e;
    }
    static ExtRealAlg fromRealAlg(RealAlg r) {
        ExtRealAlg e;
        e.value = std::move(r);
        return e;
    }
};

} // namespace nlcolver
