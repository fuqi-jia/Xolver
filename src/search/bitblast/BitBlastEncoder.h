#pragma once

#include "contracts/SatSolver.h"
#include "search/bitblast/BitVec.h"
#include "search/boolean/BooleanDefinitions.h"
#include "ir/types.h"          // Relation
#include <gmpxx.h>
#include <array>
#include <cstdint>
#include <functional>
#include <optional>
#include <utility>
#include <unordered_map>

namespace xolver::bitblast {

// CNF encoder over an independent SAT instance. Two's-complement, width-growing
// arithmetic: add -> max(wa,wb)+1, mul -> wa+wb, so the encoded value is exact
// whenever leaf widths cover their domains. Non-owning reference to the SAT.
class BitBlastEncoder {
public:
    explicit BitBlastEncoder(SatSolver& sat);

    SatLit constTrue()  const { return true_; }
    SatLit constFalse() const { return false_; }

    BitVec mkConst(const mpz_class& v, unsigned minWidth = 0);
    BitVec mkVar(unsigned width);

    // Tseitin gates; constant folding and sharing avoid redundant variables.
    SatLit andGate(SatLit a, SatLit b);
    SatLit orGate(SatLit a, SatLit b);
    SatLit xorGate(SatLit a, SatLit b);
    SatLit iteGate(SatLit s, SatLit t, SatLit e);
    SatLit majorityGate(SatLit a, SatLit b, SatLit c);
    // Full equivalences by default. With one direction requested, the caller
    // must have established the connective's occurrence polarity first.
    SatLit andGate(std::span<const SatLit> inputs, BooleanDefinitionDirections directions = {});
    SatLit orGate(std::span<const SatLit> inputs, BooleanDefinitionDirections directions = {});
    uint64_t naryGateCount() const { return naryGateCount_; }
    uint64_t naryInputCount() const { return naryInputCount_; }
    uint64_t naryCacheHits() const { return naryCacheHits_; }
    uint64_t naryDirectionUpgrades() const { return naryDirectionUpgrades_; }
    uint64_t ternaryGateCount() const { return ternaryGateCache_.size(); }
    uint64_t ternaryCacheHits() const { return ternaryCacheHits_; }

    // Arithmetic.
    BitVec add(const BitVec& a, const BitVec& b);    // width max+1
    BitVec neg(const BitVec& a);                     // width +1
    BitVec sub(const BitVec& a, const BitVec& b);
    BitVec mul(const BitVec& a, const BitVec& b);    // width wa+wb
    BitVec mulConst(const mpz_class& c, const BitVec& a);
    BitVec powConst(const BitVec& a, unsigned e);

    // Relations: every NIA constraint is `value rel 0`.
    SatLit isZero(const BitVec& a);
    SatLit eq(const BitVec& a, const BitVec& b);
    // Exact signed comparison after sign extension, without constructing a-b.
    SatLit compare(const BitVec& a, const BitVec& b, Relation rel);
    SatLit relZero(const BitVec& a, Relation rel);

    void assertLit(SatLit l);
    void assertImplication(SatLit premise, SatLit conclusion);

    // Hard resource guard: cap the number of fresh SAT variables this encoder
    // will allocate. High-degree QF_NIA can blow the encoding past memory and
    // abort inside CaDiCaL with bad_alloc; once the budget is hit, freshVar()
    // stops allocating (returns the constant-false literal) and sets the
    // overflow flag. No new clauses are emitted after failure. The unfinished
    // result cannot be assumed; previously completed facts may still refute
    // their exact prefix. SAT requires complete encoding/validation. 0 = unlimited.
    void setVarBudget(uint64_t maxVars) { maxVars_ = maxVars; }
    bool overflowed() const { return over_; }
    // Overflow can introduce dummy literals: check it before using a known
    // contradiction as evidence about the intended, exact encoding.
    bool inconsistent() const { return sat_.inconsistent(); }
    uint64_t varCount() const { return varCount_; }
    std::optional<uint64_t> remainingVarBudget() const {
        if (over_) return uint64_t(0);
        if (!maxVars_) return std::nullopt;
        return maxVars_ > varCount_ ? maxVars_ - varCount_ : 0;
    }

private:
    SatSolver& sat_;
    SatLit true_;
    SatLit false_;

    // Allocate one fresh SAT variable, honouring the var budget.
    SatLit freshVar();
    uint64_t maxVars_ = 0;     // 0 = unlimited
    uint64_t varCount_ = 0;
    bool over_ = false;
    SatLit naryGate(std::span<const SatLit> inputs, bool conjunction,
                    BooleanDefinitionDirections directions);
    uint64_t naryGateCount_ = 0;
    uint64_t naryInputCount_ = 0;
    uint64_t naryCacheHits_ = 0;
    uint64_t naryDirectionUpgrades_ = 0;

    struct NaryGateKey {
        bool conjunction;
        std::vector<SatLit> inputs;
        bool operator==(const NaryGateKey& other) const {
            return conjunction == other.conjunction && inputs == other.inputs;
        }
    };
    struct NaryGateKeyHash {
        size_t operator()(const NaryGateKey& key) const {
            size_t hash = key.conjunction;
            for (const auto input : key.inputs) {
                const uint64_t encoded = (uint64_t(input.var) << 1) | uint64_t(input.sign);
                const auto part = std::hash<uint64_t>{}(encoded);
                hash ^= part + size_t(0x9e3779b9) + (hash << 6) + (hash >> 2);
            }
            return hash;
        }
    };
    struct NaryGateDefinition {
        SatLit output;
        BooleanDefinitionDirections directions;
    };
    std::unordered_map<NaryGateKey, NaryGateDefinition, NaryGateKeyHash> naryGateCache_;

    // Share by exact gate identity within this encoder's SAT instance. Each
    // operand retains all 32 variable bits; signs and kind live separately.
    // Hash collisions are resolved by equality, never treated as identity.
    enum class GateKind : uint8_t { And, Or, Xor };
    struct GateKey {
        uint64_t variables;
        unsigned tag;
        bool operator==(const GateKey& other) const {
            return variables == other.variables && tag == other.tag;
        }
    };
    struct GateKeyHash {
        size_t operator()(const GateKey& key) const {
            const size_t h = std::hash<uint64_t>{}(key.variables);
            return h ^ (key.tag + size_t(0x9e3779b9) + (h << 6) + (h >> 2));
        }
    };
    static GateKey gateKey(GateKind kind, SatLit a, SatLit b);
    SatLit internGate(GateKind kind, SatLit a, SatLit b);
    std::unordered_map<GateKey, SatLit, GateKeyHash> gateCache_;

    enum class TernaryGateKind : uint8_t { Ite, Majority };
    struct TernaryGateKey {
        TernaryGateKind kind;
        std::array<SatLit, 3> inputs;
        bool operator==(const TernaryGateKey& other) const {
            return kind == other.kind && inputs == other.inputs;
        }
    };
    struct TernaryGateKeyHash {
        size_t operator()(const TernaryGateKey& key) const {
            size_t hash = static_cast<size_t>(key.kind);
            for (const auto literal : key.inputs) {
                const uint64_t encoded = (uint64_t(literal.var) << 1) | uint64_t(literal.sign);
                const auto part = std::hash<uint64_t>{}(encoded);
                hash ^= part + size_t(0x9e3779b9) + (hash << 6) + (hash >> 2);
            }
            return hash;
        }
    };
    SatLit internTernaryGate(TernaryGateKind kind, SatLit a, SatLit b, SatLit c);
    std::unordered_map<TernaryGateKey, SatLit, TernaryGateKeyHash> ternaryGateCache_;
    uint64_t ternaryCacheHits_ = 0;

    static unsigned bitsForValue(const mpz_class& v);
    BitVec signExtend(const BitVec& a, unsigned width);
    std::pair<SatLit, SatLit> fullAdder(SatLit a, SatLit b, SatLit cin);
    BitVec addFixed(const BitVec& a, const BitVec& b, unsigned w); // truncates to w
    BitVec shiftLeft(const BitVec& a, unsigned k);                 // a * 2^k (exact, width +k)
    BitVec negFixed(const BitVec& a, unsigned w);                  // -a in width w
};

} // namespace xolver::bitblast
