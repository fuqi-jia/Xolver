#include "ir/NativeTerms.h"
#include "ir/NativeKind.h"
#include <somtparser/ir/node.h>
#include <charconv>
#include <stdexcept>

namespace xolver {
namespace {
using SOMTParser::Node;
using SOMTParser::NODE_KIND;
using SOMTParser::SortManager;
using SortPtr = std::shared_ptr<SOMTParser::Sort>;

Node resolve(Node node) {
    std::unordered_set<Node> seen;
    while (node) {
        auto k = node->getKind();
        if (k != NODE_KIND::NT_LET_BIND_VAR && k != NODE_KIND::NT_LET &&
            k != NODE_KIND::NT_LET_CHAIN) return node;
        if (!seen.insert(node).second || !node->getChildrenSize())
            throw std::invalid_argument("cyclic or empty native let");
        node = node->getChild(k == NODE_KIND::NT_LET_CHAIN
                                 ? node->getChildrenSize() - 1 : 0);
    }
    throw std::invalid_argument("null native expression");
}

SortPtr canonical(SortPtr sort) {
    if (!sort) return sort;
    if (sort->isIntOrReal()) return SortManager::getInt();
    if ((sort->isDec() || sort->isDef()) && !sort->arity) {
        if (sort->name == "Bool") return SortManager::getBool();
        if (sort->name == "Int") return SortManager::getInt();
        if (sort->name == "Real") return SortManager::getReal();
    }
    return sort;
}

SortKind classify(const SortPtr& sort) {
    if (sort->isBool()) return SortKind::Bool;
    if (sort->isInt()) return SortKind::Int;
    if (sort->isReal()) return SortKind::Real;
    if (sort->isBv()) return SortKind::BV;
    if (sort->isFp()) return SortKind::FP;
    if (sort->isArray()) return SortKind::Array;
    if (sort->isDatatype()) return SortKind::Datatype;
    return SortKind::Other;
}

NODE_KIND toNative(Kind kind, SortKind sort) {
    switch (kind) {
        case Kind::ConstBool: case Kind::ConstInt: case Kind::ConstReal:
        case Kind::ConstBV: case Kind::ConstFP: return NODE_KIND::NT_CONST;
#define MAP(a, b) case Kind::a: return NODE_KIND::b
        MAP(Variable, NT_VAR); MAP(BoundVariable, NT_QUANT_VAR);
        MAP(UFApply, NT_UF_APPLY);
        MAP(Not, NT_NOT); MAP(And, NT_AND); MAP(Or, NT_OR);
        MAP(Implies, NT_IMPLIES); MAP(Xor, NT_XOR); MAP(Ite, NT_ITE);
        MAP(Add, NT_ADD); MAP(Sub, NT_SUB); MAP(Neg, NT_NEG); MAP(Mul, NT_MUL);
        case Kind::Div: return sort == SortKind::Int ? NODE_KIND::NT_DIV_INT
                                                   : NODE_KIND::NT_DIV_REAL;
        MAP(Mod, NT_MOD); MAP(Abs, NT_ABS); MAP(Pow, NT_POW);
        MAP(Eq, NT_EQ); MAP(Distinct, NT_DISTINCT); MAP(Lt, NT_LT);
        MAP(Leq, NT_LE); MAP(Gt, NT_GT); MAP(Geq, NT_GE);
        MAP(BvNot, NT_BV_NOT); MAP(BvAnd, NT_BV_AND); MAP(BvOr, NT_BV_OR);
        MAP(BvAdd, NT_BV_ADD); MAP(BvMul, NT_BV_MUL);
        MAP(Forall, NT_FORALL); MAP(Exists, NT_EXISTS);
        MAP(ToInt, NT_TO_INT); MAP(ToReal, NT_TO_REAL); MAP(IsInt, NT_IS_INT);
        MAP(Select, NT_SELECT); MAP(Store, NT_STORE); MAP(ConstArray, NT_CONST_ARRAY);
        MAP(Constructor, NT_DT_CONSTRUCTOR); MAP(Selector, NT_DT_SELECTOR);
        MAP(Tester, NT_DT_TESTER); MAP(Unknown, NT_UNKNOWN);
#undef MAP
    }
    throw std::invalid_argument("invalid term kind");
}

std::string text(const Payload& payload) {
    if (auto s = std::get_if<std::string>(&payload.value)) return *s;
    if (auto i = std::get_if<int64_t>(&payload.value)) return std::to_string(*i);
    if (auto i = std::get_if<uint64_t>(&payload.value)) return std::to_string(*i);
    if (auto b = std::get_if<bool>(&payload.value)) return *b ? "true" : "false";
    return {};
}
} // namespace

struct NativeTerms::Storage {
    std::shared_ptr<const void> identity = std::make_shared<const char>(0);
    std::shared_ptr<SOMTParser::NodeManager> manager;
    std::vector<Node> nodes;
    std::vector<SortId> nodeSorts; // resolve parser numeral sorts once, bottom-up
    std::unordered_map<Node, ExprId> ids; // declaration/object identity
    std::unordered_map<SortId, SortPtr> sorts;
    struct SortHash {
        size_t operator()(const SortPtr& s) const { return s->hash(); }
    };
    struct SortEqual {
        bool operator()(const SortPtr& a, const SortPtr& b) const { return *a == *b; }
    };
    std::unordered_map<SortPtr, SortId, SortHash, SortEqual> sortIds;
};

NativeTerms::NativeTerms() : NativeTerms(std::make_shared<SOMTParser::NodeManager>()) {}
NativeTerms::NativeTerms(std::shared_ptr<SOMTParser::NodeManager> manager)
    : storage_(std::make_unique<Storage>()) {
    if (!manager) throw std::invalid_argument("null native node manager");
    storage_->manager = std::move(manager);
}
NativeTerms::~NativeTerms() = default;
NativeTerms::NativeTerms(NativeTerms&&) noexcept = default;
NativeTerms& NativeTerms::operator=(NativeTerms&&) noexcept = default;
NativeTerms::NativeTerms(const NativeTerms& other)
    : storage_(std::make_unique<Storage>(*other.storage_)),
      scopedAssertions_(other.scopedAssertions_), currentScope_(other.currentScope_),
      sortKinds_(other.sortKinds_), arraySortParams_(other.arraySortParams_),
      datatypes_(other.datatypes_), boolSortId_(other.boolSortId_),
      intSortId_(other.intSortId_), realSortId_(other.realSortId_),
      nextSortId_(other.nextSortId_), freshVarCounter_(other.freshVarCounter_),
      freshVarNames_(other.freshVarNames_), internalVariables_(other.internalVariables_),
      routingAuxiliaries_(other.routingAuxiliaries_) {
    storage_->identity = std::make_shared<const char>(0);
}
NativeTerms& NativeTerms::operator=(const NativeTerms& other) {
    if (this != &other) *this = NativeTerms(other);
    return *this;
}

size_t NativeTerms::size() const { return storage_->nodes.size(); }
Node NativeTerms::native(ExprId id) const { return storage_->nodes.at(id); }
std::shared_ptr<const void> NativeTerms::expressionIndexIdentity() const {
    return storage_->identity;
}

ExprId NativeTerms::append(Node node) {
    if (auto it = storage_->ids.find(node); it != storage_->ids.end()) return it->second;
    if (size() >= FalseSentinelExpr) throw std::length_error("native term index overflow");
    const ExprId id = static_cast<ExprId>(size());
    auto sort = node->getSort();
    if (sort && sort->isIntOrReal()) {
        // IntOrReal is the parser's numeral placeholder, not an Int sort.
        // In particular a folded rational such as 1/2 must remain Real.
        bool real = node->getKind() == NODE_KIND::NT_DIV_REAL;
        const auto value = node->getValue();
        if (value && value->getType() == SOMTParser::NUMBER)
            real |= value->getNumberValue().isReal();
        else if (node->getKind() == NODE_KIND::NT_CONST)
            real |= node->getName().find_first_of("./") != std::string::npos;
        for (const auto& child : SOMTParser::children(node)) {
            auto it = storage_->ids.find(resolve(child));
            if (it != storage_->ids.end())
                real |= sortKind(storage_->nodeSorts[it->second]) == SortKind::Real;
        }
        sort = real ? SortManager::getReal() : SortManager::getInt();
    }
    const SortId sortId = indexSort(std::move(sort));
    const auto capacity = std::min<size_t>(FalseSentinelExpr, size() + size() / 2 + 1);
    if (storage_->nodes.capacity() == size()) storage_->nodes.reserve(capacity);
    if (storage_->nodeSorts.capacity() == size()) storage_->nodeSorts.reserve(capacity);
    if (node->getKind() == NODE_KIND::NT_VAR) freshVarNames_.insert(node->getName());
    // All throwing allocations precede the two noexcept vector appends.
    storage_->ids.emplace(node, id);
    storage_->nodes.push_back(node);
    storage_->nodeSorts.push_back(sortId);
    return id;
}

ExprId NativeTerms::index(Node root) {
    root = resolve(std::move(root));
    if (auto it = storage_->ids.find(root); it != storage_->ids.end()) return it->second;
    // Children precede parents, preserving dense-handle topological algorithms.
    struct Frame { Node node; size_t next = 0; };
    std::vector<Frame> stack{{root}};
    std::unordered_set<Node> active{root};
    while (!stack.empty()) {
        auto& frame = stack.back();
        if (frame.next < frame.node->getChildrenSize()) {
            Node child = resolve(frame.node->getChild(frame.next++));
            if (storage_->ids.count(child)) continue;
            if (!active.insert(child).second) throw std::invalid_argument("cyclic native DAG");
            stack.push_back({std::move(child)});
        } else {
            Node node = std::move(frame.node);
            stack.pop_back();
            active.erase(node);
            append(std::move(node));
        }
    }
    return storage_->ids.at(root);
}

SortId NativeTerms::indexSort(SortPtr sort) {
    sort = canonical(std::move(sort));
    if (!sort) return NullSort;
    if (auto it = storage_->sortIds.find(sort); it != storage_->sortIds.end()) return it->second;
    SortId id = allocateSortId();
    registerNativeSort(id, std::move(sort));
    return id;
}

void NativeTerms::registerNativeSort(SortId id, SortPtr sort) {
    sort = canonical(std::move(sort));
    if (id == NullSort || !sort) throw std::invalid_argument("invalid native sort");
    nextSortId_ = std::max(nextSortId_, id + 1);
    storage_->sorts[id] = sort;
    storage_->sortIds.emplace(sort, id); // memoize before recursive datatype fields
    SortKind kind = classify(sort);
    sortKinds_[id] = kind;
    if (kind == SortKind::Bool && boolSortId_ == NullSort) boolSortId_ = id;
    if (kind == SortKind::Int && intSortId_ == NullSort) intSortId_ = id;
    if (kind == SortKind::Real && realSortId_ == NullSort) realSortId_ = id;
    if (sort->isArray())
        arraySortParams_[id] = {indexSort(sort->getIndexSort()), indexSort(sort->getElemSort())};
    if (sort->isDatatype() && !datatypes_.isDatatypeSort(id)) {
        // Recursion is detected using native sort identity, not printed names.
        DatatypeInfo info; info.sort = id;
        std::vector<SortPtr> pending;
        for (const auto& ctor : sort->getDtConstructors()) {
            DtConstructorInfo ci; ci.name = ctor.name; ci.index = info.constructors.size();
            for (const auto& selector : ctor.selectors) {
                ci.selectors.push_back({selector.name, indexSort(selector.sort)});
                pending.push_back(selector.sort);
            }
            info.constructors.push_back(std::move(ci));
        }
        std::unordered_set<SortPtr> seen;
        while (!pending.empty()) {
            auto current = pending.back(); pending.pop_back();
            if (!current || !seen.insert(current).second) continue;
            if (current == sort) { info.recursive = true; break; }
            for (const auto& child : current->children) pending.push_back(child);
            for (const auto& ctor : current->getDtConstructors())
                for (const auto& selector : ctor.selectors) pending.push_back(selector.sort);
        }
        datatypes_.addDatatype(std::move(info));
    }
}

void NativeTerms::registerSort(SortId id, SortKind kind) {
    SortPtr sort;
    switch (kind) {
        case SortKind::Bool: sort = SortManager::getBool(); break;
        case SortKind::Int: sort = SortManager::getInt(); break;
        case SortKind::Real: sort = SortManager::getReal(); break;
        case SortKind::Other:
            sort = std::make_shared<SOMTParser::Sort>(SOMTParser::SORT_KIND::SK_DEC,
                                                     "@sort" + std::to_string(id), 0);
            break;
        default:
            throw std::invalid_argument("parameterized sorts require their native signature");
    }
    registerNativeSort(id, std::move(sort));
}
void NativeTerms::registerArraySort(SortId id, SortId index, SortId element) {
    auto sort = std::make_shared<SOMTParser::Sort>(
        SOMTParser::SORT_KIND::SK_ARRAY, "Array", 2,
        std::vector<SortPtr>{storage_->sorts.at(index), storage_->sorts.at(element)});
    registerNativeSort(id, std::move(sort));
}

namespace {
Node construct(const TermExpr& expr, const SortPtr& sort,
               const std::vector<Node>& nodes, SOMTParser::NodeManager* manager) {
    std::vector<Node> children;
    children.reserve(expr.children.size());
    for (ExprId child : expr.children) children.push_back(nodes.at(child));
    auto k = toNative(expr.kind, sort ? classify(sort) : SortKind::Other);
    auto name = text(expr.payload);
    // Native hash-consing includes the operator name. Match parser-created
    // applications so rebuilding an unchanged native term reuses its node.
    if (expr.payload.empty() && !children.empty())
        name = SOMTParser::kindToString(k);
    if (expr.kind == Kind::ConstBool)
        k = name == "true" ? NODE_KIND::NT_CONST_TRUE : NODE_KIND::NT_CONST_FALSE;
    if (manager) return manager->createNode(sort, k, std::move(name), std::move(children));
    return std::make_shared<SOMTParser::DAGNode>(sort, k, std::move(name), std::move(children));
}
}
ExprId NativeTerms::add(TermExpr expr) {
    if (expr.sort == NullSort || !storage_->sorts.count(expr.sort))
        throw std::invalid_argument("native construction requires a registered sort");
    SortPtr sort = storage_->sorts.at(expr.sort);
    return append(construct(expr, sort, storage_->nodes, nullptr));
}
ExprId NativeTerms::addShared(TermExpr expr) {
    if (expr.sort == NullSort || !storage_->sorts.count(expr.sort))
        throw std::invalid_argument("native construction requires a registered sort");
    SortPtr sort = storage_->sorts.at(expr.sort);
    return index(construct(expr, sort, storage_->nodes, storage_->manager.get()));
}

const TermExpr NativeTerms::get(ExprId id) const {
    const Node& node = storage_->nodes.at(id);
    TermExpr out;
    out.kind = nativeKind(node->getKind());
    out.sort = storage_->nodeSorts.at(id);
    const auto sk = sortKind(out.sort);
    if (out.kind == Kind::ConstReal) {
        if (sk == SortKind::Int) out.kind = Kind::ConstInt;
        else if (sk == SortKind::BV) out.kind = Kind::ConstBV;
        else if (sk == SortKind::FP) out.kind = Kind::ConstFP;
        else if (sk == SortKind::Bool) out.kind = Kind::ConstBool;
    }
    for (const auto& child : SOMTParser::children(node))
        out.children.push_back(storage_->ids.at(resolve(child)));
    if ((out.kind == Kind::Gt || out.kind == Kind::Geq) && out.children.size() == 2) {
        out.kind = out.kind == Kind::Gt ? Kind::Lt : Kind::Leq;
        std::swap(out.children[0], out.children[1]);
    }
    const auto value = node->getValue();
    if (out.kind == Kind::ConstBool) {
        if (value && value->getType() == SOMTParser::BOOLEAN)
            out.payload = Payload(value->getBooleanValue());
        else if (node->getKind() == NODE_KIND::NT_CONST_TRUE || node->getName() == "true")
            out.payload = Payload(true);
        else if (node->getKind() == NODE_KIND::NT_CONST_FALSE || node->getName() == "false")
            out.payload = Payload(false);
        else throw std::invalid_argument("invalid native Boolean literal");
    } else if (out.isConst()) {
        std::string literal = value && value->getType() == SOMTParser::NUMBER
            ? value->getNumberValue().toString() : node->getName();
        int64_t small = 0;
        auto [end, ec] = std::from_chars(literal.data(), literal.data() + literal.size(), small);
        if (out.kind == Kind::ConstInt && ec == std::errc() && end == literal.data() + literal.size())
            out.payload = Payload(small);
        else out.payload = Payload(std::move(literal));
    } else if (out.kind == Kind::Variable || out.kind == Kind::BoundVariable ||
               out.kind == Kind::UFApply || out.kind == Kind::Constructor ||
               out.kind == Kind::Selector || out.kind == Kind::Tester) {
        out.payload = Payload(node->getName());
    }
    return out;
}

ExprId NativeTerms::makeFreshVariable(SortId sort, std::string_view prefix,
                                    bool routingAuxiliary) {
    std::string name;
    do { name = std::string(prefix) + "_" + std::to_string(freshVarCounter_++); }
    while (freshVarNames_.count(name));
    ExprId id = add({Kind::Variable, sort, {}, Payload(std::move(name))});
    internalVariables_.insert(id);
    if (routingAuxiliary) routingAuxiliaries_.insert(id);
    return id;
}
} // namespace xolver
