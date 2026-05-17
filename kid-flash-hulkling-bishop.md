# EUF ITE 增量饱和集成计划（修订版 v3）

## 目标

将 ITE（if-then-else）从 `EufSolver::check()` 中的 O(N) 全量扫描，升级为**增量式 e-class merge 触发**。核心约束：

1. **EufSolver 拥有唯一 saturation loop**，`egraph_` 只提供原子操作，不暴露内部循环。
2. **`onClassMerged` 只能 enqueue**，不能调用任何 merge 或触发嵌套 drain。
3. **不用 `firedMask` 做语义状态**，幂等判断只用 `egraph_.same()`。

---

## 当前状态

- `EufTermManager` 已将 `Kind::Ite` intern 为 `"ite"` 函数符号
- `EufSolver::check()` 中存在 O(N) 扫描循环：遍历所有 term，检查 `ite(c,t,e)` 的条件是否等于 true/false
- `MergeReasonKind` 已有 `IteTrue` / `IteFalse`，`explainEdge()` 已支持
- **缺失**：R3 规则（`then=else → result=then`）、增量触发、boolMark、occurrence lists、rollback trail

---

## 架构原则

### 原则 1：单一 saturation loop

只有一个 `while (!mergeQueue.empty())` 循环，位于 `EufSolver`（或 `TheoryManager`）内。`egraph_` 不维护自己的 queue，也不暴露 `processMergeQueue()` 之类的循环接口。

`egraph_` 提供的原子操作：
- `merge(a, b, reason) → MergeResult`：执行一次 UF unite，写 union trail，返回 `{merged, kept, killed}`
- `refreshCongruence(kept, killed, queue)`：扫描 killed 的 parents，用 signature table 找新 congruence merges，把新 merge request **enqueue 到传入的 queue**，不自动 drain
- `explainEquality(a, b)`：解释两个 term 为何相等

### 原则 2：callback 只 enqueue

`onClassMerged(kept, killed)` 的职责严格限定为：
1. 合并 occurrence lists / boolMark（写 trail）
2. 对需要触发的 ITE 规则，构造 `MergeRequest` 并 `enqueue` 到 `mergeQueue_`

不得调用 `egraph_.merge()`，不得触发任何嵌套循环。

### 原则 3：不用 firedMask 做语义状态

幂等判断唯一依据：`egraph_.same(result, rhs)`。若同一 batch 内需要 dedup，用 `PendingMergeKey` 或 per-epoch stamp，不依赖 `firedMask`。

---

## Phase 1 — 基础设施扩展（~3 文件）

### 1.1 `src/theory/euf/EufTypes.h`

```cpp
using IteId = uint32_t;

struct IteRecord {
    EufTermId result;
    EufTermId cond;
    EufTermId thenTerm;
    EufTermId elseTerm;
};

struct MergeRequest {
    EufTermId a;
    EufTermId b;
    MergeReason reason;
};

struct MergeReason {
    MergeReasonKind kind;
    SatLit lit;
    EufTermId lhsApp;   // 仅用于 AppCongruence / Axiom

    // ITE 规则解释：egraph 不访问 solver 的 iteRecords_，
    // 由 EufSolver 在 enqueue 时直接填好需要解释的两个 term。
    EufTermId explainA;
    EufTermId explainB;
};
```

`MergeReasonKind` 扩展：`IteBranchesEqual`。

### 1.2 `src/theory/euf/IncrementalEGraph.h` + `.cpp`

移除或 privatize `processMergeQueue()`。暴露：

```cpp
struct MergeResult {
    bool merged;
    EClassId kept;   // winner root
    EClassId killed; // loser root
};

// 执行一次 UF unite，写 trail。不处理 queue，不刷新 congruence。
MergeResult merge(EufTermId a, EufTermId b, const MergeReason& reason);

// 扫描 killed 的 congruence parents，把新 congruence merges enqueue 到 queue。
// 不自动 drain，不调用 callback。
void refreshCongruence(EClassId kept, EClassId killed,
                       std::vector<MergeRequest>& queue);

// 解释 equality
std::vector<CoreExpr> explainEquality(EufTermId a, EufTermId b);

// 注意：egraph 内部不持有 onClassMerged callback。
// EufSolver 在唯一 saturation loop 中显式调用 onClassMerged(mr.kept, mr.killed)。
// egraph_.merge() 只返回 MergeResult，不触发任何外部回调。
```

`explainEdge()` 中 `IteTrue/IteFalse/IteBranchesEqual` 分支：

```cpp
case MergeReasonKind::IteTrue:
case MergeReasonKind::IteFalse:
case MergeReasonKind::IteBranchesEqual:
    // explainA/explainB 在 enqueue 时由 EufSolver 填入，egraph 不访问 iteRecords_
    return explainEquality(reason.explainA, reason.explainB);
```

### 1.3 `src/theory/euf/EufSolver.h`

```cpp
enum class BoolConstMark : uint8_t { None, True, False, Both };

struct EClassInfo {
    SmallVector<IteId, 4> condUses;
    SmallVector<IteId, 4> thenUses;
    SmallVector<IteId, 4> elseUses;
    BoolConstMark boolMark = BoolConstMark::None;
};

// Rollback trail entries
struct IteOccMoveTrail {
    EClassId kept, killed;

    size_t keptCondOldSize, keptThenOldSize, keptElseOldSize;
    size_t killedCondOldSize, killedThenOldSize, killedElseOldSize;
    size_t movedCondCount, movedThenCount, movedElseCount;

    BoolConstMark keptOldMark, killedOldMark;
};

struct IteSnapshot {
    size_t occMoveTrailSize;
    size_t mergeQueueSize;
    size_t nextTermToScan;
};
```

私有成员：

```cpp
std::vector<IteRecord> iteRecords_;
std::unordered_map<EufTermId, IteId> iteOfResult_;
std::vector<EClassInfo> classInfo_;
std::vector<IteOccMoveTrail> iteOccMoveTrail_;

// 唯一 saturation queue（SAT decisions + congruence + ITE）
std::vector<MergeRequest> mergeQueue_;

// per-epoch dedup（可选，不随 snapshot rollback）
std::unordered_set<uint64_t> mergeDedup_;
uint32_t currentEpoch_ = 0;

size_t nextTermToScan_ = 0;
EufTermId trueTerm_ = 0, falseTerm_ = 0;
```

---

## Phase 2 — 核心逻辑（~2 文件）

### 2.1 bool 常量初始化

```cpp
void EufSolver::initializeBoolConstants() {
    trueTerm_  = termManager_.mkBoolConst(true);
    falseTerm_ = termManager_.mkBoolConst(false);

    EClassId tRoot = egraph_.rep(trueTerm_);
    EClassId fRoot = egraph_.rep(falseTerm_);
    classInfo(tRoot).boolMark = BoolConstMark::True;
    classInfo(fRoot).boolMark = BoolConstMark::False;

    if (tRoot == fRoot) {
        pendingConflict_ = TheoryConflict{egraph_.explainEquality(trueTerm_, falseTerm_)};
    }
}
```

构造函数末尾调用。

### 2.2 注册新 ITE term

```cpp
void EufSolver::registerNewIteTerms() {
    size_t n = termManager_.termCount();
    for (; nextTermToScan_ < n; ++nextTermToScan_) {
        auto term = static_cast<EufTermId>(nextTermToScan_);
        if (termManager_.kind(term) != Kind::Ite) continue;
        if (iteOfResult_.contains(term)) continue;   // hash-cons duplicate

        auto [cond, th, el] = termManager_.iteArgs(term);
        registerIte(term, cond, th, el);
    }
}

void EufSolver::registerIte(EufTermId result, EufTermId cond,
                            EufTermId thenTerm, EufTermId elseTerm) {
    IteId id = static_cast<IteId>(iteRecords_.size());
    iteRecords_.push_back({result, cond, thenTerm, elseTerm});
    iteOfResult_[result] = id;

    classInfo(egraph_.rep(cond)).condUses.push_back(id);
    classInfo(egraph_.rep(thenTerm)).thenUses.push_back(id);
    classInfo(egraph_.rep(elseTerm)).elseUses.push_back(id);

    tryFireIte(id);
}
```

### 2.3 `tryFireIte` — 只 enqueue，不 merge

```cpp
void EufSolver::tryFireIte(IteId id) {
    const auto& r = iteRecords_[id];
    EClassId c  = egraph_.rep(r.cond);
    EClassId th = egraph_.rep(r.thenTerm);
    EClassId el = egraph_.rep(r.elseTerm);
    EClassId res = egraph_.rep(r.result);

    auto cMark = classInfo(c).boolMark;

    if (cMark == BoolConstMark::True && !egraph_.same(res, th)) {
        enqueueMerge(r.result, r.thenTerm,
                     MergeReason{MergeReasonKind::IteTrue, SatLit{}, 0,
                                r.cond, trueTerm_});
    }
    if (cMark == BoolConstMark::False && !egraph_.same(res, el)) {
        enqueueMerge(r.result, r.elseTerm,
                     MergeReason{MergeReasonKind::IteFalse, SatLit{}, 0,
                                r.cond, falseTerm_});
    }
    if (th == el && !egraph_.same(res, th)) {
        enqueueMerge(r.result, r.thenTerm,
                     MergeReason{MergeReasonKind::IteBranchesEqual, SatLit{}, 0,
                                r.thenTerm, r.elseTerm});
    }
}
```

`enqueueMerge` 负责 dedup（可选）并入队：

```cpp
void EufSolver::enqueueMerge(EufTermId a, EufTermId b, const MergeReason& reason) {
    // 第一版不实现 dedup。重复入队无害：egraph_.merge() 返回 !merged 时直接跳过。
    // 若后续需要性能优化，dedup key 必须包含 (rootPair, reason.kind, reason.iteId)。
    mergeQueue_.push_back({a, b, reason});
}
```

**没有 `firedMask`**。正确性完全依赖 `egraph_.same()` 的幂等判断。

### 2.4 `onEclassMerged` — callback，只 enqueue

```cpp
void EufSolver::onEclassMerged(EClassId kept, EClassId killed) {
    auto& kInfo = classInfo(kept);
    auto& dInfo = classInfo(killed);

    // Trail
    IteOccMoveTrail trail;
    trail.kept = kept; trail.killed = killed;
    trail.keptCondOldSize  = kInfo.condUses.size();
    trail.keptThenOldSize  = kInfo.thenUses.size();
    trail.keptElseOldSize  = kInfo.elseUses.size();
    trail.killedCondOldSize = dInfo.condUses.size();
    trail.killedThenOldSize = dInfo.thenUses.size();
    trail.killedElseOldSize = dInfo.elseUses.size();

    // Append killed -> kept
    kInfo.condUses.insert(kInfo.condUses.end(),
                          dInfo.condUses.begin(), dInfo.condUses.end());
    kInfo.thenUses.insert(kInfo.thenUses.end(),
                          dInfo.thenUses.begin(), dInfo.thenUses.end());
    kInfo.elseUses.insert(kInfo.elseUses.end(),
                          dInfo.elseUses.begin(), dInfo.elseUses.end());

    trail.movedCondCount = dInfo.condUses.size();
    trail.movedThenCount = dInfo.thenUses.size();
    trail.movedElseCount = dInfo.elseUses.size();

    dInfo.condUses.clear();
    dInfo.thenUses.clear();
    dInfo.elseUses.clear();

    // boolMark
    trail.keptOldMark  = kInfo.boolMark;
    trail.killedOldMark = dInfo.boolMark;

    BoolConstMark merged = mergeBoolMark(kInfo.boolMark, dInfo.boolMark);
    kInfo.boolMark = merged;
    dInfo.boolMark = BoolConstMark::None;

    iteOccMoveTrail_.push_back(trail);

    // Both -> conflict
    if (merged == BoolConstMark::Both) {
        pendingConflict_ = TheoryConflict{
            egraph_.explainEquality(trueTerm_, falseTerm_)
        };
        return;
    }

    // boolMark 新变成 const -> 扫描 condUses
    bool keptWasConst = (trail.keptOldMark == BoolConstMark::True ||
                         trail.keptOldMark == BoolConstMark::False);
    bool nowConst = (merged == BoolConstMark::True ||
                     merged == BoolConstMark::False);
    if (nowConst && !keptWasConst) {
        for (IteId iid : kInfo.condUses) tryFireIte(iid);
    }

    // then/else 可能相等 -> 扫描所有 thenUses/elseUses
    for (IteId iid : kInfo.thenUses) tryFireIte(iid);
    for (IteId iid : kInfo.elseUses) tryFireIte(iid);
}
```

### 2.5 唯一 saturation loop

```cpp
TheoryCheckResult EufSolver::check(TheoryLemmaDatabase&) {
    if (pendingUnknown_) return unknown();
    if (pendingConflict_) return conflict(*pendingConflict_);

    registerNewIteTerms();

    // 初始化 queue：已有的 SAT decision merges
    // （egraph 内部若有预存 merges，也应在此一次性转入 mergeQueue_）

    // 唯一 saturation loop
    while (!mergeQueue_.empty()) {
        auto req = mergeQueue_.back();
        mergeQueue_.pop_back();

        auto mr = egraph_.merge(req.a, req.b, req.reason);
        if (!mr.merged) continue;

        // 1. ITE metadata 合并：只 enqueue，不递归 merge
        onClassMerged(mr.kept, mr.killed);
        if (pendingConflict_) return conflict(*pendingConflict_);

        // 2. congruence closure：把新 merges enqueue 到同一 queue
        egraph_.refreshCongruence(mr.kept, mr.killed, mergeQueue_);
    }

    // disequality conflicts（保持现有 O(D) 扫描）
    ...
}
```

关键点：
- `egraph_.merge()` 只执行一次 unite，不处理 queue
- `onClassMerged()` 只 enqueue ITE merges，不调用 merge
- `egraph_.refreshCongruence()` 只 enqueue congruence merges，不自动 drain
- 所有 merges 由 `EufSolver::check()` 内的唯一 `while` 循环 drain

---

## Phase 3 — Rollback

### 3.1 push

```cpp
snapshots_.push_back({
    /* egraph snapshot */,
    IteSnapshot{
        iteOccMoveTrail_.size(),
        mergeQueue_.size(),
        nextTermToScan_
    }
});
```

### 3.2 pop — 严格逆序

```cpp
void EufSolver::backtrackToLevel(size_t level) {
    const auto& snap = snapshots_[level].ite;

    // 1. 丢弃未执行的 pending merges
    mergeQueue_.resize(snap.mergeQueueSize);
    mergeDedup_.clear();   // per-epoch dedup 随 batch 丢弃

    // 2. 回滚 ITE occurrence move / boolMark
    while (iteOccMoveTrail_.size() > snap.occMoveTrailSize) {
        auto t = iteOccMoveTrail_.back();
        iteOccMoveTrail_.pop_back();

        auto& kInfo = classInfo(t.kept);
        auto& dInfo = classInfo(t.killed);

        assert(kInfo.condUses.size() == t.keptCondOldSize + t.movedCondCount);
        assert(dInfo.condUses.size() == t.killedCondOldSize);

        // 把 kept 尾部搬回 killed（不能只做 resize，killed 需要恢复原始内容）
        auto moveTailBack = [](auto& kept, auto& killed,
                               size_t keptOldSize,
                               size_t killedOldSize,
                               size_t movedCount) {
            assert(kept.size() == keptOldSize + movedCount);
            assert(killed.size() == killedOldSize);
            killed.insert(killed.end(),
                          kept.begin() + keptOldSize, kept.end());
            kept.resize(keptOldSize);
        };

        moveTailBack(kInfo.condUses, dInfo.condUses,
                     t.keptCondOldSize, t.killedCondOldSize, t.movedCondCount);
        moveTailBack(kInfo.thenUses, dInfo.thenUses,
                     t.keptThenOldSize, t.killedThenOldSize, t.movedThenCount);
        moveTailBack(kInfo.elseUses, dInfo.elseUses,
                     t.keptElseOldSize, t.killedElseOldSize, t.movedElseCount);

        kInfo.boolMark = t.keptOldMark;
        dInfo.boolMark = t.killedOldMark;
    }

    // 3. 回滚 egraph union / signature trail
    egraph_.backtrackToLevel(level);

    // 4. nextTermToScan
    nextTermToScan_ = snap.nextTermToScan;
}
```

顺序：**metadata trail 先于 egraph trail 回滚**。

---

## Phase 4 — 测试

### 4.1 单元测试

| 测试名 | 说明 |
|--------|------|
| `ITE R1: ite(true, a, b) = a` | 条件 true → result=then |
| `ITE R2: ite(false, a, b) = b` | 条件 false → result=else |
| `ITE R3: a=b → ite(c, a, b) = a` | then=else → result=then |
| `ITE nested` | 嵌套 ITE 增量传播 |
| `ITE + UF` | ITE 与 congruence 交互 |
| `ITE disequality conflict` | distinct(ite(c,a,b), a) ∧ c=true → unsat |
| `ITE true=false conflict` | true/false 合并，含完整 explanation |
| `ITE backtrack` | push/pop 后状态恢复 |
| `ITE rollback opposite branch` | push c=true + pop + c=false，双向触发正确 |
| `ITE delayed cond merge` | 初始 c 未知，merge 后变 true，触发 result=then |
| `ITE delayed branch equality` | 初始 then≠else，merge 后相等，触发 R3 |
| `ITE hash-cons duplicate` | 同一个 ite(c,a,b) 多次出现，只注册一个 IteRecord |
| `ITE non-bool condition rejected` | 非 Bool 条件在更早阶段拒绝 |
| `ITE non-bool sorts` | Int/Real/UF 作为 result sort |

### 4.2 回归 SMT2

- `euf_030_sat_ite_true.smt2`
- `euf_031_unsat_ite_true_conflict.smt2`
- `euf_032_unsat_ite_branches_equal.smt2`
- `euf_033_sat_ite_nested.smt2`
- `euf_034_sat_ite_delayed_trigger.smt2`
- `euf_035_unsat_ite_rollback_opposite.smt2`

关键 case：

```smt2
(set-logic QF_UF)
(declare-fun c () Bool)
(declare-fun a () Int)
(declare-fun b () Int)
(push)
(assert (= c true))
(assert (distinct (ite c a b) a))
(check-sat)  ; unsat
(pop)
(assert (= c false))
(assert (distinct (ite c a b) b))
(check-sat)  ; unsat
```

---

## 复杂度

| 指标 | 旧方案 | 新方案 |
|------|--------|--------|
| check | O(T) | O(新增 term 数) |
| 每次 merge | 不触发 | O(killed occurrences) |
| 总开销 | O(checks × T) | O(M log N + firedRules) |

---

## 实施顺序

1. `EufTypes.h` — `IteId`、`IteRecord`、`MergeRequest`、`IteBranchesEqual`
2. `IncrementalEGraph.h/cpp` — 移除 `processMergeQueue()` 暴露，改为 `merge` + `refreshCongruence`（无 callback）
3. `EufSolver.h` — 数据结构、`mergeQueue_`、snapshot
4. `EufSolver.cpp` — `initializeBoolConstants`、`registerIte`、`tryFireIte`、`onEclassMerged`、唯一 saturation loop、rollback
5. 测试

---

## 修订记录

| 版本 | 变更 |
|------|------|
| v1 | 初始版本，含递归 callback merge |
| v2 | callback 改为只 enqueue；但 check() 仍为嵌套 drain（egraph.processMergeQueue + 外层 while） |
| v3 | **EufSolver 拥有唯一 saturation loop**；egraph 只提供原子操作（merge / refreshCongruence）；彻底移除 firedMask 语义；rollback 顺序写死为 metadata 先于 egraph；所有反馈全部落实 |
