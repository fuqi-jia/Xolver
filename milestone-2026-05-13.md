# NLColver Milestone — 2026-05-13

> 本里程碑文档记录截至 2026-05-13 NLColver 的实现状态，包括已完成的模块、关键设计决策、验证用例，以及待实现的 Stage 骨架和 TODO。

---

## 1. 项目概览

NLColver (**N**on**L**inear **Co**nstraint So**lver**) 是一个研究级 SMT/OMT 求解器平台，采用双引擎架构：

- **CDCL(T) / MCSAT** 精确内核 —— 用于可靠的 SAT/UNSAT 推理
- **Local Search Advisor** —— 用于启发式指导和 OMT 优化

**仓库**: `https://github.com/fuqi-jia/NLColver.git`

**当前阶段**: Stages A–E 功能完备，Stage I (NIA-Core) MVP 完成，F/G/H/J/K 为骨架状态。

---

## 2. 已实现的模块（详细）

### 2.1 Stage A — Bootstrap & Core Infrastructure ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **构建系统** | `CMakeLists.txt` | C++17，GMP/MPFR，nlohmann/json (FetchContent)，doctest (FetchContent) |
| **SOMTParser 集成** | `src/parser/`, `third_party/SOMTParser/` | Git submodule，FrontendAdapter 桥接，Rewriter 重写器 |
| **核心 IR** | `src/expr/` | CoreExpr / CoreIr，scope-aware assertions，ExprId/SortId/VarId 类型化 ID |
| **Atomizer** | `src/sat/Atomizer.cpp` | Tseitin CNF 转换 + 理论原子提取 |
| **Solver API** | `src/api/Solver.cpp` | `parseFile`, `checkSat`, `push/pop`, `dumpSMT2`，seed 选项 |
| **CLI** | `tools/cli/main.cpp` | solve, bench, trace, model-check, proof-check, version 子命令；**默认 solve**（不传子命令也可直接求解文件）|
| **模型验证** | `src/theory/ModelValidator.cpp` | 布尔表达式求值骨架 |
| **TraceRecorder** | `src/learning/TraceRecorder.h` | 仅记录结果和时间（完整 trace 待 Stage A+）|
| **Statistics** | `src/util/Statistics.h` | 统计骨架 |

**关键设计决策**:
- SOMTParser 已提供 hash-consing、rewriter、visitor，NLColver 不重新实现
- CoreIr 是轻量级稠密数组，用于 solver 专属元数据（literal IDs、proof IDs、scope levels），不替代 SOMTParser 的 DAG
- pImpl 模式用于公共 API 边界 (`Solver::Impl`)，避免在 public header 中暴露 libpoly/CaDiCaL 重头文件

---

### 2.2 Stage B — SAT Engine ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **CaDiCaL Wrapper** | `src/sat/CadicalSolver.cpp` | CaDiCaL (vendored submodule) 封装，理论传播接口 |
| **Stub Fallback** | `src/sat/UnitPropagator.cpp` | CaDiCaL 不可用时降级为单元传播桩 |
| **Theory Propagation** | `src/sat/CadicalTheoryPropagator.cpp` | CDCL(T) 回调：理论检查、冲突解释、引理注入 |

**编译宏**: `NLCOLVER_HAS_CADICAL` — 定义时表示 CaDiCaL 可用。

---

### 2.3 Stage C/E — LRA Solver (Simplex) ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **SimplexSolver** | `src/theory/arith/lra/SimplexSolver.h/.cpp` | 单变量边界传播，CDCL(T) 循环集成 |

**覆盖范围**: 单变量线性实数约束（ bound propagation ）。

**验证用例**:
| 输入 | 结果 |
|------|------|
| `x > 0 ∧ x < 10` | **sat** |
| `x > 0 ∧ x < 0` | **unsat** |
| `(p ∨ x>0) ∧ (¬p ∨ x<0) ∧ (x=0)` | **unsat**（LRA + bool 混合）|

---

### 2.4 Stage C/E — LIA Solver (Branch-and-Bound) ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **LiaSolver** | `src/theory/arith/lia/LiaSolver.h/.cpp` | 分支定界、GCD 强化不等式、动态原子注册表 |

**验证用例**:
| 输入 | 结果 |
|------|------|
| `2x ≤ 5 ∧ x ≥ 0` | **sat** |
| `2x = 1` (Int) | **unsat** |
| `x ≠ 0 ∧ x ≥ 0 ∧ x ≤ 0` | **unsat**（disequality）|

---

### 2.5 Stage D — NRA Solver (Grid Sampling) ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **NraSolver** | `src/theory/arith/nra/NraSolver.h/.cpp` | 网格采样、单变量 + 双变量多项式约束 |

**验证用例**:
| 输入 | 结果 |
|------|------|
| `x² > 2 ∧ x < 0` | **sat** |
| `x² > 2 ∧ x² < 1` | **unsat** |
| `x² + y² ≤ 1` | **sat**（2D）|
| `y = x² ∧ y < 0` | **unsat**（2D）|

---

### 2.5b Difference Logic (IDL / RDL) ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **IdlSolver** | `src/theory/arith/idl/IdlSolver.h/.cpp` | 整数差分逻辑 (QF_IDL)，Bellman-Ford 负环检测 |
| **RdlSolver** | `src/theory/arith/rdl/RdlSolver.h/.cpp` | 实数差分逻辑 (QF_RDL)，基于 DifferenceGraph |
| **DifferenceGraph** | `src/theory/arith/dl/DifferenceGraph.h` | 差分约束图数据结构 |
| **BellmanFord** | `src/theory/arith/dl/BellmanFord.h` | 最短路径 / 负环检测算法 |
| **DlExplanation** | `src/theory/arith/dl/DlExplanation.h` | 差分逻辑冲突解释 |
| **DlModel** | `src/theory/arith/dl/DlModel.h` | 差分逻辑模型生成 |

**测试**: `tests/unit/test_idl.cpp`, `tests/unit/test_rdl.cpp`

---

### 2.5c Interval Evaluation ✅

| 组件 | 文件 | 说明 |
|------|------|------|
| **IntervalEvaluator** | `src/theory/arith/interval/IntervalEvaluator.h/.cpp` | 多项式约束的区间求值 |
| **ReasonedBox** | `src/theory/arith/interval/ReasonedBox.h/.cpp` | 带推理原因的区间盒子 |
| **IntervalTypes** | `src/theory/arith/interval/IntervalTypes.h` | 区间类型定义（含 GMP 有理数边界）|
| **IntervalOperations** | `src/theory/arith/interval/IntervalOperations.h` | 区间算术运算 |

**注**: IntervalEvaluator 已从 `src/theory/arith/nia/` 迁移至独立的 `src/theory/arith/interval/` 目录，作为跨理论共享的基础设施。

---

### 2.6 Stage I — NIA-Core Solver ✅

NIA-Core 是 NLColver 最新完成的 MVP 模块，具备**完整的求解管道**和**可靠的冲突生成**。

#### 2.6.1 求解管道

```
assertLit (effective relation via negateRelation)
    ↓
NiaNormalizer (clear denominators, strict → non-strict)
    ↓
Trivial constants (constant contradiction → Conflict)
    ↓
LinearNiaDomainReasoner (single-var linear bounds)
    ↓
UnivariateIntegerReasoner (RRT integer roots, square bounds)
    ↓
AlgebraicIntegerReasoner (square rules, GCD conflict, modular reasoning)
    ↓
Empty domain check → Conflict
    ↓
BoundedNiaSolver (direct enumeration over finite domains)
    ↓
NiaLocalSearch (heuristic candidate SAT finder)
    ↓
Branch lemma or Unknown
```

#### 2.6.2 子引擎详解

| 子引擎 | 文件 | 功能 |
|--------|------|------|
| **NiaNormalizer** | `NiaNormalizer.h/.cpp` | 清除分母，严格关系转非严格 |
| **LinearNiaDomainReasoner** | `LinearNiaDomainReasoner.h/.cpp` | 单变量线性边界推导 |
| **UnivariateIntegerReasoner** | `UnivariateIntegerReasoner.h/.cpp` | RRT 整数根，平方边界 |
| **AlgebraicIntegerReasoner** | `AlgebraicIntegerReasoner.h/.cpp` | 平方规则、GCD 冲突、模运算推理 |
| **BoundedNiaSolver** | `BoundedNiaSolver.h/.cpp` | 有限域直接枚举 |
| **NiaLocalSearch** | `NiaLocalSearch.h/.cpp` | 启发式候选 SAT 搜索 |
| **IntegerModelValidator** | `IntegerModelValidator.h/.cpp` | 整数模型验证 |
| **DomainStore** | `DomainStore.h/.cpp` | 变量域存储与管理 |
| **NiaSolver** | `NiaSolver.h/.cpp` | 总控，调度上述引擎 |

#### 2.6.3 冲突类型（Soundness 保证）

NIA 是不可判定问题。NLColver 的 UNSAT 结论基于以下**可靠冲突**：
- 常数矛盾
- 空根集
- 模运算矛盾
- GCD 矛盾
- 有限域穷尽

对于无界情况，`Unknown` 是可接受的；永远不会从不完整的推理中发出 UNSAT。

#### 2.6.4 验证用例

| 逻辑 | 输入 | 结果 |
|------|------|------|
| QF_NIA | `x² = 4` | **sat** |
| QF_NIA | `x² = 2` | **unsat** |
| QF_NIA | `0 ≤ x ≤ 10 ∧ x² = 49` | **sat** |
| QF_NIA | `0 ≤ x ≤ 10 ∧ x² = 50` | **unsat** |
| QF_NIA | `x² + y² = 3` | **unsat**（模运算）|
| QF_NIA | `0 ≤ x ≤ 3 ∧ 0 ≤ y ≤ 3 ∧ xy = 6` | **sat** |

---

### 2.7 其他基础设施 ✅

| 组件 | 说明 |
|------|------|
| **TheoryManager** | 调度所有已注册求解器，每个求解器静默忽略不支持的约束 |
| **TheoryAtomRegistry** | 理论原子（AtomId = theory + poly + relation）的动态注册 |
| **PolynomialKernel** | 通过 libpoly (vendored) 提供规范稀疏多项式表示 |
| **ModelValidator** | 对原始断言进行布尔表达式求值验证（Sat 结果必须通过验证）|
| **SmallVector** | `src/util/SmallVector.h`，用于 CoreExpr 短子列表的默认容器 |

---

## 3. 骨架 / 未实现模块

### 3.1 Stage F — IncrementalLinearizer 🏗️

| 文件 | 状态 | 描述 |
|------|------|------|
| `src/theory/arith/IncrementalLinearizer.h/.cpp` | Skeleton | 引理生成接口就绪，但 sign/interval/McCormick 引理未实现 |

**目标**: 将非线性约束增量线性化为 lemmas，供 CDCL(T) 使用。

---

### 3.2 Stage G — LocalSearchAdvisor 🏗️

| 文件 | 状态 | 描述 |
|------|------|------|
| `src/search/LocalSearchAdvisor.h/.cpp` | Skeleton | 模型提案接口就绪 |

**待实现**:
- 代价函数（cost function）
- 移动生成器（move generator）
- 禁忌表（tabu list）
- 重启策略（restart policy）

---

### 3.3 Stage H — McsatSolver 🏗️

| 文件 | 状态 | 描述 |
|------|------|------|
| `src/mcsat/McsatSolver.h/.cpp` | Skeleton | MCSAT 引擎接口就绪 |

**待实现**:
- 理论轨迹（theory trail）
- 值决策（value decisions）
- 可行集（feasible sets）
- 与局部搜索 advisor 和理论传播的集成

---

### 3.4 Stage J — ProofManager 🏗️

| 文件 | 状态 | 描述 |
|------|------|------|
| `src/proof/ProofManager.h/.cpp` | Skeleton | SAT/理论证明跟踪接口就绪 |

**待实现**:
- Alethe 证明格式导出
- LFSC 证明格式导出
- 当前仅返回 `"; not yet implemented"` 桩字符串

---

### 3.5 Stage K — Optimize (OMT) 🏗️

| 文件 | 状态 | 描述 |
|------|------|------|
| `src/omt/Optimize.h/.cpp` | Skeleton | 单目标优化接口就绪 |

**待实现**:
- OMT 优化循环（目标函数二分搜索 + checkSat 调用）
- 目标函数类型检测（线性 vs 多项式）
- 见证赋值（witness assignment）存储

---

### 3.6 NIA-Core 待完善

| 文件 | 描述 |
|------|------|
| `src/theory/arith/nia/NiaLocalSearch.h` | 仅尝试少量候选赋值，搜索策略待增强 |
| `src/theory/arith/nia/BoundedNiaSolver.h/.cpp` | 大范围区间的分支定界 (B&B) 是骨架实现 |
| `tests/unit/test_nia_core.cpp:616` | Factor 引理（`xy=0 ⇒ x=0 ∨ y=0`）未实现 |

---

### 3.7 多项式内核 (LibPolyKernel) 待改进

| 文件 | 描述 |
|------|------|
| `src/theory/arith/poly/LibPolyKernel.cpp:46` | 有理数系数处理：需通过缩放或 Q-环正确支持 |
| `src/theory/arith/poly/LibPolyKernel.cpp:190` | 多变量检测的项遍历优化 |

---

### 3.8 API 层空实现

| 文件 | 函数 | 状态 |
|------|------|------|
| `src/api/Solver.cpp:221` | `boolSort()` | 返回空 Sort |
| `src/api/Solver.cpp:222` | `intSort()` | 返回空 Sort |
| `src/api/Solver.cpp:223` | `realSort()` | 返回空 Sort |
| `src/api/Solver.cpp:224` | `bvSort(uint32_t)` | 返回空 Sort（位向量）|
| `src/api/Solver.cpp:225` | `fpSort(uint32_t, uint32_t)` | 返回空 Sort（浮点）|
| `src/api/Solver.cpp:227` | `mkConst(Sort, string_view)` | 返回空 Term |
| `src/api/Solver.cpp:228` | `mkVar(Sort, string_view)` | 返回空 Term |
| `src/api/Solver.cpp:229` | `mkBool(bool)` | 返回空 Term |
| `src/api/Solver.cpp:230` | `mkInt(int64_t)` | 返回空 Term |
| `src/api/Solver.cpp:231` | `mkReal(const string&)` | 返回空 Term |
| `src/api/Solver.cpp:232` | `mkOp(uint32_t, vector<Term>)` | 返回空 Term |
| `src/api/Solver.cpp:235` | `assertFormula()` | build term and assert（待实现）|
| `src/api/Solver.cpp:247` | `getModel()` | 模型构造完成后需过滤内部变量 |

---

### 3.9 其他零散 TODO

| 模块 | 文件 | 描述 |
|------|------|------|
| Rewriter | `src/expr/rewriter.cpp:17` | 注册自定义重写规则 `onGT`, `onGE` 等 |
| Learning | `src/learning/TraceRecorder.h:14` | 完整 trace 记录（目前仅记录结果和时间）|
| SAT | `src/sat/CadicalTheoryPropagator.cpp` | 理论检查回调优化 |
| CLI | `tools/cli/main.cpp` | `bench`, `trace`, `model-check`, `proof-check` 子命令均为桩实现 |

---

## 4. 工具与测试

### 4.1 Benchmark Runner（本次新增）

| 文件 | 功能 |
|------|------|
| `tools/run_benchmark.py` | 一键 benchmark 运行器：支持多线程并行、timeout 控制、Z3 对拍、单文件 HTML 报告生成 |

**特性**:
- 参数：`--logic`, `-j` (jobs), `-t` (timeout), `--compare-with` (Z3/cvc5), `--max-files`, `--filter`
- 输出：`summary.txt`, `results.csv`, `report.html` (独立单文件，内嵌 CSS/JS), `discrepancies.txt`, `errors.txt`, `top_slow.txt`, `category_summary.txt`, `statistics.json`
- HTML 报告包含：概览卡片、SVG 饼图、时间统计、可搜索过滤的结果表格、Mismatch/Diff/Timeout/Error 异常专区、分类统计、Top 50 最慢实例

### 4.2 测试覆盖

| 类型 | 框架 | 说明 |
|------|------|------|
| Unit Tests | doctest | `tests/unit/`，涵盖 bool/LRA/LIA/NRA/NIA 核心用例 |
| Regression | SMT2 | `tests/regression/nia/`，NIA 端到端 SMT2 文件 |
| CLI 测试 | 手动 | `nlcolver solve file.smt2` 已验证 QF_BOOL/QF_LRA/QF_LIA/QF_NRA/QF_NIA/QF_UF |

---

## 5. 架构不变式（Invariants）

1. **Soundness 边界**: `Result::Sat` 必须由 `ModelValidator` 对原始断言进行验证。局部搜索、MCSAT 值提议、NIA bit-blast 结果均为**候选**，必须通过精确内核验证后才能返回。
2. **Advisor 模式**: 所有启发式（局部搜索、学习模块、组合调度器）通过 `Advisor::propose() → Proposal → policy.accept()` 流动，启发式**绝不**直接写入 solver 状态。
3. **三种表达式视图分离**:
   - DAG 视图 (`Expr`): 用于重写、证明、美化打印
   - 多项式视图 (`PolyId`): 用于理论推理
   - 求值视图: 用于局部搜索增量评分
4. **Atomizer 分离 SAT 文字与理论原子**: 理论原子 (`AtomId`) 不是 SAT 变量；`b_i ↔ atom_i` 的抽象由 Atomizer 管理。
5. **CDCL(T) 为主循环；MCSAT 为并行研究路径**: 理论求解器实现两个接口（`TheorySolver` 用于 CDCL(T)，`McsatSolver` 用于基于 trail 的推理），不合并它们。
6. **NIA Soundness > Completeness**: NIA 不可判定。SAT 需要精确整数验证；UNSAT 需要可靠证明；Unknown 对于无界情况是可接受的。

---

## 6. 下一步建议（按优先级）

| 优先级 | 任务 | 理由 |
|--------|------|------|
| P0 | **修复 LRA/NIA 大规模 benchmark 的 parser 兼容性** | 当前 Heizmann/VeryMax 等 benchmark 导致大量 error，需诊断具体不支持的 SMT-LIB 语法 |
| P1 | **API 层实现** (`mkBool`, `mkInt`, `assertFormula` 等) | 使 C++ API 可用，支持程序化建模 |
| P2 | **Factor 引理** (`xy=0 ⇒ x=0 ∨ y=0`) | NIA-Core 完整性的关键缺口 |
| P3 | **Stage G — LocalSearchAdvisor** | 提升 NIA 有界实例的 SAT 发现能力 |
| P4 | **Stage F — IncrementalLinearizer** | 为非线性约束生成 lemmas，增强 CDCL(T) 推理 |
| P5 | **Stage H — McsatSolver** | 长期研究方向，NLSAT 引擎 |
| P6 | **Stage J — ProofManager** | 证明产出，用于 SMT-COMP / 形式化验证场景 |
| P7 | **Stage K — Optimize (OMT)** | 优化扩展，OMT 求解 |

---

*文档生成时间: 2026-05-13*
*对应 commit: `4ac56a9` (benchmark runner) + `2c03182` (CLI default solve) + `869d543` (implementation process docs)*
