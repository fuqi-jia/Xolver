# Gate 语义盘点

2026-10-23 补查：另删除无源码使用者的 CMake `XOLVER_ENABLE_TRACING`，移除旧默认值推广工具 `tools/tuning/autotune.py` 并修正遗留注释。已知活跃遗留 gate 仍为 0，清单外累计移除 8 项；161 个诊断/资源/策略配置保留。最终说明见 [清理收尾记录](GATE-CLOSEOUT.md)。下文保留原始时间点及失败记录。

2026-10-22 当前：本批删除12项遗留gate（7命名、5内部），已盘点余项为0；原171项清单全部移除，清单外累计7项。MCSAT/NLSAT实现及直接测试保留。当前161控制/237读取，分别为88诊断、66资源、7策略。Panda1最终版本833项相关单测通过；902例差分无错答、错误或新增求解回退，但77次模型检查中1次因20秒超时未通过，严格验收仍为失败。该难例在旧版/新版15次复核中13次超时，尚未修复。计数覆盖已审计范围，不是无遗漏的形式化证明。

最新证据：[batch12清理与验收记录](evidence/gate-batch-12/README.md)。

## 之前的快照（下文不是当前状态）


2026-10-22 batch12：最后7个已知实验开关已删除，MCSAT/NLSAT实现保留并改用直接接入的测试。171项原清单已全部移除；另2项清单外残留已移除。当前161控制/237读取（88诊断、66资源、7策略），静态分层检查0违规；本批服务器验收待完成。以下为此前证据与历史计数。

2026-10-22 当前：已知171项批次清单中164项已移除，7项MCSAT/NLSAT实验依用户要求暂留；另移除2项清单外残留。最近一轮实际清理47项，并修复数组重建、DT校验三态语义及组合函数模型问题。Panda1最终验收：828项相关单测、902例差分、76次模型检查、18次外部模型重放通过；无错答、错误、新增回退或unknown，新旧版本各6例超时。当前168个类型化控制/244处读取，其中88诊断、66资源、7策略、7保留实验。计数不是全程序无遗漏的形式化证明。完整PA/SL仍是后续工作。

最新证据见[最终批次记录](evidence/gate-batch-11/README.md)。

## 历史快照（以下数字不是当前计数）


2026-10-22 验收更新：47 项源码清理已落地，MCSAT/NLSAT 7 个实验控制依用户要求暂留。batch09 严格验收失败：815/817 单测通过，902 差分无错答，1 例 UNSAT→unknown、2 例旧模型失败。已归档1137个证据文件。batch10 已修正数组模型重建和 DT 三态语义，服务器增量编译通过，运行验证中；当前168控制/244读取。下文较早计数与状态均为历史记录。

2026-10-22 补查：另删除 portfolio 包装层和内部数值数组开关，本轮累计 47 项。当前 168 控制／245 读取，已知保留 7 项 MCSAT/NLSAT；原清单外两处残留已处理。生产二进制已编译，单测编译暴露旧 A/B 循环残片，已修正并准备再次服务器验证；尚无本批运行测试结论。

2026-10-22 最新：batch07-08 整批移除 45 项、6 个专属控制、21 个文件，净减 5536 行。原命名清单剩 7 项，均为用户要求暂留的 MCSAT/NLSAT 实验；170 个剩余命名控制包含资源、诊断、策略及这 7 个实验控制，不能称为 170 个 gate。静态分层和类型读取通过；服务器验收待完成。上一批 43 项在编译时发现残留 `row2Split` 引用，已在本批修正；那次失败未执行求解测试。尚须扫描原清单以外的遗留控制，不能宣称所有 gate 已清零。

2026-10-22 当前更新：batch03-05 的 44 项删除已完成编译，593 单测通过；776 差分无新增错答或回退，仍有 2 例已有模型检查失败。batch04-06 又实际移除 43 项，221 控制／307 读取，静态分层检查通过，服务器验证待完成。已知余项 52：其中 MCSAT/NLSAT 相关 7 项依用户新指示暂留，其余 45 项继续清理。以下逐步记录是历史快照；当前批次见 [记录](evidence/gate-batch-04-06/README.md)。


**当前源码：345 个命名控制、456 处读取，134 项确认遗留 gate + 16 项待判定。已验收 47 个逐项步骤；批次 1 已删除 14 个 gate 和 4 个专属控制项，待服务器验收。另有 6 项内部／CLI 残留，合计 156 项待清理；全库盘点尚未穷尽。**

**第 21 项审计快照：375 个命名控制、489 个字面读取。其中 160 个已确认属于遗留功能开关，另有 16 个未决。** 因而仅在这 375 项范围内，功能开关待清理数的分类区间为 **160–176**；这不是全库 gate 总数，也不是可直接删除的实现数量。

审查日期：2026-10-22。基准为本地移除 `XOLVER_NIA_BITBLAST_NOPRE` 后的源码；当时第 21 项服务器验收尚未完成，上一个已验收第 20 项二进制仍对应 376 个控制 / 491 处读取。计数反映源码状态，不替代服务器验收。

后续验收：第 21 项已通过 Panda1 / ExperimentOS 运行 `d6721094e813`，见[结果与完整证据](evidence/gate-0021/README.md)。本表 375 / 489 的盘点基准及分类数未变。

| 类别 | 数量 | 处理原则 |
|---|---:|---|
| 诊断、观测及调试核验 | 103 | 保留并统一观测接口；不算求解算法 feature gate。 |
| 需进一步审查 | 16 | 未决，继续跟踪正确性契约、默认差异及公开策略定位；不计入已确认遗留 gate 下界。 |
| 已确认遗留功能开关 | 160 | 逐项去掉历史功能门：有用算法保留并接入，无用实现经证据确认后删除；先通过服务器验证。 |
| 资源预算和上限 | 85 | 保留必要资源限制并核对值域/溢出；只有所属算法删除后才删除专属资源参数。 |
| 正常策略选择和调度参数 | 11 | 保留明确策略/数值选择，迁移到有类型的策略配置；不靠是否为 Boolean 自动判断。 |

“已确认”表示读取点确实保留了功能启停、A/B 逃生口、实验替代路径或多层默认配置；不表示该功能错误、无用或可不经验证删除。默认 OFF 也不等于不用：CLI 默认表仍写入 **31 个当前有效名字**，portfolio 另有 cuts 臂配置；局部搜索还存在直接 setter 和单测调用。应去掉开关、保留有用算法，还是连同无用实现删除，必须逐项决定。

本表人工读取配置调用及上下文后归类，未作全程序控制流证明、运行覆盖证明或完整历史使用分析。不能把自动 census 的名字分类当成语义结论：`NRA_CAC_SAT_SAMPLE` 实际尝试模型搜索；`COMB_ARRAY_NIA`、`TARGETED_PP` 等数值项实际是开关；`NIA_LS_LONG` 是预算快捷配置；`EUF_INCREMENTAL_PROP_VERIFY` 同时开启算法，因此列为未决。

诊断类可以有开销或调试中止：`ASSERT_PF_INV` 发现违例会 abort，`NIA_CT_DIAG` 还执行诊断子查询。分类不宣称打开观测完全不影响时间或进程行为。资源类包含算法规模 cap，不应为减少 gate 数而删除可靠性保护。正常策略类也不意味着配置设计已最终定型。

## 快照后的增量

第 22 项 `XOLVER_NIA_BB_CONGRUENCE` 和第 23 项 `XOLVER_NIA_PER_BRANCH_BB`
已通过服务器验收。第 24 项已删除 `XOLVER_NIA_LS_FARKAS_INIT`，
连同专属初始化槽、状态及接口一起移除，并通过服务器验收。
第 25 项已移除 `XOLVER_NIA_LS_DIVERSE_INIT` 及专属初始化轮换，
通过服务器运行 `05386cabfc79`：226 单测、327 差分、47 模型检查、63 双 oracle；
无错答、进程错误或新增退化，1 例新旧共同超时。
第 26 项已删除 `XOLVER_NIA_LS_SMART_MOVE` 及专属根候选生成实现，并通过服务器验收。
第 27 项修复整数 ICP 传播、预算及分派缺陷，并移除内部 `enableIcp_`，已通过服务器验收。
第 28 项修复有限集合交集边界的冲突理由，并移除内部 `enableGcd_`，已通过服务器验收。
第 29 项已移除内部 `enableModular_`，模推理及独立结果核验保留，并通过服务器验收。
运行 `36db3068e6bd` 的 278 单测、227 差分、46 严格模型和 60 双 oracle 检查通过，
无错答或新增退化，3 例新旧共同超时；[本项证据](evidence/gate-0029/README.md)的 1,045 个归档成员已校验。
第 30 项已移除内部 `enableRefute_` 并通过服务器验收：300 单测、227 差分，2 例共同超时，无错答或新增退化。
第 31 项已移除内部 `normCache_`，修复三类服务器已复现的实数线性化错误并拆开共享线性化层对整数规范化的依赖；333 单测／40,564 断言、457 差分、47 严格模型、60 双 oracle 通过，4 例共同超时。
第 32 项已删除 `XOLVER_PP_LET_ELIM` 的悬空 CLI／单测写入及重复用例，保留五种 let 语义回归；316 单测／40,325 断言、348 差分、47 模型及 60 双 oracle 通过，1 例共同超时，1,051 个归档成员已校验。
第 33 项已完整移除默认关闭且未发现生产启用者的 `SmartInit` 实验，共 847 行；305 单测／40,400 断言、227 差分、48 模型及 60 双 oracle 通过，候选 1 例／基线 2 例超时，1,045 个归档成员已校验。
第 34 项旧代码的有理数 ICP 预算／冲突理由缺陷已复现（3 测试／13 失败断言），修复及 `enableSplitSuggestion` 悬空字段删除已通过验收：452 单测／40,975 断言、457 差分、47 模型及 60 双 oracle，3 例共同超时；2,017 个归档成员已校验。
第 35 项已删除无读写者的 `enableBoundPropagationLemma` 字段并验收：424 单测／40,811 断言、227 差分、47 模型和 60 双 oracle 通过，1 例共同超时；1,046 个证据成员已校验。
第 36 项已删除无读写者的 `enableTracing` 字段并验收：424 单测／40,811 断言、227 差分、47 模型和 60 双 oracle 通过，1 例共同超时；1,046 个证据成员已校验。
第 37 项已删除 `maxSplits` 及无生产者／消费者的 `SplitSuggestion` 枚举、载荷、结果槽和空初始化，修正相邻 factory 旧说明；424 单测／40,811 断言、227 差分、47 模型和 60 双 oracle 通过，1 例共同超时，1,046 个证据成员已校验。
第 38 项已完整删除默认关闭的 `XOLVER_NIA_MODULAR_WARM_START` 缓存、哈希、专属状态和重置，普通模推理及独立核验保留；424 单测／40,811 断言、227 差分、46 模型和 60 双 oracle 通过，2 例共同超时，1,046 个证据成员已校验。
第 39 项提前处理服务器已复现的 NRA 无效等式传播：删除 `XOLVER_NRA_CAC_COMB_SAT` 实验、错误推导、缓存、同一开关的 CAC 接受分支及专属声明，保留正常排列与组合回退；471 单测／41,012 断言、原触发环境、457 差分、48 模型及 60 双 oracle 通过，2 例共同超时，2,019 个证据成员已校验。
第 40 项已删除默认关闭且无启用调用者的自适应 plateau 实验、字段、setter 和控制；424 单测／40,811 断言、227 差分、47 模型及 60 双 oracle 通过，1 例共同超时，1,046 个证据成员已校验。
第 41 项已完整删除默认关闭且无启用调用者的 atom-local-accept 实验、提交分支、状态、setter 和控制；424 单测／40,811 断言、227 差分、47 模型及 60 双 oracle 通过，1 例共同超时，1,046 个证据成员已校验。
第 42 项已删除常真内部字段 `enableSubtropical_` 及唯一早退，保留模型搜索和精确核验；462 单测／41,002 断言、457 差分、47 模型及 60 双 oracle 通过，2 例共同超时，1,047 个证据成员已校验。
第 43 项已删除常真内部字段 `enableSignRefute_` 及唯一早退，保留符号推理和冲突理由；471 单测／41,012 断言、457 差分、47 模型及 60 双 oracle 通过，2 例共同超时，1,047 个证据成员已校验。
第 44 项修复服务器已复现的整数规范化／引理错误并删除 LIA safe-mode：511 单测／44,866 断言、736 差分、47 模型和 61 双 oracle 通过；原协议漏算一个增量 oracle 用例，另经只读审计校正验收。候选 2 例／基线 3 例超时，无错答或新增回退；1,086 个证据成员已校验。
第 45 项已删除常真内部字段 `enableCac_`、唯一早退和诊断值读取，保留覆盖算法、候选核验和冲突理由；523 单测／41,190 断言、457 差分、47 模型及 60 双 oracle 通过，2 例共同超时，无错答或新增退化，1,050 个证据成员已校验。
第 46 项已完整删除默认关闭且无启用调用者的 RW_HUB 实验、字段、setter 和控制；普通随机游走保留，424 单测／40,811 断言及两组父模式测试（各 36 单测／86 断言）、227 差分、47 模型、60 双 oracle 通过；候选 1 例／基线 2 例超时，无错答或新增退化，1,052 个证据成员已校验。
第 47 项 RW_LADDER 已验收：424 单测／40,811 断言、两组父模式测试各 36 项、227 差分、47 模型和60双oracle通过；1,052个归档成员已核验。
当前源码为 **328 个命名控制 / 438 处读取，121 项确认 gate + 16 项未决 + 1 项内部残留，共 138 项**。
用户已改为按模块批量清理默认 OFF 和 ON 控制，后续采用 [8 批清单](GATE-BATCH-PLAN.json)。批次1整组删除未被生产配置启用的二层局部搜索、缓存和分支提示；生产普通 WalkSAT 保留并移除启停开关。413 单测和 ASan 通过；267 差分无答案退化，2 项严格模型失败在旧基线复现，保留原始失败结果。批次2已删除18项及4项专属资源控制，静态检查通过，服务器验证待完成。
下列逐项表和源码 hash 保留第 21 项审计快照；JSON 的 `current_delta` 记录
之后的差异，不将旧行号冒充新快照。证据见 [gate-0022](evidence/gate-0022/README.md)、
[gate-0023](evidence/gate-0023/README.md)
、[gate-0024](evidence/gate-0024/README.md)
和 [gate-0025](evidence/gate-0025/README.md)。

本次扩展成员字段审查又确认三处：NRA 的 `enableSubtropical_`、`enableSignRefute_` 常真开关，以及 SAT 的 `decideSteer_` 悬空字段。它们未被先前的命名控制读取清单覆盖，发现时均尚未删除；见 [引用及源码哈希](INTERNAL-GATE-FINDINGS.json)。因此当时已知剩余数增加三项，未改变已验收进度。
第 36 项送测期间进一步发现 `NraSolver::enableCac_`：常真字段，除阶段早退读取外还有一处诊断输出引用，没有设置入口。此项另计入待清理数，当时额外内部／CLI 残留为 10 项；当前数见页首。

第 44 项送测期间另发现 `CacEngine::Config::inloopPrune`：结构默认关闭，生产 `NraSolver` 固定开启，循环内仍保留启停分支；先前命名控制盘点没有计入这项内部 gate。其算法在生产使用，须保留并单独核验后去掉开关。此项已加入页首剩余数。

## 基准与证据

- Git HEAD：`e927757f5a033e244e96d7d41234866fb783d038`。工作树已有大量未提交修改，不能只用 HEAD 复现本表。
- `src/base/controls.json` SHA256：`94194e2be4bff16f03d3f191af9c2e7a4a8eb050cc117e9c97b55b435163befa`。
- [机器可读清单](GATE-INVENTORY.json) 保存全部 489 个读取点的完整调用、fallback 表达式、上下文、行号和读取源文件 hash；另保存补充定义位置、配置引用与 setter 证据。
- 每行“缺省”指 API/库调用的缺省语义。CLI baked 值另列，用户环境及实例配置可覆盖。Presence 的 unset 为 false，但任何已设置文本（包括 `0`）均为 true；Flag、Boolean、ExactZero 各有不同解析规则，见 `src/base/RuntimeConfig.cpp`。
- 对状态成员或局部参数推导了实际缺省；“读取 0 保留成员 N”与有效缺省为 0 不同。预算还可能按求解墙钟缩放。

配置引用搜索覆盖 `src, include, app, tests, tools, README.md, CMakeLists.txt`，共 860 个所选文本文件。未扫描 `build/`、`docs/`（含历史 evidence）、`third_party/`、外部基准档案、服务器独有配置和外部 API 客户端。

引用搜索包括引号形式的控制名及非整行注释中的 `NAME=value`。引用可以是测试、脚本预设、示例或注释，并不证明实际执行。表中“未见字面引用”只表示此限定搜索没有发现，不能推出全库无用；动态组合名称、直接 setter 和外部环境可能绕过字面名字。21 个 NIA 局部搜索控制另外追踪了对应 setter 字面调用，其余 setter 未穷尽。

## 未纳入这 375 项的内部与 CLI 门

下列是已确认存在的额外入口或冗余状态示例，**没有混入上述分母，也不是穷尽清单**。不能据此把全库剩余数简单写成 160 或 176。

| 名称 | 缺省和作用 | 位置 |
|---|---|---|
| `--lia-safe-mode / lia-safe-mode` | false；关闭 aggressive LIA integer reasoning；需要固定正确算法或明确保留受限模式契约。 | [app/main.cpp:231](../../app/main.cpp#L231), [src/runtime/Solver_impl_checksat.cpp:1221](../../src/runtime/Solver_impl_checksat.cpp#L1221), [src/search/lia/LiaSolver.h:38](../../src/search/lia/LiaSolver.h#L38) |
| `--lia-ultra-safe-mode / lia-ultra-safe-mode` | false；选择仅 LRA relaxation 的整数受限路径；须检查结果完备性和候选验证。 | [app/main.cpp:233](../../app/main.cpp#L233), [src/runtime/Solver_impl_checksat.cpp:1225](../../src/runtime/Solver_impl_checksat.cpp#L1225), [src/search/lia/LiaSolver.h:42](../../src/search/lia/LiaSolver.h#L42) |
| `--lia-enable-single-var-tightening` | false（runtime options 覆盖）；单独重新开启 single-var integer tightening。 | [app/main.cpp:235](../../app/main.cpp#L235), [src/runtime/Solver_impl_checksat.cpp:1229](../../src/runtime/Solver_impl_checksat.cpp#L1229), [src/search/lia/LiaSolver.h:49](../../src/search/lia/LiaSolver.h#L49) |
| `--lia-enable-gcd-ineq-tightening` | false（runtime options 覆盖）；单独重新开启 GCD inequality tightening。 | [app/main.cpp:237](../../app/main.cpp#L237), [src/runtime/Solver_impl_checksat.cpp:1233](../../src/runtime/Solver_impl_checksat.cpp#L1233), [src/search/lia/LiaSolver.h:52](../../src/search/lia/LiaSolver.h#L52) |
| `--lia-enable-eq-gcd-normalization` | false（runtime options 覆盖）；单独重新开启 equality GCD normalization。 | [app/main.cpp:239](../../app/main.cpp#L239), [src/runtime/Solver_impl_checksat.cpp:1237](../../src/runtime/Solver_impl_checksat.cpp#L1237), [src/search/lia/LiaSolver.h:55](../../src/search/lia/LiaSolver.h#L55) |
| `NiaSolver::enableIcp_` | 第 27 项源码已移除；先复现并修复 ICP 传播、预算及分派缺陷，已通过服务器验收。 | [src/search/nia/NiaSolver.h:200](../../src/search/nia/NiaSolver.h#L200), [src/search/nia/NiaSolver_engines.cpp:392](../../src/search/nia/NiaSolver_engines.cpp#L392) |
| `NiaSolver::enableGcd_` | true；私有字段只有初始化与 stageGcdDivisibility 早退读取，无设置入口；第 28 项已移除并通过服务器验收。 | [src/search/nia/NiaSolver.h](../../src/search/nia/NiaSolver.h), [src/search/nia/NiaSolver_refute.cpp](../../src/search/nia/NiaSolver_refute.cpp) |
| `NiaSolver::enableModular_` | true；私有字段只有初始化与 stageModular 早退读取，无设置入口；与另有命名控制的 warm-start 缓存分别处理。 | [src/search/nia/NiaSolver.h](../../src/search/nia/NiaSolver.h), [src/search/nia/NiaSolver_refute.cpp](../../src/search/nia/NiaSolver_refute.cpp) |
| `NiaSolver::enableRefute_` | true；私有字段只有初始化与 stageProductPositivity 早退读取，无设置入口；算法继续保留。 | [src/search/nia/NiaSolver.h](../../src/search/nia/NiaSolver.h), [src/search/nia/NiaSolver_refute.cpp](../../src/search/nia/NiaSolver_refute.cpp) |
| `NiaSolver::normCache_` | true；私有字段只有初始化与 stageNormalize 条件读取，无设置入口；删除冗余字段时仍须保留 interface equality 生命周期决定的缓存适用条件。 | [src/search/nia/NiaSolver.h](../../src/search/nia/NiaSolver.h), [src/search/nia/NiaSolver_linear.cpp](../../src/search/nia/NiaSolver_linear.cpp) |
| `XOLVER_PP_LET_ELIM（只写无命名 reader）` | CLI baked 写入 1；CLI kFlags 仍含此名字，但本次命名 reader 清单无该项；这是悬空默认设置，不能为了凑分母把它加入 375。 | [app/main.cpp:747](../../app/main.cpp#L747) |

第 27 项检查时发现的内部残留（历史快照，当时均未删除）：`IcpConfig::enableSplitSuggestion`、
`enableBoundPropagationLemma`、`enableTracing` 三个开关，以及无消费者的 `maxSplits`
预算字段。对 `src/app/include/tests/tools/python` 的搜索仅命中声明。它们不计入
命名 gate 数；第 27 项已在源码删除上表的 `enableIcp_`，第 28 项又删除 `enableGcd_`，第 29 项又在源码删除 `enableModular_`，当时其余 12 项额外清理项仍待处理；当前状态以本页首段及 JSON 的 `current_delta` 为准。
ICP 算法缺陷已由服务器复现 13 个失败断言；修复和删除已通过最终验收。

## 逐项清单

每一项的读取点源码上下文、配置引用文本、确切 reader 和处置依据都在 JSON 中。以下表按语义类别排列；“引用”仅表示上述限定范围中发现的静态引用。

### 已确认遗留功能开关（160）

| 控制 | 缺省 | 语义与处置依据 | 读取位置 | 启用/配置证据 |
|---|---|---|---|---|
| `XOLVER_ARRAY_CONGR_EXT` | false (unset) | 数组 UF congruence/extensionality 附加路径，库 OFF、CLI baked ON。 | [src/search/euf/EufSolver_array.cpp:98](../../src/search/euf/EufSolver_array.cpp#L98) | CLI baked=1；测试字面引用 1 处；赋值形引用 1 处 |
| `XOLVER_ARRAY_NOARR_DOWNGRADE` | true | 没有数组和 UF 时降级到实际算术逻辑，默认 ON 的禁用逃生口。 | [src/runtime/Solver_impl_checksat.cpp:884](../../src/runtime/Solver_impl_checksat.cpp#L884) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_FIXPOINT` | false (unset) | 数组公理饱和 fixpoint，源码标注 L3/default-OFF。 | [src/search/euf/EufSolver.cpp:86](../../src/search/euf/EufSolver.cpp#L86) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_LAZY` | false (unset) | lazy/eager completion 双路径，源码与 CLI 注释记录默认 OFF 及历史完备性回退。 | [src/search/array/ArrayReasoner.cpp:21](../../src/search/array/ArrayReasoner.cpp#L21) | 工具字面引用 1 处 |
| `XOLVER_AX_REFINE` | false (unset) | 模型驱动 Row2 refinement，库 OFF、CLI baked ON。 | [src/search/euf/EufSolver.cpp:82](../../src/search/euf/EufSolver.cpp#L82) | CLI baked=1；测试字面引用 4 处 |
| `XOLVER_AX_ROW2_CONST` | false (unset) | 常量索引 read-over-write 合并，库 OFF、CLI baked ON。 | [src/search/array/ArrayReasoner.cpp:19](../../src/search/array/ArrayReasoner.cpp#L19) | CLI baked=1；测试字面引用 5 处 |
| `XOLVER_AX_ROW2_DISEQ` | true | 已知索引不等 Row2 合并，默认 ON，保留 =0 逃生口。 | [src/search/array/ArrayReasoner.cpp:29](../../src/search/array/ArrayReasoner.cpp#L29) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_ROW2_SPLIT` | true | 组合 Row2 分裂引理，两处默认 ON 的逃生口。 | [src/search/coordination/TheoryManager.cpp:365](../../src/search/coordination/TheoryManager.cpp#L365), [src/search/euf/EufSolver_check.cpp:580](../../src/search/euf/EufSolver_check.cpp#L580) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_STORECOMM_EXT` | false (unset) | 常量索引 store-tower extensionality，库 OFF、CLI baked ON。 | [src/search/array/ArrayReasoner.cpp:36](../../src/search/array/ArrayReasoner.cpp#L36) | CLI baked=1；测试字面引用 3 处 |
| `XOLVER_AX_STORE_MODEL` | true | store-aware 模型构造，由 OFF 提升至默认 ON 的遗留开关。 | [src/search/euf/EufSolver.cpp:80](../../src/search/euf/EufSolver.cpp#L80) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_STORE_NOOP` | true | store-store no-op 合并，源码称 default-ON soundness fix，不能删除必要算法。 | [src/search/array/ArrayReasoner.cpp:34](../../src/search/array/ArrayReasoner.cpp#L34) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_CMS_WIDTH_PROBE` | QF_UFNIA/UFNIA 时 true，其余 false | CMS 中额外整数位宽网格求模型，UFNIA 逻辑默认 ON 的禁用口。 | [src/runtime/Solver_impl_checksat.cpp:1575](../../src/runtime/Solver_impl_checksat.cpp#L1575) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_ARRANGE_INTERNAL` | false (unset) | 内部 shared terms 参与 arrangement，UF_CONGRUENCE 也能隐式启用。 | [src/search/coordination/TheoryManager.cpp:1070](../../src/search/coordination/TheoryManager.cpp#L1070), [src/search/coordination/TheoryManager.cpp:1188](../../src/search/coordination/TheoryManager.cpp#L1188) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_ARRAY_BRIDGE_MODEL` | 1 | 整数非零启用 numeric-array 模型桥接，默认 1；实际算法门而非预算。 | [src/runtime/Solver_impl_model.cpp:122](../../src/runtime/Solver_impl_model.cpp#L122), [src/runtime/Solver_impl_model.cpp:190](../../src/runtime/Solver_impl_model.cpp#L190) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_ARRAY_NIA` | 1 | 整数非零启用数组+NIA 路由，默认 1；源码明确 regression escape。 | [src/runtime/Solver_impl_checksat.cpp:622](../../src/runtime/Solver_impl_checksat.cpp#L622), [src/runtime/Solver_impl_checksat.cpp:1030](../../src/runtime/Solver_impl_checksat.cpp#L1030) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_CAREGRAPH` | false (unset) | 额外 care graph 开关；数组组合无条件 OR 启用。 | [src/search/coordination/TheoryManager.cpp:113](../../src/search/coordination/TheoryManager.cpp#L113) | 赋值形引用 1 处 |
| `XOLVER_COMB_DECIDE_FREE_ATOMS` | false | 自由理论原子 SAT 决策引导，默认 OFF。 | [src/search/sat/CadicalTheoryPropagator.cpp:372](../../src/search/sat/CadicalTheoryPropagator.cpp#L372) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_DEMAND_ARRANGE` | true | 按需 equality arrangement，默认 ON 的禁用口。 | [src/search/coordination/TheoryManager.cpp:1180](../../src/search/coordination/TheoryManager.cpp#L1180) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_EQ_DISEQ_PHASE` | true | 共享等式原子的默认 disequality phase，ExactZero 旧逃生口。 | [src/search/coordination/TheoryManager.cpp:78](../../src/search/coordination/TheoryManager.cpp#L78) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_MODEL_BASED` | true | model-based arrangement，默认 ON，源码明确 =0 escape。 | [src/search/coordination/TheoryManager.cpp:149](../../src/search/coordination/TheoryManager.cpp#L149) | CLI baked=1；测试字面引用 4 处；赋值形引用 1 处 |
| `XOLVER_COMB_SAT_FLOOR` | false (unset) | 实际作用是 ufArgBridgeEnabledLegacy，启用 UF 参数桥接，名称不是纯 SAT 校验。 | [src/search/combination/Purifier.cpp:19](../../src/search/combination/Purifier.cpp#L19) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_SCALAR_BACKFILL` | false (unset) | UF 标量模型值补全，库 OFF、CLI baked ON。 | [src/search/coordination/TheoryManager.cpp:1681](../../src/search/coordination/TheoryManager.cpp#L1681) | CLI baked=1；测试字面引用 1 处 |
| `XOLVER_COMB_UFARG_ARITH_APART` | true | 算术互异证据剪枝 UF arrangement，默认 ON。 | [src/search/coordination/TheoryManager.cpp:1263](../../src/search/coordination/TheoryManager.cpp#L1263) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_UF_CONGRUENCE` | false (unset) | 源码明确 server-bake-pending/default-OFF，并限制数组、非线性、DT。 | [src/runtime/factory/TheoryFactory.cpp:302](../../src/runtime/factory/TheoryFactory.cpp#L302), [src/search/coordination/TheoryManager.cpp:1046](../../src/search/coordination/TheoryManager.cpp#L1046) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_INCREMENTAL_PROP` | false (unset) | 增量 EUF 蕴含扫描，默认 OFF，VERIFY 也强制启用。 | [src/search/euf/EufSolver.cpp:57](../../src/search/euf/EufSolver.cpp#L57) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_MINLEVEL_HEAP` | false (unset) | mergeQueue level 分桶替代扫描，源码明确默认 OFF 实验实现。 | [src/search/euf/EufSolver.cpp:55](../../src/search/euf/EufSolver.cpp#L55) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_PROP` | true | EUF 传播默认 ON 的 ExactZero 逃生口。 | [src/search/euf/EufSolver.cpp:46](../../src/search/euf/EufSolver.cpp#L46) | 赋值形引用 2 处 |
| `XOLVER_EUF_PROP_COMB` | false | 组合 EUF 传播，库 OFF、CLI baked ON。 | [src/search/coordination/TheoryManager.cpp:336](../../src/search/coordination/TheoryManager.cpp#L336) | CLI baked=1；工具字面引用 1 处 |
| `XOLVER_EUF_PROP_DEDUP` | false (unset) | 跳过当前层已发 EUF 蕴含，Phase A v2/default-OFF。 | [src/search/euf/EufSolver.cpp:61](../../src/search/euf/EufSolver.cpp#L61) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_CUTS` | false | 根部 cuts，库 OFF、CLI 与 portfolio cut 臂启用。 | [src/search/lia/LiaSolver.cpp:33](../../src/search/lia/LiaSolver.cpp#L33) | CLI baked=1；portfolio cuts=1；测试字面引用 4 处；赋值形引用 1 处 |
| `XOLVER_LIA_DIO` | false | Diophantine tighten，默认 OFF 的额外 reasoner。 | [src/search/lia/LiaSolver.cpp:47](../../src/search/lia/LiaSolver.cpp#L47) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_ENTAIL_GEN` | false (unset) | 通用 LIA entailment 查询，默认 OFF。 | [src/search/lia/LiaSolver_entailment.cpp:125](../../src/search/lia/LiaSolver_entailment.cpp#L125) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_GMI_CUTS` | false | GMI cuts，默认 OFF，portfolio cut 臂启用。 | [src/search/lia/LiaSolver.cpp:34](../../src/search/lia/LiaSolver.cpp#L34) | portfolio cuts=1；赋值形引用 1 处 |
| `XOLVER_LIA_INCREMENTAL` | false | 增量 replay 与完整 simplex 重建双路径，源码 default-OFF。 | [src/search/lia/LiaSolver.cpp:45](../../src/search/lia/LiaSolver.cpp#L45) | 赋值形引用 1 处 |
| `XOLVER_LIA_LP_DUALITY` | false (unset) | LP-duality probe 默认 OFF；源码记录数组 push/pop 历史缺陷，先修复再处置。 | [src/search/lia/LiaSolver.cpp:412](../../src/search/lia/LiaSolver.cpp#L412) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_REPAIR` | false | 整数候选修复，库 OFF、CLI baked ON。 | [src/search/lia/LiaSolver.cpp:32](../../src/search/lia/LiaSolver.cpp#L32) | CLI baked=1；测试字面引用 4 处 |
| `XOLVER_LRA_BOUND_AXIOMS` | false | bound axioms 生成，库 OFF、CLI baked ON。 | [src/search/linear/BoundAxiomGenerator.cpp:132](../../src/search/linear/BoundAxiomGenerator.cpp#L132) | CLI baked=1 |
| `XOLVER_LRA_DECIDE` | false | 理论原子优先 SAT 决策，库 OFF、CLI baked ON。 | [src/search/sat/CadicalTheoryPropagator.cpp:329](../../src/search/sat/CadicalTheoryPropagator.cpp#L329) | CLI baked=1；测试字面引用 2 处 |
| `XOLVER_LRA_INCREMENTAL_BETA` | false | 增量 beta 与完整重算双路径，源码 default-OFF。 | [src/search/lra/GeneralSimplex.cpp:59](../../src/search/lra/GeneralSimplex.cpp#L59) | 赋值形引用 1 处 |
| `XOLVER_LRA_PIVOT_HEUR` | false | pivot 启发式双路径，库 OFF、CLI baked ON。 | [src/search/lra/GeneralSimplex.cpp:48](../../src/search/lra/GeneralSimplex.cpp#L48) | CLI baked=1；测试字面引用 3 处 |
| `XOLVER_LRA_PROP` | false | LRA 蕴含传播，库 OFF、CLI baked ON。 | [src/search/lra/LraSolver.cpp:37](../../src/search/lra/LraSolver.cpp#L37) | CLI baked=1 |
| `XOLVER_NIA_BB_ARRAY` | false (unset) | 解除含数组公式的 bit-blast 排除，属于适用范围逃生口，不能直接把 OFF 改 ON。 | [src/search/nia/NiaSolver_bitblast.cpp:51](../../src/search/nia/NiaSolver_bitblast.cpp#L51) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BB_CONGRUENCE` | false (unset) | CaDiCaL congruence opt-out 逃生口，默认抑制以规避大实例 OOM。 | [src/search/bitblast/BitBlastSolver.cpp:185](../../src/search/bitblast/BitBlastSolver.cpp#L185) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BILINEAR_FACTOR` | false | 双线性整数分解 reasoner 默认 OFF。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:301](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L301) | 测试字面引用 3 处 |
| `XOLVER_NIA_CDCAC` | false | 实数 CDCAC 候选转整数并验证，库 OFF、CLI baked ON。 | [src/search/nia/NiaSolver.cpp:280](../../src/search/nia/NiaSolver.cpp#L280) | CLI baked=1 |
| `XOLVER_NIA_DIO` | false | Diophantine/Smith normal form reasoner 默认 OFF。 | [src/search/nia/NiaSolver_engines.cpp:305](../../src/search/nia/NiaSolver_engines.cpp#L305) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_EAGER_BITBLAST` | true | 全公式 eager bit-blast 默认 ON 的逃生口。 | [src/runtime/Solver_impl_checksat.cpp:1087](../../src/runtime/Solver_impl_checksat.cpp#L1087) | CLI baked=1 |
| `XOLVER_NIA_EAGER_LIA` | false (unset) | 允许 LIA 进入 eager bit-blast，默认 OFF，源码记录变量除法旧错答风险。 | [src/runtime/Solver_impl_checksat.cpp:1111](../../src/runtime/Solver_impl_checksat.cpp#L1111) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_DNF_BLOCKS` | false (unset) | Farkas OR 额外 DNF block 枚举默认 OFF。 | [src/search/nia/farkas/FarkasOrDetector.cpp:616](../../src/search/nia/farkas/FarkasOrDetector.cpp#L616) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_OR_UNSAT_EMIT` | false (unset) | exhaustive 空 Farkas 表发 UNSAT 的默认 OFF 逃生口，需核实证据链。 | [src/search/nia/NiaSolver_farkas.cpp:219](../../src/search/nia/NiaSolver_farkas.cpp#L219) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_GROBNER` | false | NIA Groebner 理想推理默认 OFF。 | [src/search/nia/NiaSolver.cpp:269](../../src/search/nia/NiaSolver.cpp#L269) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_IFACE_LIFECYCLE` | true | 组合共享接口 lifecycle 默认 ON，源码明确 A/B escape。 | [src/search/nia/NiaSolver.cpp:334](../../src/search/nia/NiaSolver.cpp#L334) | CLI baked=1 |
| `XOLVER_NIA_IFACE_PROP` | false | 线性内核接口蕴含默认 OFF。 | [src/search/nia/NiaSolver_linear.cpp:161](../../src/search/nia/NiaSolver_linear.cpp#L161) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_INT_BOUND_PROP` | false | 整数 interval contraction 默认 OFF。 | [src/search/nia/NiaSolver.cpp:160](../../src/search/nia/NiaSolver.cpp#L160) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LINEAR_DOWNGRADE` | true | 线性 NIA→LIA 默认 ON 的禁用口。 | [src/runtime/Solver_impl_checksat.cpp:947](../../src/runtime/Solver_impl_checksat.cpp#L947) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LOCALSEARCH` | false | enhanced_ 局部搜索分支；不是全部 LS，库 OFF、CLI baked ON。 | [src/search/nia/search/NiaLocalSearch.cpp:50](../../src/search/nia/search/NiaLocalSearch.cpp#L50) | CLI baked=1；赋值形引用 1 处；`setEnhanced` 声明/调用 35 处 |
| `XOLVER_NIA_LS_ADAPTIVE_PLATEAU` | false | plateau 自适应默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:123](../../src/search/nia/search/NiaLocalSearch.cpp#L123) | `setAdaptivePlateau` 声明/调用 1 处 |
| `XOLVER_NIA_LS_ATOM_LOCAL_ACCEPT` | false | 原子局部接受准则默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:98](../../src/search/nia/search/NiaLocalSearch.cpp#L98) | `setAtomLocalAccept` 声明/调用 1 处 |
| `XOLVER_NIA_LS_BILINEAR_PAIR` | false | 双线性变量对联合移动默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:71](../../src/search/nia/search/NiaLocalSearch.cpp#L71) | `setBilinearPair` 声明/调用 1 处 |
| `XOLVER_NIA_LS_BILINEAR_SUBST` | false | 双线性代换移动默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:74](../../src/search/nia/search/NiaLocalSearch.cpp#L74) | `setBilinearSubst` 声明/调用 3 处 |
| `XOLVER_NIA_LS_BRANCH_HINT` | false | LS varActivity 分支引导默认 OFF。 | [src/search/nia/NiaSolver_branch.cpp:133](../../src/search/nia/NiaSolver_branch.cpp#L133) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_DIVERSE_INIT` | false | 多种初始赋值默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:68](../../src/search/nia/search/NiaLocalSearch.cpp#L68) | `setDiverseInit` 声明/调用 1 处 |
| `XOLVER_NIA_LS_DIVERSIFY` | false | diversification 默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:83](../../src/search/nia/search/NiaLocalSearch.cpp#L83) | `setDiversify` 声明/调用 1 处 |
| `XOLVER_NIA_LS_FARKAS_INIT` | false | Farkas 结构初始化默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:126](../../src/search/nia/search/NiaLocalSearch.cpp#L126) | `setFarkasInit` 声明/调用 1 处 |
| `XOLVER_NIA_LS_FS_JUMP` | false | 可行性跳跃默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:65](../../src/search/nia/search/NiaLocalSearch.cpp#L65) | `setFsJump` 声明/调用 5 处 |
| `XOLVER_NIA_LS_MODULAR_ESCALATE` | false | 模数搜索升级默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:80](../../src/search/nia/search/NiaLocalSearch.cpp#L80) | `setModularEscalate` 声明/调用 1 处 |
| `XOLVER_NIA_LS_MULTI_SCALE` | false | 多尺度步长默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:59](../../src/search/nia/search/NiaLocalSearch.cpp#L59) | `setMultiScale` 声明/调用 5 处 |
| `XOLVER_NIA_LS_PIN_EQ` | false | 等式 pinning 默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:77](../../src/search/nia/search/NiaLocalSearch.cpp#L77) | `setPinEq` 声明/调用 4 处 |
| `XOLVER_NIA_LS_QUAD_CRITICAL` | false | 二次函数临界点候选默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:62](../../src/search/nia/search/NiaLocalSearch.cpp#L62) | `setQuadCritical` 声明/调用 5 处 |
| `XOLVER_NIA_LS_RW_HUB` | false | read/write hub 增强默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:117](../../src/search/nia/search/NiaLocalSearch.cpp#L117) | `setRwHub` 声明/调用 1 处 |
| `XOLVER_NIA_LS_RW_LADDER` | false | read/write ladder 增强默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:120](../../src/search/nia/search/NiaLocalSearch.cpp#L120) | `setRwLadder` 声明/调用 1 处 |
| `XOLVER_NIA_LS_SMART_INIT` | false | SmartInit 默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:86](../../src/search/nia/search/NiaLocalSearch.cpp#L86) | `setSmartInit` 声明/调用 1 处 |
| `XOLVER_NIA_LS_SMART_MOVE` | false | SmartMove 默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:89](../../src/search/nia/search/NiaLocalSearch.cpp#L89) | `setSmartMove` 声明/调用 1 处 |
| `XOLVER_NIA_LS_TABU` | false | tabu 搜索默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:92](../../src/search/nia/search/NiaLocalSearch.cpp#L92) | `setTabu` 声明/调用 1 处 |
| `XOLVER_NIA_LS_TWO_LEVEL` | false | two-level 搜索默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:53](../../src/search/nia/search/NiaLocalSearch.cpp#L53) | `setTwoLevel` 声明/调用 34 处 |
| `XOLVER_NIA_LS_VIOLATION_CORE` | false | 违反约束核心引导默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:95](../../src/search/nia/search/NiaLocalSearch.cpp#L95) | `setViolationCore` 声明/调用 1 处 |
| `XOLVER_NIA_LS_WARM_START` | false | 历史候选 warm start 默认 OFF 分支。 | [src/search/nia/search/NiaLocalSearch.cpp:56](../../src/search/nia/search/NiaLocalSearch.cpp#L56) | `setWarmStart` 声明/调用 5 处 |
| `XOLVER_NIA_MODULAR_WARM_START` | false | 模数推理 warm start 默认 OFF 路径。 | [src/search/nia/NiaSolver_refute.cpp:430](../../src/search/nia/NiaSolver_refute.cpp#L430) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_NATIVE_MODEQCONST` | false | lowerer/reasoner 共用的 native mod equality 默认 OFF 路径。 | [src/frontend/preprocess/IntDivModLowerer.cpp:406](../../src/frontend/preprocess/IntDivModLowerer.cpp#L406), [src/search/nia/NiaSolver_refute.cpp:471](../../src/search/nia/NiaSolver_refute.cpp#L471) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_NLA_CUTS` | false | NIA cuts 库 OFF、CLI baked ON，共用 NRA 生成器。 | [src/search/nia/NiaSolver_refute.cpp:568](../../src/search/nia/NiaSolver_refute.cpp#L568), [src/search/nra/reasoners/NlaCutsRunner.cpp:20](../../src/search/nra/reasoners/NlaCutsRunner.cpp#L20) | CLI baked=1 |
| `XOLVER_NIA_NO_DISEQ` | false | Nelson–Oppen 共享不等式提前传递默认 OFF；不是禁止 disequality。 | [src/search/coordination/TheoryManager.cpp:732](../../src/search/coordination/TheoryManager.cpp#L732) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_NO_PROP` | false | 共享等式走 Standard entailment 通道默认 OFF。 | [src/search/coordination/TheoryManager.cpp:892](../../src/search/coordination/TheoryManager.cpp#L892) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_OMEGA` | false | Omega reasoner 默认 OFF。 | [src/search/nia/NiaSolver.cpp:150](../../src/search/nia/NiaSolver.cpp#L150) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_PER_BRANCH_BB` | false (unset) | 解除纯 NIA 每分支 bit-blast 禁用的逃生口，组合 NIA 不受此门控制。 | [src/search/nia/NiaSolver_bitblast.cpp:109](../../src/search/nia/NiaSolver_bitblast.cpp#L109) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_ROW2_DEMAND` | false | 按 Row2 索引需求传播，两处默认 OFF。 | [src/search/coordination/TheoryManager.cpp:787](../../src/search/coordination/TheoryManager.cpp#L787), [src/search/euf/EufSolver_check.cpp:155](../../src/search/euf/EufSolver_check.cpp#L155) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_SECANT` | false | 平方 secant 引理默认 OFF。 | [src/search/nia/NiaSolver_engines.cpp:546](../../src/search/nia/NiaSolver_engines.cpp#L546) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_SHARED_ARITH_VALUE` | 1 | 整数非零允许共享算术模型值查询，默认 1，实际算法门。 | [src/search/nia/NiaSolver_combination.cpp:122](../../src/search/nia/NiaSolver_combination.cpp#L122) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_SMALL_PRIME_MODULAR` | false | 小素数 congruence refutation 默认 OFF。 | [src/search/nia/NiaSolver.cpp:155](../../src/search/nia/NiaSolver.cpp#L155) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_ZOHAR_PLUGIN` | false | pow2 UF 公理插件默认 OFF，启用还会关闭 CMS prepass，需核实语义。 | [src/runtime/Solver_impl_checksat.cpp:595](../../src/runtime/Solver_impl_checksat.cpp#L595), [src/runtime/Solver_impl_checksat.cpp:1544](../../src/runtime/Solver_impl_checksat.cpp#L1544) | 测试字面引用 5 处 |
| `XOLVER_NO_BAKED_DEFAULTS` | false | CLI 默认配置整组回退口，源码称用于 pre-bake differential。 | [app/main.cpp:718](../../app/main.cpp#L718) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NO_EXPAND_FUNCTIONS` | false (unset) | 解析器 expand_functions 反值开关，需与上游 IR 契约一起整理。 | [src/runtime/Solver_impl_solve.cpp:57](../../src/runtime/Solver_impl_solve.cpp#L57) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_COMBINATION` | false | 在组合逻辑中运行 CAC 的默认 OFF 路径，改变 equality propagation 分工。 | [src/search/nra/NraSolver.cpp:529](../../src/search/nra/NraSolver.cpp#L529), [src/search/nra/NraSolver_cac.cpp:69](../../src/search/nra/NraSolver_cac.cpp#L69) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_COMB_SAT` | false | 组合 CAC 接受模型的默认 OFF 路径，须保留完整验证。 | [src/search/nra/NraSolver.cpp:517](../../src/search/nra/NraSolver.cpp#L517), [src/search/nra/NraSolver_cac.cpp:374](../../src/search/nra/NraSolver_cac.cpp#L374) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_EARLY_INFEAS` | false | 提前不可行检测默认 OFF。 | [src/search/nra/NraSolver_cac.cpp:295](../../src/search/nra/NraSolver_cac.cpp#L295) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_INT` | false | NIA MCSAT/CDCAC 中 integer-aware CAC 两处默认 OFF。 | [src/search/nia/mcsat/NiaMcsatEngine.cpp:378](../../src/search/nia/mcsat/NiaMcsatEngine.cpp#L378), [src/search/nra/core/CdcacCore.cpp:2208](../../src/search/nra/core/CdcacCore.cpp#L2208) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_INT_COVER` | false | integer-aware covering 默认 OFF。 | [src/search/nra/core/CdcacCore.cpp:1444](../../src/search/nra/core/CdcacCore.cpp#L1444) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_LAZARD_DEDUP` | false | Lazard 投影因子去重默认 OFF 双实现。 | [src/search/nra/lazard/LazardProjectionOperator.cpp:141](../../src/search/nra/lazard/LazardProjectionOperator.cpp#L141) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_MIN_CONFLICT` | true | UNSAT core 最小化默认 ON 的禁用口。 | [src/search/nra/NraSolver_cac.cpp:352](../../src/search/nra/NraSolver_cac.cpp#L352) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_NLSAT` | false | CAC 内 lazy conflict-driven NLSAT 默认 OFF，并强制 SAT_FIRST。 | [src/search/nra/core/CdcacCore.cpp:264](../../src/search/nra/core/CdcacCore.cpp#L264) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_NO_COLLINS` | false | 禁用 Collins 回退，与 CAC_ONLY 重复控制同一分支。 | [src/search/nra/NraSolver_cac.cpp:289](../../src/search/nra/NraSolver_cac.cpp#L289), [src/search/nra/NraSolver_cac.cpp:558](../../src/search/nra/NraSolver_cac.cpp#L558) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_ONLY` | false | 与 CAC_NO_COLLINS 重复表达同一求解路径选择。 | [src/search/nra/NraSolver_cac.cpp:289](../../src/search/nra/NraSolver_cac.cpp#L289), [src/search/nra/NraSolver_cac.cpp:558](../../src/search/nra/NraSolver_cac.cpp#L558) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_PRUNE_INTERVALS` | false | interval pruning 默认 OFF。 | [src/search/nra/NraSolver_cac.cpp:298](../../src/search/nra/NraSolver_cac.cpp#L298) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_RATIONAL_FALLBACK` | false | 有理数候选恢复默认 OFF。 | [src/search/nra/NraSolver_cac.cpp:446](../../src/search/nra/NraSolver_cac.cpp#L446) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_ALGEBRAIC` | false | 接受经过检查的 algebraic CAC 模型默认 OFF。 | [src/search/nra/NraSolver_cac.cpp:387](../../src/search/nra/NraSolver_cac.cpp#L387) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST` | false（NLSAT/LOOKAHEAD 可强制 true） | rational sample-first 默认 OFF，NLSAT/LOOKAHEAD 可间接开启。 | [src/search/nra/core/CdcacCore.cpp:254](../../src/search/nra/core/CdcacCore.cpp#L254) | 测试字面引用 6 处 |
| `XOLVER_NRA_CAC_SAT_FIRST_ALG` | true | algebraic sample-first 实际默认 ON 的 kill switch；旧注释还有 OFF，以成员初始化为准。 | [src/search/nra/core/CdcacCore.cpp:270](../../src/search/nra/core/CdcacCore.cpp#L270) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_LOOKAHEAD` | false | forward infeasibility lookahead 默认 OFF，并强制 SAT_FIRST。 | [src/search/nra/core/CdcacCore.cpp:275](../../src/search/nra/core/CdcacCore.cpp#L275) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_SAMPLE` | false | 候选值 sweep 求 SAT；不是诊断采样，默认 OFF 算法路径。 | [src/search/nra/cac/CacEngine.cpp:222](../../src/search/nra/cac/CacEngine.cpp#L222) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_VAR_ORDER` | false | CAC 变量排序启发式默认 OFF 双路径。 | [src/search/nra/NraSolver_cac.cpp:248](../../src/search/nra/NraSolver_cac.cpp#L248) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_EQ_CASCADE` | true | 结构等式 cascade 候选模型默认 ON 的禁用口。 | [src/search/nra/NraSolver_stages.cpp:1026](../../src/search/nra/NraSolver_stages.cpp#L1026) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_GROBNER` | false | NRA Groebner 默认 OFF。 | [src/search/nra/NraSolver.cpp:50](../../src/search/nra/NraSolver.cpp#L50) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_ICP` | false | interval propagation 默认 OFF 阶段。 | [src/search/nra/NraSolver_stages.cpp:150](../../src/search/nra/NraSolver_stages.cpp#L150) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_INT_PROBE` | false | 整数结构候选探测默认 OFF。 | [src/search/nra/NraSolver_stages.cpp:907](../../src/search/nra/NraSolver_stages.cpp#L907) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LAZARD_LIFT` | false（Projection=Lazard 会重配） | Lazard lifting 库 OFF、CLI baked ON；显式投影策略也能改变模式。 | [src/search/nra/core/CdcacCore.cpp:218](../../src/search/nra/core/CdcacCore.cpp#L218) | CLI baked=1 |
| `XOLVER_NRA_LIBPOLY_PSC` | false | libpoly subresultant 后端默认 OFF 双实现，CLI baked ON。 | [src/search/nra/lazard/SubresultantChain.cpp:20](../../src/search/nra/lazard/SubresultantChain.cpp#L20) | CLI baked=1；测试字面引用 2 处 |
| `XOLVER_NRA_LINEARIZE` | false | incremental linearization 默认 OFF。 | [src/search/nra/NraSolver_cac.cpp:590](../../src/search/nra/NraSolver_cac.cpp#L590) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LINEAR_DOWNGRADE` | true | 线性 NRA→LRA 默认 ON 的逃生口。 | [src/runtime/Solver_impl_checksat.cpp:920](../../src/runtime/Solver_impl_checksat.cpp#L920) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LS_EQ_RELAX` | false | LS 等式放松候选路径默认 OFF。 | [src/search/nra/NraSolver.cpp:364](../../src/search/nra/NraSolver.cpp#L364) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_MCCORMICK_PARTIAL` | false | 缺少完整有限边界时生成部分 McCormick 引理，默认 OFF，须核对理由完整性。 | [src/search/linearizer/McCormickGenerator.cpp:66](../../src/search/linearizer/McCormickGenerator.cpp#L66) | 测试字面引用 7 处 |
| `XOLVER_NRA_MCSAT_NO_CDCAC` | false | 为诊断高次实例禁用 CDCAC 回退的逃生口。 | [src/search/nra/engine/NlsatEngine.cpp:544](../../src/search/nra/engine/NlsatEngine.cpp#L544) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLA_CUTS` | false | NRA cuts 库 OFF、CLI baked ON。 | [src/search/nra/NraSolver_cac.cpp:144](../../src/search/nra/NraSolver_cac.cpp#L144), [src/search/nra/reasoners/NlaCutsRunner.cpp:19](../../src/search/nra/reasoners/NlaCutsRunner.cpp#L19) | CLI baked=1；工具字面引用 1 处 |
| `XOLVER_NRA_NLEXT_BERNSTEIN` | false | Bernstein 扩展引理默认 OFF。 | [src/search/linearizer/IncrementalLinearizer.cpp:244](../../src/search/linearizer/IncrementalLinearizer.cpp#L244) | 工具字面引用 1 处 |
| `XOLVER_NRA_NLEXT_HIGHER` | false | 高阶非线性扩展引理默认 OFF。 | [src/search/linearizer/IncrementalLinearizer.cpp:391](../../src/search/linearizer/IncrementalLinearizer.cpp#L391) | 工具字面引用 1 处 |
| `XOLVER_NRA_NLEXT_MONO_BOUND` | false | 单项式界引理默认 OFF。 | [src/search/linearizer/IncrementalLinearizer.cpp:324](../../src/search/linearizer/IncrementalLinearizer.cpp#L324) | 工具字面引用 1 处 |
| `XOLVER_NRA_NLEXT_POWER` | false | power 扩展引理默认 OFF。 | [src/search/linearizer/IncrementalLinearizer.cpp:241](../../src/search/linearizer/IncrementalLinearizer.cpp#L241) | 工具字面引用 1 处 |
| `XOLVER_NRA_NLEXT_TANGENT_PERTURB` | false | 切线扰动默认 OFF；次数 cap/启动轮次另列。 | [src/search/nra/NraSolver_cac.cpp:707](../../src/search/nra/NraSolver_cac.cpp#L707) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_ROOT_CANDIDATES` | 0 | 整数非零启用精确根候选收集，默认 0，实际算法门。 | [src/search/nra/engine/NlsatEngine.cpp:785](../../src/search/nra/engine/NlsatEngine.cpp#L785) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_OSF_PRUNE` | false | PolynomialIntervalPruner 默认 OFF 阶段。 | [src/search/nra/NraSolver_stages.cpp:506](../../src/search/nra/NraSolver_stages.cpp#L506) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PREELIM` | false | 线性 pre-elimination 默认 OFF。 | [src/search/nra/NraSolver.cpp:198](../../src/search/nra/NraSolver.cpp#L198) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_SIGN_SPLIT` | false | 符号区间分裂引理默认 OFF。 | [src/search/nra/NraSolver_stages.cpp:392](../../src/search/nra/NraSolver_stages.cpp#L392) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_SQUARE_CASCADE` | true | 平方结构候选模型默认 ON 的禁用口。 | [src/search/nra/NraSolver_stages.cpp:1056](../../src/search/nra/NraSolver_stages.cpp#L1056) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_VARORDER_ASC` | false (unset) | 恢复旧 ascending 排序的 differential 逃生口，源码明确。 | [src/search/nra/core/CdcacSolver.cpp:173](../../src/search/nra/core/CdcacSolver.cpp#L173) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_VARORDER_SIMPLEX` | false | simplex-guided 排序的可选替代路径。 | [src/search/nra/core/CdcacSolver.cpp:20](../../src/search/nra/core/CdcacSolver.cpp#L20) | 测试字面引用 3 处 |
| `XOLVER_PP_AND_FLATTEN` | false (unset) | base-scope AND flatten 默认 OFF。 | [src/runtime/Solver_impl_checksat.cpp:194](../../src/runtime/Solver_impl_checksat.cpp#L194) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_AUTO_EUF_PROMOTE` | false (unset) | 按实际特征升级 UF 逻辑默认 OFF。 | [src/runtime/Solver_impl_checksat.cpp:671](../../src/runtime/Solver_impl_checksat.cpp#L671) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_BOUNDED_ENUM` | false (unset) | 根部有界枚举预处理默认 OFF，枚举预算另列。 | [src/runtime/Solver_impl_checksat.cpp:222](../../src/runtime/Solver_impl_checksat.cpp#L222) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_INLINE_SINGLE_DEFS_INT` | false (unset) | 额外内联单定义整数默认 OFF。 | [src/frontend/preprocess/DefinedVariableSubstitution.cpp:76](../../src/frontend/preprocess/DefinedVariableSubstitution.cpp#L76) | 测试字面引用 1 处 |
| `XOLVER_PP_MONOMIAL_SHARE` | false (unset) | NIA base-scope 单项式共享默认 OFF。 | [src/runtime/Solver_impl_checksat.cpp:275](../../src/runtime/Solver_impl_checksat.cpp#L275) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_NEWTON_INT_SQRT` | false (unset) | Newton 整数平方根预处理默认 OFF。 | [src/runtime/Solver_impl_checksat.cpp:226](../../src/runtime/Solver_impl_checksat.cpp#L226) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_PG_CNF` | false (unset) | PG CNF 路径，库 OFF、CLI baked ON。 | [src/runtime/Solver_impl_checksat.cpp:1322](../../src/runtime/Solver_impl_checksat.cpp#L1322) | CLI baked=1 |
| `XOLVER_PP_PURE_DEFINED_VAR_SUBST` | false (unset) | 定义变量替换默认 OFF，另有限定 algebraic-model 逻辑。 | [src/runtime/Solver_impl_checksat.cpp:392](../../src/runtime/Solver_impl_checksat.cpp#L392) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_REWRITE` | false (unset) | FormulaRewriter 开关，STRAT_PRESETS 可间接开启，CLI baked ON。 | [src/runtime/Solver_impl_checksat.cpp:233](../../src/runtime/Solver_impl_checksat.cpp#L233) | CLI baked=1；测试字面引用 3 处 |
| `XOLVER_PP_ROW_FOLD` | 0 | 整数非零执行 ArrayReadOverWrite，默认 0，实际算法门。 | [src/runtime/Solver_impl_checksat.cpp:525](../../src/runtime/Solver_impl_checksat.cpp#L525) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_SOLVE_EQS` | 库：QF_LIA/LIA/QF_NIA/NIA/QF_LRA/LRA 默认 true；其余 false，另限 base scope 且非 algebraic-model logic | 按逻辑自动决定外仍有覆盖口，CLI baked 1，存在多层默认设置。 | [src/runtime/Solver_impl_checksat.cpp:326](../../src/runtime/Solver_impl_checksat.cpp#L326) | CLI baked=1；测试字面引用 1 处；赋值形引用 1 处 |
| `XOLVER_PP_SOLVE_EQS_GAUSS` | false (unset) | 通用线性 Gaussian elimination 默认 OFF。 | [src/runtime/Solver_impl_checksat.cpp:346](../../src/runtime/Solver_impl_checksat.cpp#L346) | 赋值形引用 1 处 |
| `XOLVER_PP_STORE_TOWER_MULTISET` | 0 | 整数非零执行 StoreTowerEqMultiset，默认 0，实际算法门。 | [src/runtime/Solver_impl_checksat.cpp:449](../../src/runtime/Solver_impl_checksat.cpp#L449) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_TIGHT_BOUND_SUBST` | false (unset) | 紧上下界变量代换默认 OFF。 | [src/frontend/preprocess/FormulaRewriter.cpp:282](../../src/frontend/preprocess/FormulaRewriter.cpp#L282) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_UNCONSTRAINED_ELIM` | false (unset) | 未约束项消除 fixpoint，源码 default-OFF。 | [src/runtime/Solver_impl_checksat.cpp:373](../../src/runtime/Solver_impl_checksat.cpp#L373) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_UNIVARIATE_CYCLE_SOLVE` | false (unset) | 定义变量中的一元循环求解默认 OFF。 | [src/frontend/preprocess/DefinedVariableSubstitution.cpp:165](../../src/frontend/preprocess/DefinedVariableSubstitution.cpp#L165) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_VALIDATOR_MEMO` | true | 模型验证缓存默认 ON 的旧禁用口，先验证 key/context 充分性。 | [src/runtime/Solver_impl_model.cpp:523](../../src/runtime/Solver_impl_model.cpp#L523) | CLI baked=1 |
| `XOLVER_RELEVANCY` | false (unset) | 相关性图和值 oracle，源码 default-OFF 待广泛验证。 | [src/runtime/Solver_impl_checksat.cpp:1486](../../src/runtime/Solver_impl_checksat.cpp#L1486) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_DEFER_EARLY_CONFLICT` | false (unset) | 推迟早期 theory conflict 的默认 OFF 双路径。 | [src/search/sat/CadicalTheoryPropagator.cpp:113](../../src/search/sat/CadicalTheoryPropagator.cpp#L113) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_MIN` | false (unset) | theory lemma 最小化，库 OFF、CLI baked ON。 | [src/search/coordination/TheoryManager.cpp:129](../../src/search/coordination/TheoryManager.cpp#L129) | CLI baked=1 |
| `XOLVER_SIMPLEX_IMPLIED_EQ` | false | LIA/LRA 相等式发现，两处 default-OFF。 | [src/search/lia/LiaSolver.cpp:46](../../src/search/lia/LiaSolver.cpp#L46), [src/search/lra/LraSolver.cpp:39](../../src/search/lra/LraSolver.cpp#L39) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_STRAT_PRESETS` | false (unset) | rewrite 和 theory setup 的另一层默认配置，CLI baked ON。 | [src/runtime/Solver_impl_checksat.cpp:234](../../src/runtime/Solver_impl_checksat.cpp#L234), [src/runtime/Solver_impl_checksat.cpp:1212](../../src/runtime/Solver_impl_checksat.cpp#L1212) | CLI baked=1；测试字面引用 2 处 |
| `XOLVER_TARGETED_PP` | 0 | 整数非零启用目标数组预处理，库 0、CLI baked 1，实际算法门。 | [src/runtime/Solver_impl_checksat.cpp:245](../../src/runtime/Solver_impl_checksat.cpp#L245), [src/runtime/Solver_impl_checksat.cpp:544](../../src/runtime/Solver_impl_checksat.cpp#L544) | CLI baked=1 |
| `XOLVER_TARGETED_PP_UFACK` | false (unset) | UF Ackermann 预处理，库 OFF、CLI baked ON。 | [src/runtime/Solver_impl_checksat.cpp:561](../../src/runtime/Solver_impl_checksat.cpp#L561) | CLI baked=1 |
| `XOLVER_TARGETED_PP_WRITEARRAY` | false (unset) | ReadOnlyArrayElim 扩展到 write array 默认 OFF。 | [src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp:286](../../src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp#L286) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_UF_DISEQ_WATCH` | true | EUF 不等式 watch 默认 ON 的 ExactZero 逃生口。 | [src/search/euf/EufSolver.cpp:45](../../src/search/euf/EufSolver.cpp#L45) | 测试字面引用 2 处 |
| `XOLVER_UF_FAST_CC` | true | 快速 congruence closure 默认 ON，源码明确 A/B escape。 | [src/search/euf/IncrementalEGraph.cpp:14](../../src/search/euf/IncrementalEGraph.cpp#L14) | CLI baked=1；测试字面引用 1 处 |

### 需进一步审查（16）

| 控制 | 缺省 | 语义与处置依据 | 读取位置 | 启用/配置证据 |
|---|---|---|---|---|
| `XOLVER_ARRAY_COMB_VALIDATE_SAT` | false (unset) | 额外数组组合模型验证 floor；影响 sat/unknown，需先统一 soundness 合约。 | [src/runtime/Solver_impl_checksat.cpp:2090](../../src/runtime/Solver_impl_checksat.cpp#L2090) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_PUBLISH_ON_LEMMA` | combinationMode_ | 按 combinationMode_ 默认选择 lemma 前共享等式发布；需追踪 pendingLemma 协议。 | [src/search/coordination/TheoryManager.cpp:619](../../src/search/coordination/TheoryManager.cpp#L619) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_UFARG_ARRANGE` | false / true | 同一 Boolean key 在 Purifier 默认 false、TheoryManager 默认 true；先统一消费者合约。 | [src/search/combination/Purifier.cpp:20](../../src/search/combination/Purifier.cpp#L20), [src/search/coordination/TheoryManager.cpp:1249](../../src/search/coordination/TheoryManager.cpp#L1249) | CLI baked=1；测试字面引用 1 处 |
| `XOLVER_COMB_VALIDATE_SAT` | false | 组合模型验证 floor，需与无条件模型验证覆盖一起审查。 | [src/runtime/Solver_impl_checksat.cpp:1978](../../src/runtime/Solver_impl_checksat.cpp#L1978) | 赋值形引用 1 处 |
| `XOLVER_DT_SELECTOR_SEMANTIC_BRIDGE` | true | 默认 true 的 selector 算术模型桥接，需确认禁用对模型语义的影响。 | [src/runtime/Solver_impl_model.cpp:446](../../src/runtime/Solver_impl_model.cpp#L446) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DT_VALIDATOR_STRICT` | false (unset) | DtModelValidator 严格模式影响 indeterminate 的处理，属正确性契约。 | [src/search/euf/EufSolver_check.cpp:704](../../src/search/euf/EufSolver_check.cpp#L704) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_ESCALATING_BOUNDED_SAT` | 0 | 轮数同时启用 bounded SAT 求解入口，兼具模式选择和预算语义。 | [src/runtime/Solver.cpp:1169](../../src/runtime/Solver.cpp#L1169) | 测试字面引用 6 处 |
| `XOLVER_EUF_INCREMENTAL_PROP_VERIFY` | false (unset) | 既启用不变量核验又强制 incrementalProp=true；不是纯诊断。 | [src/search/euf/EufSolver.cpp:58](../../src/search/euf/EufSolver.cpp#L58) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_UF_MODEL` | EufSolver true；TheoryManager false | EufSolver 默认 true、TheoryManager 默认 false；涉及真实 UF 模型构造。 | [src/search/coordination/TheoryManager.cpp:1515](../../src/search/coordination/TheoryManager.cpp#L1515), [src/search/euf/EufSolver.cpp:52](../../src/search/euf/EufSolver.cpp#L52) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LINEAR_PROP` | false / 0 | TheoryManager 用 Flag，NiaSolver 用 Int；非法 token 语义不同。 | [src/search/coordination/TheoryManager.cpp:322](../../src/search/coordination/TheoryManager.cpp#L322), [src/search/nia/NiaSolver.cpp:138](../../src/search/nia/NiaSolver.cpp#L138) | 工具字面引用 1 处 |
| `XOLVER_NIA_MCSAT` | false | 选择另一个 theory engine；需决定长期公开 engine 策略还是实验入口。 | [src/runtime/factory/TheoryFactory.cpp:105](../../src/runtime/factory/TheoryFactory.cpp#L105) | 测试字面引用 5 处 |
| `XOLVER_NRA_CAC_VAR_ORDER_DESC` | false | 在 VAR_ORDER 前提下选择升/降序，可能应合并为正常枚举策略。 | [src/search/nra/NraSolver_cac.cpp:268](../../src/search/nra/NraSolver_cac.cpp#L268) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LAZARD_CELL_CERT` | true | 默认 true 的 cell certificate 路径影响可信 UNSAT 接受；先审证书合约。 | [src/search/nra/core/CdcacCore.cpp:251](../../src/search/nra/core/CdcacCore.cpp#L251) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_MCSAT` | false | 选择另一个 theory engine；需决定长期公开 engine 策略还是实验入口。 | [src/runtime/factory/TheoryFactory.cpp:69](../../src/runtime/factory/TheoryFactory.cpp#L69) | 测试字面引用 5 处 |
| `XOLVER_PP_STRICT_VALIDATION` | false (unset) | 额外全公式 SAT 严格验证；先统一结果/证据契约。 | [src/runtime/Solver_impl_checksat.cpp:2093](../../src/runtime/Solver_impl_checksat.cpp#L2093) | 测试字面引用 2 处 |
| `XOLVER_PP_VALIDATE_NONLINEAR_SAT` | false (unset) | 额外非线性模型验证，需与已有强制 floor 合并审查。 | [src/runtime/Solver_impl_checksat.cpp:2095](../../src/runtime/Solver_impl_checksat.cpp#L2095) | 限定范围未见字面引用；不排除直接 API/外部 |

### 资源预算和上限（85）

| 控制 | 缺省 | 语义与处置依据 | 读取位置 | 启用/配置证据 |
|---|---|---|---|---|
| `XOLVER_AX_COMPLETE_BUDGET` | 0（累计 selects 无上限；正值覆盖） | 数组 completion 累计生成 select 的数量上限。 | [src/search/array/ArrayReasoner.cpp:56](../../src/search/array/ArrayReasoner.cpp#L56) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_ESCALATING_BOUNDED_SAT_BUDGET_MS` | 15000 | escalating bounded SAT 的时间分配，单位 ms。 | [src/runtime/Solver.cpp:1175](../../src/runtime/Solver.cpp#L1175) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_PROP_BUDGET` | 512 | 每次 EUF 蕴含扫描/输出的工作数量上限。 | [src/search/euf/EufSolver_diagnostics.cpp:84](../../src/search/euf/EufSolver_diagnostics.cpp#L84) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_CUT_MAXBITS` | 8 | LIA cut 可处理的数值位数阈值。 | [src/search/lia/LiaSolver_integrality.cpp:476](../../src/search/lia/LiaSolver_integrality.cpp#L476) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_CUT_MAXPERSOLVE` | 4 | 每次求解生成 LIA cuts 的最大数量。 | [src/search/lia/LiaSolver_integrality.cpp:212](../../src/search/lia/LiaSolver_integrality.cpp#L212) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_MILP_BRANCH_BUDGET` | 100 | 快速 MILP integrality 检查的分支工作预算。 | [src/search/lia/InternalMilpEngine.cpp:139](../../src/search/lia/InternalMilpEngine.cpp#L139) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_PORTFOLIO_ARM0_MS` | 240000 ms | LIA 普通 portfolio 臂时间预算。 | [src/runtime/factory/StrategyPresets.cpp:17](../../src/runtime/factory/StrategyPresets.cpp#L17) | 测试字面引用 3 处 |
| `XOLVER_LIA_PORTFOLIO_CUT_MS` | 60000 ms | LIA cuts portfolio 臂时间预算。 | [src/runtime/factory/StrategyPresets.cpp:18](../../src/runtime/factory/StrategyPresets.cpp#L18) | 测试字面引用 2 处 |
| `XOLVER_LRA_BOUND_AXIOMS_MAXGROUP` | 256 | bound axioms 每组原子数量阈值，用来避免成对生成爆炸。 | [src/search/linear/BoundAxiomGenerator.cpp:138](../../src/search/linear/BoundAxiomGenerator.cpp#L138) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LRA_LP_DUALITY_BUDGET` | 100（0 禁用该查询工作） | LP-duality 查询预算，0 不分配此工作。 | [src/search/lra/LraSolver.cpp:41](../../src/search/lra/LraSolver.cpp#L41) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BILINEAR_FACTOR_MAX_C` | 10000 | 双线性分解处理常数大小的上限。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:306](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L306) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BILINEAR_FACTOR_MAX_DIV` | 64 | 双线性分解枚举约数的数量上限。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:311](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L311) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BITBLAST_CONFLICTS` | 0（不限 conflicts） | CaDiCaL 冲突预算，0 不限。 | [src/search/bitblast/BitBlastSolver.h:44](../../src/search/bitblast/BitBlastSolver.h#L44) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BITBLAST_GATE_BUDGET` | 2000000 | 编码生成的 SAT 变量/gate 资源上限；此 gate 是电路门，不是功能开关。 | [src/search/bitblast/BitBlastSolver.cpp:24](../../src/search/bitblast/BitBlastSolver.cpp#L24) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BITBLAST_MAX_BITWIDTH` | 128 | 任一编码整数的位宽上限，超出返回资源不足结果。 | [src/search/bitblast/BitBlastSolver.h:59](../../src/search/bitblast/BitBlastSolver.h#L59) | 测试字面引用 3 处 |
| `XOLVER_NIA_BITBLAST_MAX_ITERS` | 7 | 位宽编码/SAT 尝试次数上限。 | [src/search/bitblast/BitBlastSolver.h:49](../../src/search/bitblast/BitBlastSolver.h#L49) | 测试字面引用 3 处 |
| `XOLVER_NIA_BOUNDED_ENUM_THRESHOLD` | 10000 | 完整有限域枚举的域乘积/工作量阈值。 | [src/search/nia/NiaSolver_bitblast.cpp:171](../../src/search/nia/NiaSolver_bitblast.cpp#L171), [src/search/nia/reasoners/BoundedNiaSolver.cpp:13](../../src/search/nia/reasoners/BoundedNiaSolver.cpp#L13) | 测试字面引用 1 处 |
| `XOLVER_NIA_EAGER_BITBLAST_BUDGET` | 20000000 | 全公式 eager bit-blast 的编码变量/gate 上限。 | [src/search/bitblast/EagerBitBlastSolver.cpp:300](../../src/search/bitblast/EagerBitBlastSolver.cpp#L300) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_EAGER_BITBLAST_BUDGET_MS` | 120000 | eager bit-blast 时间上限。 | [src/search/bitblast/EagerBitBlastSolver.cpp:339](../../src/search/bitblast/EagerBitBlastSolver.cpp#L339) | 测试字面引用 1 处；赋值形引用 2 处 |
| `XOLVER_NIA_EAGER_BITBLAST_BUDGET_PCT` | 33 | eager bit-blast 可使用总墙钟的百分比。 | [src/search/bitblast/EagerBitBlastSolver.cpp:343](../../src/search/bitblast/EagerBitBlastSolver.cpp#L343) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_EAGER_BITBLAST_CONFLICTS` | 1000000 | eager SAT 每次冲突数预算。 | [src/search/bitblast/EagerBitBlastSolver.cpp:356](../../src/search/bitblast/EagerBitBlastSolver.cpp#L356) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_EAGER_BITBLAST_UNSAT_CAP` | 4 | 小位宽连续 UNSAT 尝试次数上限，不把小盒 UNSAT 当全域 UNSAT。 | [src/search/bitblast/EagerBitBlastSolver.cpp:383](../../src/search/bitblast/EagerBitBlastSolver.cpp#L383) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_COMBO_CAP` | 16384 | Farkas 表候选组合枚举上限。 | [src/search/nia/NiaSolver_farkas.cpp:288](../../src/search/nia/NiaSolver_farkas.cpp#L288) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_DNF_CAP` | 读取 0 保留局部 256 | Farkas OR 分类的 DNF 展开上限。 | [src/search/nia/farkas/FarkasOrDetector.cpp:618](../../src/search/nia/farkas/FarkasOrDetector.cpp#L618) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_EAGER_BUDGET_MS` | 2000 | Farkas eager 阶段时间上限。 | [src/runtime/Solver_impl_checksat.cpp:1145](../../src/runtime/Solver_impl_checksat.cpp#L1145) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_EAGER_PCT` | 33 | Farkas eager 阶段墙钟份额。 | [src/runtime/Solver_impl_checksat.cpp:1144](../../src/runtime/Solver_impl_checksat.cpp#L1144) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_OR_MAX_B` | 8000 | Farkas OR 建表所允许的 bounded 参数规模上限。 | [src/search/nia/NiaSolver_farkas.cpp:95](../../src/search/nia/NiaSolver_farkas.cpp#L95) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_REFUTE_DOM_CAP` | 8192 | Farkas refutation 有界全局变量域乘积上限。 | [src/search/nia/NiaSolver_farkas.cpp:576](../../src/search/nia/NiaSolver_farkas.cpp#L576) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_REFUTE_LEAF_CAP` | 200000 | Farkas refutation 叶枚举上限。 | [src/search/nia/NiaSolver_farkas.cpp:737](../../src/search/nia/NiaSolver_farkas.cpp#L737) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_REFUTE_MAX_LEAF_VARS` | 24 | Farkas 叶输入变量数阈值。 | [src/search/nia/NiaSolver_farkas.cpp:819](../../src/search/nia/NiaSolver_farkas.cpp#L819) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_VALIDATE_BUDGET` | 200 | Farkas 候选全公式验证次数上限。 | [src/search/nia/NiaSolver_farkas.cpp:308](../../src/search/nia/NiaSolver_farkas.cpp#L308) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_GROBNER_MAX_EQ` | 6 | Groebner 阶段接收等式数量阈值。 | [src/search/nia/reasoners/GroebnerIdealReasoner.cpp:96](../../src/search/nia/reasoners/GroebnerIdealReasoner.cpp#L96) | 测试字面引用 1 处 |
| `XOLVER_NIA_GROBNER_MAX_VARS` | 8 | Groebner 阶段接收变量数量阈值。 | [src/search/nia/reasoners/GroebnerIdealReasoner.cpp:101](../../src/search/nia/reasoners/GroebnerIdealReasoner.cpp#L101) | 测试字面引用 1 处 |
| `XOLVER_NIA_LS_BUDGET_MS` | 5000 ms（非正值无此时限） | NIA 局部搜索单次时间预算。 | [src/search/nia/search/NiaLocalSearch.cpp:48](../../src/search/nia/search/NiaLocalSearch.cpp#L48) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_LONG` | false；true 仅改变未覆盖的重启/翻转预算 | 预算快捷配置：未显式覆盖时从 20×800 调到 80×25000；是冗余预算别名，不是算法门。 | [src/search/nia/search/NiaLocalSearch.cpp:113](../../src/search/nia/search/NiaLocalSearch.cpp#L113) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_MAX_FLIPS` | 读取 fallback 0 保留成员 800；LS_LONG 可改为 25000 | 局部搜索每次重启最大翻转次数。 | [src/search/nia/search/NiaLocalSearch.cpp:111](../../src/search/nia/search/NiaLocalSearch.cpp#L111) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_RESTARTS` | 读取 fallback 0 保留成员 20；LS_LONG 可改为 80 | 局部搜索重启次数预算。 | [src/search/nia/search/NiaLocalSearch.cpp:108](../../src/search/nia/search/NiaLocalSearch.cpp#L108) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_TOTAL_MS` | 60000 ms（非正值无累计时限） | NIA 局部搜索累计时间预算。 | [src/search/nia/search/NiaLocalSearch.cpp:49](../../src/search/nia/search/NiaLocalSearch.cpp#L49) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_MCSAT_DFS_BUDGET` | 50000 | NIA MCSAT DFS 节点工作预算。 | [src/search/nia/mcsat/NiaMcsatEngine.cpp:178](../../src/search/nia/mcsat/NiaMcsatEngine.cpp#L178) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_MODULAR_ENUM_BUDGET` | 16777216 | 模数域枚举总工作预算。 | [src/search/nia/reasoners/ModularResidueReasoner.cpp:74](../../src/search/nia/reasoners/ModularResidueReasoner.cpp#L74) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_MODULAR_MAX_ENUM` | 50000 | 小模数推理每个模数的枚举上限。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:206](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L206) | 测试字面引用 1 处 |
| `XOLVER_NIA_MODULAR_MAX_VARS` | 15 | 小模数推理接收变量数量阈值。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:201](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L201) | 测试字面引用 1 处 |
| `XOLVER_NIA_MODULAR_MODULUS_CAP` | 262144 | 模数 residue 推理允许的模数大小上限。 | [src/search/nia/reasoners/ModularResidueReasoner.cpp:72](../../src/search/nia/reasoners/ModularResidueReasoner.cpp#L72) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_PRESOLVE_BUDGET_MS` | 50 | 整数 presolve fixpoint 时间预算。 | [src/search/nia/NiaSolver_linear.cpp:254](../../src/search/nia/NiaSolver_linear.cpp#L254) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_BOUNDCHAIN_MAX_ATOMS` | 2000 | bound-chain composer 输入原子数上限。 | [src/search/presolve/BoundChainComposer.cpp:55](../../src/search/presolve/BoundChainComposer.cpp#L55) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_BOUNDCHAIN_MAX_WORK` | 1500000 | bound-chain composer 工作量预算。 | [src/search/presolve/BoundChainComposer.cpp:57](../../src/search/presolve/BoundChainComposer.cpp#L57) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_DEADLINE_MS` | 2000 | CAC 混合路径时间份额；sole engine 策略还有外部墙钟语义。 | [src/search/nra/NraSolver_cac.cpp:293](../../src/search/nra/NraSolver_cac.cpp#L293) | 赋值形引用 1 处 |
| `XOLVER_NRA_CAC_SAT_FIRST_ALG_DEG` | 读取 0 保留成员 12 | algebraic sample-first 约束次数上限。 | [src/search/nra/core/CdcacCore.cpp:271](../../src/search/nra/core/CdcacCore.cpp#L271) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_BUDGET` | 读取 0 保留成员 2000000 | sample-first 节点预算。 | [src/search/nra/core/CdcacCore.cpp:255](../../src/search/nra/core/CdcacCore.cpp#L255) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_MAX_BITS` | 读取 0 保留成员 64 | sample-first 候选数值位数上限。 | [src/search/nra/core/CdcacCore.cpp:257](../../src/search/nra/core/CdcacCore.cpp#L257) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_MAX_DEG` | 12 | sample-first 可处理的次数上限。 | [src/search/nra/core/CdcacCore.cpp:844](../../src/search/nra/core/CdcacCore.cpp#L844), [src/search/nra/core/CdcacCore.cpp:845](../../src/search/nra/core/CdcacCore.cpp#L845) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_MS` | 读取 -1 保留成员 10000 ms；0 只保留节点上限 | sample-first 时间上限，0 保留节点预算。 | [src/search/nra/core/CdcacCore.cpp:259](../../src/search/nra/core/CdcacCore.cpp#L259) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_FIRST_TOWER_CAP` | 4 | algebraic sample-first 扩张塔深度上限。 | [src/search/nra/core/CdcacCore.cpp:2267](../../src/search/nra/core/CdcacCore.cpp#L2267) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_SAT_SAMPLE_DEPTH` | 2 | CAC 候选 sweep 变量层数限制。 | [src/search/nra/cac/CacEngine.cpp:226](../../src/search/nra/cac/CacEngine.cpp#L226) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CDCAC_MAX_DEGREE` | 0 | CDCAC 输入次数资源阈值，0 不加此限制。 | [src/search/nra/NraSolver.cpp:52](../../src/search/nra/NraSolver.cpp#L52) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CDCAC_MAX_VARS` | 0 | CDCAC 输入变量数资源阈值，0 不加此限制。 | [src/search/nra/NraSolver.cpp:51](../../src/search/nra/NraSolver.cpp#L51) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_EQ_CASCADE_DYADIC_DEPTH` | 20 | 等式 cascade dyadic 候选深度上限。 | [src/search/nra/StructuralIntegerProbe.cpp:653](../../src/search/nra/StructuralIntegerProbe.cpp#L653) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LAZARD_MAX_COEFF_BITS` | 65536 | Lazard/平方自由运算系数位数资源上限。 | [src/search/nra/core/CdcacCore.cpp:831](../../src/search/nra/core/CdcacCore.cpp#L831), [src/search/nra/lazard/LazardProjectionOperator.cpp:62](../../src/search/nra/lazard/LazardProjectionOperator.cpp#L62), [src/search/nra/lazard/Squarefree.cpp:26](../../src/search/nra/lazard/Squarefree.cpp#L26) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LIBPOLY_MAX_COEFF_BITS` | 262144 | libpoly 运算预估系数位数防护 cap，非正值回到安全缺省。 | [src/search/nra/backend/LibpolyBackend.cpp:122](../../src/search/nra/backend/LibpolyBackend.cpp#L122) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LINEARIZE_CAP` | 60 | 增量线性化 refinement 最大轮次。 | [src/search/nra/NraSolver_cac.cpp:596](../../src/search/nra/NraSolver_cac.cpp#L596) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LS_BUDGET_MS` | 250 | NRA 局部搜索累计时间份额，可能按墙钟缩放。 | [src/search/nra/NraSolver.cpp:357](../../src/search/nra/NraSolver.cpp#L357) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LS_MAX_DEN` | 1000000 | 局部搜索有理候选分母上限。 | [src/search/nra/reasoners/NraLocalSearch.cpp:655](../../src/search/nra/reasoners/NraLocalSearch.cpp#L655) | 测试字面引用 1 处 |
| `XOLVER_NRA_LS_MAX_ROUNDS` | 3000 | NRA 局部搜索最大轮次，可能按墙钟缩放。 | [src/search/nra/NraSolver.cpp:363](../../src/search/nra/NraSolver.cpp#L363) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LS_TOP_VARS` | 8 | 每轮局部搜索处理的变量预算。 | [src/search/nra/reasoners/NraLocalSearch.cpp:611](../../src/search/nra/reasoners/NraLocalSearch.cpp#L611) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLEXT_TANGENT_PERTURB_CAP` | 4 | 每次求解允许的切线扰动次数。 | [src/search/nra/NraSolver_cac.cpp:716](../../src/search/nra/NraSolver_cac.cpp#L716) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_DFS_BUDGET` | 50000 | NLSAT DFS 节点预算。 | [src/search/nra/engine/NlsatEngine.cpp:419](../../src/search/nra/engine/NlsatEngine.cpp#L419) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_FALLBACK_DEG_CAP` | 12 | NLSAT→CDCAC 回退的最高次数阈值。 | [src/search/nra/engine/NlsatEngine.cpp:556](../../src/search/nra/engine/NlsatEngine.cpp#L556) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_ISO_BUDGET` | 1500 | NLSAT 每次 pickValue 的根隔离调用上限。 | [src/search/nra/engine/NlsatEngine.cpp:162](../../src/search/nra/engine/NlsatEngine.cpp#L162) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_MAX_CORE_POLYS` | 20 | NLSAT 核心多项式数量上限。 | [src/search/nra/core/CdcacCore.cpp:3052](../../src/search/nra/core/CdcacCore.cpp#L3052), [src/search/nra/core/CdcacCore.cpp:3053](../../src/search/nra/core/CdcacCore.cpp#L3053) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_MAX_CORE_VARS` | 8 | NLSAT 核心变量数量上限。 | [src/search/nra/core/CdcacCore.cpp:3049](../../src/search/nra/core/CdcacCore.cpp#L3049), [src/search/nra/core/CdcacCore.cpp:3050](../../src/search/nra/core/CdcacCore.cpp#L3050) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_MAX_ELIM_DEG` | 10 | NLSAT elimination 的次数上限。 | [src/search/nra/core/CdcacCore.cpp:3055](../../src/search/nra/core/CdcacCore.cpp#L3055), [src/search/nra/core/CdcacCore.cpp:3056](../../src/search/nra/core/CdcacCore.cpp#L3056) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_NLSAT_ROOT_DEG_CAP` | 12 | 精确根候选路径的次数上限。 | [src/search/nra/engine/NlsatEngine.cpp:836](../../src/search/nra/engine/NlsatEngine.cpp#L836) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PRESOLVE_BUDGET_MS` | 50 | NRA presolve/preelim 阶段时间上限。 | [src/search/nra/NraSolver_stages.cpp:63](../../src/search/nra/NraSolver_stages.cpp#L63), [src/search/nra/NraSolver_stages.cpp:639](../../src/search/nra/NraSolver_stages.cpp#L639) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PROJ_MAX_COEFF_BITS` | 50000000 | 投影多项式总系数位长 cap。 | [src/search/nra/core/CdcacCore.cpp:481](../../src/search/nra/core/CdcacCore.cpp#L481), [src/search/nra/core/CdcacCore.cpp:482](../../src/search/nra/core/CdcacCore.cpp#L482) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PROJ_MAX_DEG` | 100000 | 投影多项式次数 cap。 | [src/search/nra/core/CdcacCore.cpp:475](../../src/search/nra/core/CdcacCore.cpp#L475), [src/search/nra/core/CdcacCore.cpp:476](../../src/search/nra/core/CdcacCore.cpp#L476) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PROJ_MAX_TERMS` | 2000000 | 投影多项式项数 cap。 | [src/search/nra/core/CdcacCore.cpp:472](../../src/search/nra/core/CdcacCore.cpp#L472), [src/search/nra/core/CdcacCore.cpp:473](../../src/search/nra/core/CdcacCore.cpp#L473) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PA_RESIDUES` | 100000 | Presburger 消元 residue 枚举工作预算。 | [src/runtime/Solver_impl_checksat.cpp:95](../../src/runtime/Solver_impl_checksat.cpp#L95) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PA_WORK` | 2000000 | Presburger 消元总体工作预算。 | [src/runtime/Solver_impl_checksat.cpp:94](../../src/runtime/Solver_impl_checksat.cpp#L94) | 测试字面引用 2 处；赋值形引用 1 处 |
| `XOLVER_PP_BOUNDED_ENUM_MAX_CARTESIAN` | 256 | bounded enumeration 预处理的 Cartesian 展开规模 cap。 | [src/frontend/preprocess/BoundedEnumeration.cpp:98](../../src/frontend/preprocess/BoundedEnumeration.cpp#L98) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_SOLVE_EQS_BUDGET` | 40000000 | solve-eqs 代换工作预算。 | [src/frontend/preprocess/SolveEqs.cpp:17](../../src/frontend/preprocess/SolveEqs.cpp#L17) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_SOLVE_EQS_GROWTH_CAP` | 1.30 | solve-eqs 公式 DAG 相对增长阈值。 | [src/frontend/preprocess/SolveEqs.cpp:22](../../src/frontend/preprocess/SolveEqs.cpp#L22) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_LEMMA_MGMT` | unset 0; true uses 100000 | lemma 缓存容量，unset/0 无上限，true 默认 100000，1 表示容量 1。 | [src/search/coordination/TheoryLemmaDatabase.cpp:12](../../src/search/coordination/TheoryLemmaDatabase.cpp#L12) | 测试字面引用 5 处 |
| `XOLVER_STRAT_PORTFOLIO_BUDGET_MS` | 0 | 覆盖所有 portfolio 臂的时间分配；0 保留各臂默认值。 | [src/runtime/factory/StrategyPresets.cpp:19](../../src/runtime/factory/StrategyPresets.cpp#L19) | 测试字面引用 5 处 |
| `XOLVER_WALLCLOCK_MS` | 0 | 整个求解查询的墙钟预算，0 不限。 | [src/runtime/Solver.cpp:1152](../../src/runtime/Solver.cpp#L1152) | 工具字面引用 1 处；赋值形引用 1 处 |
| `XOLVER_WALLCLOCK_SCALE` | 0 | 按 wall-clock 缩放内部工作预算的资源分配策略。 | [src/base/SolveClock.cpp:58](../../src/base/SolveClock.cpp#L58) | 测试字面引用 3 处 |

### 正常策略选择和调度参数（11）

| 控制 | 缺省 | 语义与处置依据 | 读取位置 | 启用/配置证据 |
|---|---|---|---|---|
| `XOLVER_LRA_INCREMENTAL_BETA_REFRESH` | 0 | 增量回溯中强制完整 beta 重算的周期。 | [src/search/lra/GeneralSimplex.cpp:67](../../src/search/lra/GeneralSimplex.cpp#L67) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BB_EARLY_MIN_ACTIVE` | 50 | 早期 bit-blast 适用的约束数阈值，默认 50。 | [src/search/nia/NiaSolver_bitblast.cpp:70](../../src/search/nia/NiaSolver_bitblast.cpp#L70) | 测试字面引用 1 处 |
| `XOLVER_NIA_MODULAR_MODULI` | [2,3,4,5,7,8,9,11] | 显式小模数列表，解析为 [2,100] 范围去重整数。 | [src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp:222](../../src/search/nia/reasoners/AlgebraicIntegerReasoner.cpp#L222) | 测试字面引用 4 处 |
| `XOLVER_NRA_LS_NOISE_PCT` | 35 | 局部搜索扰动动作概率，候选仍经模型检查。 | [src/search/nra/reasoners/NraLocalSearch.cpp:960](../../src/search/nra/reasoners/NraLocalSearch.cpp#L960) | 测试字面引用 1 处 |
| `XOLVER_NRA_LS_SA_PCT` | 33 | 局部搜索模拟退火动作概率。 | [src/search/nra/reasoners/NraLocalSearch.cpp:915](../../src/search/nra/reasoners/NraLocalSearch.cpp#L915) | 测试字面引用 1 处 |
| `XOLVER_NRA_NLEXT_TANGENT_PERTURB_MINROUND` | 30 | 切线扰动前的最小 refinement 轮数，默认 30。 | [src/search/nra/NraSolver_cac.cpp:726](../../src/search/nra/NraSolver_cac.cpp#L726) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_OSF_FACTOR_CADENCE` | 1 | OSF 因式推理调用节奏。 | [src/search/nra/NraSolver_stages.cpp:575](../../src/search/nra/NraSolver_stages.cpp#L575) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_PROJECTION` | Automatic | 显式 Automatic/Collins/Lazard 投影策略。 | [src/search/nra/core/CdcacCore.cpp:231](../../src/search/nra/core/CdcacCore.cpp#L231) | 测试字面引用 1 处 |
| `XOLVER_PROP_CHECK_EVERY` | 0 | theory check 的赋值增长阈值，0 采用自适应 max(3,size/10)。 | [src/search/sat/CadicalTheoryPropagator.cpp:742](../../src/search/sat/CadicalTheoryPropagator.cpp#L742) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_STRAT_PORTFOLIO` | false | 选择分预算 portfolio 求解入口；当前 LIA 有普通臂和 cuts 臂。 | [src/runtime/Solver.cpp:1174](../../src/runtime/Solver.cpp#L1174), [src/runtime/Solver.cpp:1178](../../src/runtime/Solver.cpp#L1178) | 测试字面引用 4 处 |
| `XOLVER_THEORY_ENTAIL_PROP_EVERY` | 1 | 理论蕴含传播调用节奏，最小 1。 | [src/search/sat/CadicalTheoryPropagator.cpp:905](../../src/search/sat/CadicalTheoryPropagator.cpp#L905) | 限定范围未见字面引用；不排除直接 API/外部 |

### 诊断、观测及调试核验（103）

| 控制 | 缺省 | 语义与处置依据 | 读取位置 | 启用/配置证据 |
|---|---|---|---|---|
| `ARITH_STAGE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/arith/ArithSolverBase.cpp:134](../../src/search/arith/ArithSolverBase.cpp#L134) | 限定范围未见字面引用；不排除直接 API/外部 |
| `ARITH_STAGE_ENTER` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/arith/ArithSolverBase.cpp:101](../../src/search/arith/ArithSolverBase.cpp#L101) | 限定范围未见字面引用；不排除直接 API/外部 |
| `ARITH_STAGE_PROF` | "/tmp/xolver_stageprof.txt" | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/arith/ArithSolverBase.cpp:69](../../src/search/arith/ArithSolverBase.cpp#L69), [src/search/arith/ArithSolverBase.cpp:78](../../src/search/arith/ArithSolverBase.cpp#L78) | 测试字面引用 2 处；工具字面引用 1 处 |
| `BB_ASSERT_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/bitblast/PolyBitBlaster.cpp:80](../../src/search/bitblast/PolyBitBlaster.cpp#L80) | 限定范围未见字面引用；不排除直接 API/外部 |
| `EUF_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/combination/Purifier.cpp:594](../../src/search/combination/Purifier.cpp#L594), [src/search/euf/EufSolver.cpp:446](../../src/search/euf/EufSolver.cpp#L446), [src/search/euf/EufSolver.cpp:648](../../src/search/euf/EufSolver.cpp#L648), [src/search/euf/EufSolver_check.cpp:433](../../src/search/euf/EufSolver_check.cpp#L433), [src/search/euf/EufSolver_check.cpp:443](../../src/search/euf/EufSolver_check.cpp#L443), [src/search/euf/EufSolver_check.cpp:454](../../src/search/euf/EufSolver_check.cpp#L454), [src/search/euf/EufSolver_check.cpp:467](../../src/search/euf/EufSolver_check.cpp#L467), [src/search/euf/EufSolver_check.cpp:482](../../src/search/euf/EufSolver_check.cpp#L482) | 限定范围未见字面引用；不排除直接 API/外部 |
| `EUF_VERIFY` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/euf/EufSolver_check.cpp:113](../../src/search/euf/EufSolver_check.cpp#L113) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_BITBLAST_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/bitblast/BitBlastSolver.cpp:217](../../src/search/bitblast/BitBlastSolver.cpp#L217) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_BITBLAST_PROF` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/bitblast/BitBlastSolver.cpp:159](../../src/search/bitblast/BitBlastSolver.cpp#L159) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_DOM_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_refute.cpp:209](../../src/search/nia/NiaSolver_refute.cpp#L209), [src/search/nia/core/DomainStore.cpp:257](../../src/search/nia/core/DomainStore.cpp#L257) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_EAGER_BB_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/bitblast/EagerBitBlastSolver.cpp:139](../../src/search/bitblast/EagerBitBlastSolver.cpp#L139), [src/search/bitblast/EagerBitBlastSolver.cpp:202](../../src/search/bitblast/EagerBitBlastSolver.cpp#L202), [src/search/bitblast/EagerBitBlastSolver.cpp:232](../../src/search/bitblast/EagerBitBlastSolver.cpp#L232), [src/search/bitblast/EagerBitBlastSolver.cpp:237](../../src/search/bitblast/EagerBitBlastSolver.cpp#L237), [src/search/bitblast/EagerBitBlastSolver.cpp:289](../../src/search/bitblast/EagerBitBlastSolver.cpp#L289) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_EAGER_BB_GATE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:1088](../../src/runtime/Solver_impl_checksat.cpp#L1088) | 限定范围未见字面引用；不排除直接 API/外部 |
| `NIA_OPP_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver.cpp:395](../../src/search/nia/NiaSolver.cpp#L395) | 限定范围未见字面引用；不排除直接 API/外部 |
| `SOLVE_PHASE_PROF` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:171](../../src/runtime/Solver_impl_checksat.cpp#L171) | 工具字面引用 1 处 |
| `XOLVER_ANIA_PROF` | false | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/array/AniaProfile.h:111](../../src/search/array/AniaProfile.h#L111) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_ARRAY_NOARR_DOWNGRADE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:892](../../src/runtime/Solver_impl_checksat.cpp#L892) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_ASSERT_PF_INV` | false (unset) | 开启 proof-forest 不变量检查，违例会 abort；属于诊断但不保证纯日志/无行为影响。 | [src/search/euf/EufSolver_diagnostics.cpp:370](../../src/search/euf/EufSolver_diagnostics.cpp#L370) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/array/ArrayReasoner.cpp:634](../../src/search/array/ArrayReasoner.cpp#L634), [src/search/euf/EufSolver_check.cpp:394](../../src/search/euf/EufSolver_check.cpp#L394), [src/search/euf/EufSolver_check.cpp:423](../../src/search/euf/EufSolver_check.cpp#L423) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_R2D_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/array/ArrayReasoner.cpp:489](../../src/search/array/ArrayReasoner.cpp#L489), [src/search/euf/EufSolver_check.cpp:522](../../src/search/euf/EufSolver_check.cpp#L522), [src/search/euf/EufSolver_check.cpp:599](../../src/search/euf/EufSolver_check.cpp#L599) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_REFINE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/euf/EufSolver_check.cpp:648](../../src/search/euf/EufSolver_check.cpp#L648) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_AX_STORECOMM_EXT_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/array/ArrayReasoner.cpp:807](../../src/search/array/ArrayReasoner.cpp#L807) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_CMS_WIDTH_PROBE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:1648](../../src/runtime/Solver_impl_checksat.cpp#L1648) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_CONFLICT_TRACE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:645](../../src/search/coordination/TheoryManager.cpp#L645) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_COMB_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:36](../../src/search/coordination/TheoryManager.cpp#L36) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DECIDE_PROBE` | unset 0; true uses 2000 | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/sat/CadicalTheoryPropagator.cpp:293](../../src/search/sat/CadicalTheoryPropagator.cpp#L293), [src/search/sat/CadicalTheoryPropagator.cpp:295](../../src/search/sat/CadicalTheoryPropagator.cpp#L295), [src/search/sat/CadicalTheoryPropagator.cpp:335](../../src/search/sat/CadicalTheoryPropagator.cpp#L335) | 测试字面引用 2 处 |
| `XOLVER_DIAG_AM` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_model.cpp:126](../../src/runtime/Solver_impl_model.cpp#L126), [src/search/array/ArrayModelCompletion.cpp:17](../../src/search/array/ArrayModelCompletion.cpp#L17), [src/search/array/ArrayModelCompletion.cpp:240](../../src/search/array/ArrayModelCompletion.cpp#L240), [src/search/euf/EufSolver_array.cpp:411](../../src/search/euf/EufSolver_array.cpp#L411) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DIAG_AMV` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/evidence/ArithModelValidator.cpp:21](../../src/evidence/ArithModelValidator.cpp#L21) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DIAG_AMV_DEEP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/evidence/ArithModelValidator.cpp:22](../../src/evidence/ArithModelValidator.cpp#L22) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DIAG_CMS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/candidate/CandidateModelSearch.cpp:31](../../src/search/candidate/CandidateModelSearch.cpp#L31), [src/search/candidate/CandidateModelSearch.cpp:55](../../src/search/candidate/CandidateModelSearch.cpp#L55) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DIAG_FI` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:1624](../../src/search/coordination/TheoryManager.cpp#L1624) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DIAG_PF_INV` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/euf/EufSolver_diagnostics.cpp:369](../../src/search/euf/EufSolver_diagnostics.cpp#L369) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DT_HC_STATS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/datatype/DtReasoner.cpp:156](../../src/search/datatype/DtReasoner.cpp#L156) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DT_VALIDATE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/euf/EufSolver_check.cpp:707](../../src/search/euf/EufSolver_check.cpp#L707) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DT_VALIDATE_PER_ASSERT` | false (unset) | 统计打印每个断言验证结果，不控制是否运行 validator。 | [src/search/datatype/DtModelValidator.cpp:421](../../src/search/datatype/DtModelValidator.cpp#L421) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_DUMP_FINAL_ASSERTS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:856](../../src/runtime/Solver_impl_checksat.cpp#L856) | 工具字面引用 1 处 |
| `XOLVER_ENTAIL_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:346](../../src/search/coordination/TheoryManager.cpp#L346) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_EUF_HOTPROFILE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/euf/EufSolver.cpp:84](../../src/search/euf/EufSolver.cpp#L84) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_L4R_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:523](../../src/search/coordination/TheoryManager.cpp#L523), [src/search/coordination/TheoryManager.cpp:767](../../src/search/coordination/TheoryManager.cpp#L767), [src/search/coordination/TheoryManager.cpp:840](../../src/search/coordination/TheoryManager.cpp#L840), [src/search/coordination/TheoryManager.cpp:924](../../src/search/coordination/TheoryManager.cpp#L924), [src/search/sat/CadicalTheoryPropagator.cpp:926](../../src/search/sat/CadicalTheoryPropagator.cpp#L926) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LIA_DUMP_DIR` | empty path | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/lia/LiaSolver_model.cpp:251](../../src/search/lia/LiaSolver_model.cpp#L251) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LRA_BETA_EVERY` | 0 | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/lra/GeneralSimplex.cpp:327](../../src/search/lra/GeneralSimplex.cpp#L327) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LRA_BOUND_AXIOMS_DIAG` | false | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/linear/BoundAxiomGenerator.cpp:187](../../src/search/linear/BoundAxiomGenerator.cpp#L187) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LRA_PROFILE_EVERY` | 0 | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/lra/GeneralSimplex.cpp:711](../../src/search/lra/GeneralSimplex.cpp#L711) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_LRA_VERIFY_BETA` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/lra/GeneralSimplex.cpp:252](../../src/search/lra/GeneralSimplex.cpp#L252) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_ARITH_VALUE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_combination.cpp:242](../../src/search/nia/NiaSolver_combination.cpp#L242) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_BB_ENTRY_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_bitblast.cpp:72](../../src/search/nia/NiaSolver_bitblast.cpp#L72), [src/search/nia/NiaSolver_bitblast.cpp:113](../../src/search/nia/NiaSolver_bitblast.cpp#L113) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_CT_DIAG` | empty path | 写诊断文件并做 abstraction 模型核验及 CT 可行性子查询；当前无论结果均返回 false，不据此发新求解结论。 | [src/search/nia/farkas/LeafFarkasLia.cpp:20](../../src/search/nia/farkas/LeafFarkasLia.cpp#L20), [src/search/nia/farkas/LeafFarkasLia.cpp:182](../../src/search/nia/farkas/LeafFarkasLia.cpp#L182), [src/search/nia/farkas/LeafFarkasLia.cpp:296](../../src/search/nia/farkas/LeafFarkasLia.cpp#L296) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_CT_SMT` | empty path | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/farkas/LeafFarkasLia.cpp:234](../../src/search/nia/farkas/LeafFarkasLia.cpp#L234) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_DUMP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:1443](../../src/runtime/Solver_impl_checksat.cpp#L1443), [src/search/nia/NiaSolver.cpp:52](../../src/search/nia/NiaSolver.cpp#L52) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_DUMP_FILE` | "/tmp/farkas_dump" | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:1444](../../src/runtime/Solver_impl_checksat.cpp#L1444), [src/search/nia/NiaSolver.cpp:53](../../src/search/nia/NiaSolver.cpp#L53) | 测试字面引用 2 处 |
| `XOLVER_NIA_FARKAS_FAILDIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_farkas.cpp:351](../../src/search/nia/NiaSolver_farkas.cpp#L351) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_OR_TRACE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_farkas.cpp:103](../../src/search/nia/NiaSolver_farkas.cpp#L103), [src/search/nia/NiaSolver_farkas.cpp:562](../../src/search/nia/NiaSolver_farkas.cpp#L562) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_OUTER_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_farkas.cpp:116](../../src/search/nia/NiaSolver_farkas.cpp#L116) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_REJECT_DUMP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/farkas/FarkasOrDetector.cpp:517](../../src/search/nia/farkas/FarkasOrDetector.cpp#L517) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_FARKAS_REJECT_FILE` | "/tmp/farkas_reject" | Farkas 拒绝诊断输出文件路径，受 REJECT_DUMP 控制，缺省 /tmp/farkas_reject。 | [src/search/nia/farkas/FarkasOrDetector.cpp:519](../../src/search/nia/farkas/FarkasOrDetector.cpp#L519) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_INT_BOUND_PROP_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_engines.cpp:292](../../src/search/nia/NiaSolver_engines.cpp#L292) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LINDECIDE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_linear.cpp:90](../../src/search/nia/NiaSolver_linear.cpp#L90), [src/search/nia/search/NiaLinearDecider.cpp:32](../../src/search/nia/search/NiaLinearDecider.cpp#L32) | 赋值形引用 2 处 |
| `XOLVER_NIA_LINEAR_DOWNGRADE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:950](../../src/runtime/Solver_impl_checksat.cpp#L950) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LINPROP_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_linear.cpp:182](../../src/search/nia/NiaSolver_linear.cpp#L182), [src/search/nia/search/NiaLinearDecider.cpp:184](../../src/search/nia/search/NiaLinearDecider.cpp#L184) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_LS_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/search/NiaLocalSearch.cpp:1730](../../src/search/nia/search/NiaLocalSearch.cpp#L1730), [src/search/nia/search/NiaLocalSearch.cpp:2074](../../src/search/nia/search/NiaLocalSearch.cpp#L2074) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_MODULAR_DIAG` | 0 | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/reasoners/ModularResidueReasoner.cpp:486](../../src/search/nia/reasoners/ModularResidueReasoner.cpp#L486) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_OMEGA_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_engines.cpp:117](../../src/search/nia/NiaSolver_engines.cpp#L117) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_SHARED_EQ_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_combination.cpp:498](../../src/search/nia/NiaSolver_combination.cpp#L498) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_SMALL_PRIME_MODULAR_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nia/NiaSolver_engines.cpp:190](../../src/search/nia/NiaSolver_engines.cpp#L190) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NIA_ZOHAR_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/ZoharBwiAxiomEmitter.cpp:200](../../src/frontend/preprocess/ZoharBwiAxiomEmitter.cpp#L200), [src/runtime/Solver_impl_checksat.cpp:598](../../src/runtime/Solver_impl_checksat.cpp#L598) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NO_DEBUG` | false | NO 指 Nelson–Oppen；设置该值启用 NO_DBG stderr 输出，并非关闭 debug。 | [src/contracts/DebugTrace.h:16](../../src/contracts/DebugTrace.h#L16) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NO_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:869](../../src/search/coordination/TheoryManager.cpp#L869) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_cac.cpp:316](../../src/search/nra/NraSolver_cac.cpp#L316), [src/search/nra/cac/CacEngine.cpp:230](../../src/search/nra/cac/CacEngine.cpp#L230), [src/search/nra/cac/CacEngine.cpp:329](../../src/search/nra/cac/CacEngine.cpp#L329), [src/search/nra/cac/SingleCellProjection.cpp:243](../../src/search/nra/cac/SingleCellProjection.cpp#L243) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_DUMP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/cac/SingleCellProjection.cpp:432](../../src/search/nra/cac/SingleCellProjection.cpp#L432) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_INSTR` | false (unset) | 析构时打印 projection instrumentation 计数。 | [src/search/nra/cac/SingleCellProjection.cpp:40](../../src/search/nra/cac/SingleCellProjection.cpp#L40) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_INT_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/core/CdcacCore.cpp:1449](../../src/search/nra/core/CdcacCore.cpp#L1449), [src/search/nra/core/CdcacCore.cpp:1846](../../src/search/nra/core/CdcacCore.cpp#L1846) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CAC_TRACE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/cac/CacEngine.cpp:480](../../src/search/nra/cac/CacEngine.cpp#L480) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_CDCAC_GUARD_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_cac.cpp:549](../../src/search/nra/NraSolver_cac.cpp#L549) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_EQ_CASCADE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/StructuralIntegerProbe.cpp:660](../../src/search/nra/StructuralIntegerProbe.cpp#L660) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_GROBNER_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:371](../../src/search/nra/NraSolver_stages.cpp#L371) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_HYB_PARTITION_STATS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver.cpp:292](../../src/search/nra/NraSolver.cpp#L292), [src/search/nra/core/HybridPartitionStats.cpp:69](../../src/search/nra/core/HybridPartitionStats.cpp#L69) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_ICP_DIAG` | false | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/core/CdcacCore.cpp:901](../../src/search/nra/core/CdcacCore.cpp#L901) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_INT_PROBE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:900](../../src/search/nra/NraSolver_stages.cpp#L900), [src/search/nra/NraSolver_stages.cpp:921](../../src/search/nra/NraSolver_stages.cpp#L921), [src/search/nra/StructuralIntegerProbe.cpp:347](../../src/search/nra/StructuralIntegerProbe.cpp#L347) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_KERNEL_STATS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/algebra/poly/LibPolyKernel.cpp:79](../../src/algebra/poly/LibPolyKernel.cpp#L79) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LAZARD_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/backend/LibpolyBackend.cpp:1791](../../src/search/nra/backend/LibpolyBackend.cpp#L1791), [src/search/nra/backend/LibpolyBackend.cpp:1999](../../src/search/nra/backend/LibpolyBackend.cpp#L1999), [src/search/nra/core/CdcacCore.cpp:500](../../src/search/nra/core/CdcacCore.cpp#L500), [src/search/nra/core/CdcacCore.cpp:547](../../src/search/nra/core/CdcacCore.cpp#L547), [src/search/nra/core/CdcacCore.cpp:937](../../src/search/nra/core/CdcacCore.cpp#L937), [src/search/nra/core/CdcacCore.cpp:955](../../src/search/nra/core/CdcacCore.cpp#L955), [src/search/nra/core/CdcacCore.cpp:1127](../../src/search/nra/core/CdcacCore.cpp#L1127), [src/search/nra/core/CdcacCore.cpp:1196](../../src/search/nra/core/CdcacCore.cpp#L1196), [src/search/nra/core/CdcacCore.cpp:1885](../../src/search/nra/core/CdcacCore.cpp#L1885) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LIBPOLY_FIREWALL_DIAG` | false (unset) | 打印超 cap 拒绝原因，cap 不受此值解除。 | [src/search/nra/backend/LibpolyBackend.cpp:129](../../src/search/nra/backend/LibpolyBackend.cpp#L129) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LINEARIZE_DUMP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_cac.cpp:639](../../src/search/nra/NraSolver_cac.cpp#L639) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LINEAR_DOWNGRADE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:923](../../src/runtime/Solver_impl_checksat.cpp#L923) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_LS_STATS` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/reasoners/NraLocalSearch.cpp:77](../../src/search/nra/reasoners/NraLocalSearch.cpp#L77) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_OSF_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:587](../../src/search/nra/NraSolver_stages.cpp#L587), [src/search/nra/simplex/PolynomialIntervalPruner.cpp:1172](../../src/search/nra/simplex/PolynomialIntervalPruner.cpp#L1172) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_SIGN_REFUTE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:326](../../src/search/nra/NraSolver_stages.cpp#L326) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_SIGN_SPLIT_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:483](../../src/search/nra/NraSolver_stages.cpp#L483) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_STAGE_TIMING` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver.cpp:60](../../src/search/nra/NraSolver.cpp#L60), [src/search/nra/NraSolver.cpp:205](../../src/search/nra/NraSolver.cpp#L205) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_STAGE_TRACE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver.cpp:61](../../src/search/nra/NraSolver.cpp#L61) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_STAGE_TRACE_FILE` | empty path | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver.cpp:68](../../src/search/nra/NraSolver.cpp#L68) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_SUBTROP_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_stages.cpp:880](../../src/search/nra/NraSolver_stages.cpp#L880) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_NRA_TOWER_DIAG` | empty path | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/nra/NraSolver_cac.cpp:54](../../src/search/nra/NraSolver_cac.cpp#L54), [src/search/nra/NraSolver_cac.cpp:530](../../src/search/nra/NraSolver_cac.cpp#L530), [src/search/nra/backend/LibpolyBackend.cpp:666](../../src/search/nra/backend/LibpolyBackend.cpp#L666), [src/search/nra/backend/LibpolyBackend.cpp:1893](../../src/search/nra/backend/LibpolyBackend.cpp#L1893), [src/search/nra/cac/CacEngine.cpp:154](../../src/search/nra/cac/CacEngine.cpp#L154), [src/search/nra/cac/CacEngine.cpp:402](../../src/search/nra/cac/CacEngine.cpp#L402), [src/search/nra/core/CdcacCore.cpp:23](../../src/search/nra/core/CdcacCore.cpp#L23), [src/search/nra/core/CdcacCore.cpp:731](../../src/search/nra/core/CdcacCore.cpp#L731), [src/search/nra/core/CdcacCore.cpp:746](../../src/search/nra/core/CdcacCore.cpp#L746), [src/search/nra/core/CdcacCore.cpp:776](../../src/search/nra/core/CdcacCore.cpp#L776), [src/search/nra/core/CdcacCore.cpp:786](../../src/search/nra/core/CdcacCore.cpp#L786), [src/search/nra/core/CdcacCore.cpp:970](../../src/search/nra/core/CdcacCore.cpp#L970), [src/search/nra/core/CdcacCore.cpp:985](../../src/search/nra/core/CdcacCore.cpp#L985), [src/search/nra/core/CdcacCore.cpp:1239](../../src/search/nra/core/CdcacCore.cpp#L1239) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_MONOMIAL_SHARE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/MonomialSharingPass.cpp:114](../../src/frontend/preprocess/MonomialSharingPass.cpp#L114) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_ROW_FOLD_DIAG` | false | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/ArrayReadOverWrite.cpp:17](../../src/frontend/preprocess/ArrayReadOverWrite.cpp#L17) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PP_SOLVE_EQS_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/SolveEqs.cpp:175](../../src/frontend/preprocess/SolveEqs.cpp#L175), [src/frontend/preprocess/SolveEqs.cpp:219](../../src/frontend/preprocess/SolveEqs.cpp#L219), [src/frontend/preprocess/SolveEqs.cpp:234](../../src/frontend/preprocess/SolveEqs.cpp#L234) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_PRESOLVE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/presolve/BoundChainComposer.cpp:58](../../src/search/presolve/BoundChainComposer.cpp#L58), [src/search/presolve/PresolveEngine.cpp:101](../../src/search/presolve/PresolveEngine.cpp#L101) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_RELEVANCY_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/runtime/Solver_impl_checksat.cpp:1490](../../src/runtime/Solver_impl_checksat.cpp#L1490) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_PROF` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/sat/CadicalTheoryPropagator.cpp:182](../../src/search/sat/CadicalTheoryPropagator.cpp#L182), [src/search/sat/CadicalTheoryPropagator.cpp:250](../../src/search/sat/CadicalTheoryPropagator.cpp#L250), [src/search/sat/CadicalTheoryPropagator.cpp:401](../../src/search/sat/CadicalTheoryPropagator.cpp#L401), [src/search/sat/CadicalTheoryPropagator.cpp:430](../../src/search/sat/CadicalTheoryPropagator.cpp#L430), [src/search/sat/CadicalTheoryPropagator.cpp:554](../../src/search/sat/CadicalTheoryPropagator.cpp#L554), [src/search/sat/CadicalTheoryPropagator.cpp:611](../../src/search/sat/CadicalTheoryPropagator.cpp#L611), [src/search/sat/CadicalTheoryPropagator.cpp:636](../../src/search/sat/CadicalTheoryPropagator.cpp#L636), [src/search/sat/CadicalTheoryPropagator.cpp:654](../../src/search/sat/CadicalTheoryPropagator.cpp#L654), [src/search/sat/CadicalTheoryPropagator.cpp:680](../../src/search/sat/CadicalTheoryPropagator.cpp#L680), [src/search/sat/CadicalTheoryPropagator.cpp:937](../../src/search/sat/CadicalTheoryPropagator.cpp#L937) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_SAMPLE` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/sat/CadicalBackend.cpp:188](../../src/search/sat/CadicalBackend.cpp#L188) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SAT_SIZE_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/sat/CadicalBackend.cpp:189](../../src/search/sat/CadicalBackend.cpp#L189) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_SELFPROF` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [app/main.cpp:39](../../app/main.cpp#L39) | 工具字面引用 1 处 |
| `XOLVER_TARGETED_PP_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp:298](../../src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp#L298), [src/frontend/preprocess/targeted/UfApplyAckermann.cpp:141](../../src/frontend/preprocess/targeted/UfApplyAckermann.cpp#L141), [src/runtime/Solver_impl_model.cpp:386](../../src/runtime/Solver_impl_model.cpp#L386) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_TARGETED_PP_DUMP` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp:321](../../src/frontend/preprocess/targeted/ReadOnlyArrayElim.cpp#L321) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_TMCHECK_HB` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/coordination/TheoryManager.cpp:622](../../src/search/coordination/TheoryManager.cpp#L622) | 限定范围未见字面引用；不排除直接 API/外部 |
| `XOLVER_WISA_DIAG` | false (unset) | 调用点用于日志、统计、计时或额外不变量检查；具体动作和调用语义见本条源码上下文。 | [src/search/sat/CadicalTheoryPropagator.cpp:833](../../src/search/sat/CadicalTheoryPropagator.cpp#L833) | 限定范围未见字面引用；不排除直接 API/外部 |
