# 第二轮实现与服务器验证

本轮执行于 Panda1 `/pub/data/jiafq/xolver`，主要测试由 ExperimentOS 调度。WSL 仅编辑、检查语法和打包。整个过程复用 `build/`，写入由 `.writer.lock` 串行化，仅保留必要的冻结二进制和验证记录。

R5 完整终验已通过。以下严格区分版本，保留 R2/R3/R4 的失败记录及其修复过程。源码基线仍为 `e927757f5a033e244e96d7d41234866fb783d038`，子模块保持第一轮记录的修订。

## 已得到的证据

| 检查 | 已完成结果 | 版本边界 |
|---|---|---|
| 原生单测 | 1527/1527，512984 条断言；0 失败、0 跳过 | R5 |
| 仓库文件回归 | 820/820 通过；串行、每例 240 秒上限 | R5 |
| CLI / 工具测试 | 31/31 通过，包括 PA 功能测试 | R5 |
| 已登记 known gap | 1 项仍为 unknown，报告为 KNOWN_FAIL | R5；不能算作已解决 |
| 原始组合差分 | 种子 1、17，各 100 例；199 个确定答案与双 oracle 一致，1 unknown | R5 |
| 扩展组合差分 | 600 例，581 个确定答案一致，19 unknown；0 错误答案、崩溃、超时或 oracle 跳过 | R5 |
| 恢复数组模型 | 10/10 正面验证全部原始断言 | R5，独立 EOS 任务 |
| PA 差分 | 300 例；290 例双 oracle 一致，其中 270 个确定答案匹配、20 unknown；另 10 例 oracle 未共同给出确定答案 | R4，PA 引擎和分流入口之后未改动 |
| PA 优化对照 | 同一组 300 输入，candidate unknown 从 121 减至 22；两个版本均无观测到的反向答案 | `pa-r2` 与 `pa-r3` |
| 符号堆求解 | 原生测试包含 200 个随机小查询与有限位置赋值穷举对照，以及模型、冲突证书的篡改拒绝 | 包含在原生单测中 |
| Coq 证明 | coqc、coqchk 均成功；6 条定理不依赖额外公理 | `formal-r3`，证明源码之后未改动 |
| Python | 30/30 通过 | R5 |
| 46 例证明语料 | 5 个完整 CNF 反证、32 个 CNF 骨架、9 个无证明；无 checker 拒绝或执行错误 | R5 |

扩展差分各种子的 unknown 数为：1 → 0，17 → 1，43 → 4，79 → 2，101 → 2，20261020 → 10。原 11 例均解决；最终留下的 seed 17 / case 10 是另一条 QF_ALRA 公式。R4 曾达到原 200 例全确定，但该版本另有原生单测暴露的 false SAT，因此不能以它替代最终结果。

PA 的 22 个 unknown 中有 2 个也属于 oracle 跳过的 10 例，因此不能把“290 个可核对输入”和“22 unknown”直接相减。其他 8 个 oracle 跳过输入被 Xolver 判为确定答案，**未计为经双 oracle 确认**。Oracle 是 Z3 4.15.4 和 cvc5 1.3.4，报告保留工具及输入的 SHA256。

原 11 个 unknown 已进入仓库回归。其中 10 个数组模型使用 `model-check` 要求所有原始断言确定成立；完整数据类型模型的独立导出校验仍未实现，不能把它与十个数组样例等同处理。

## 性能对照的限制

固定语料从改动前回归记录选择：每个逻辑目录的中位样例和较慢样例，共 48 个。每例 3 轮，baseline/candidate 交替先后运行，各次均为新进程，包含启动和解析开销。报告记录输入、二进制哈希、原始输出、每轮时间及 CPU affinity。服务器并非全机独占。

R5 的 48 对结果全部一致且无 unknown、错误或超时。baseline/candidate 时间比的几何均值为 **0.9591**，按案例 bootstrap 的 95% 区间为 **[0.9280, 0.9853]**；对应本次样本中平均耗时约增加 **4.3%**。它不能支持显著提速的结论，也不代表 SMT-LIB 全语料的性能。

中间 R4 的比值为 0.9403、约慢 6.3%，保留原始记录。较早 R2 对照约为 0.8859，但其中两个多查询输入被工具误分类为执行错误，两版本共记了 12 次错误。该失败记录保留；后续工具比较完整的答案序列。不能将这两个版本的差异直接归为优化收益，因为其代码和部分测试工具也有变化。

## 终验中发现的问题与处理

- R2 原生单测 1525 项中两项失败。一个是历史 gate-off 必须 unknown 的过时预期；另一个是实际 false SAT：组合层生成数据类型字段引理后优先返回其他引理，原义务被丢失。现在 Full-effort 引理先交付，字段引理使用可跨回溯复用的稳定前提。
- R3/R4 的原生回归又发现两项失败：数组常量索引样例已恢复 SAT，旧测试仍期待 unknown；库 API 的 `uflra_012_unsat_fn_arg_pinned.smt2` 则存在实际 false SAT。LRA 曾忽略没有变量名的常量一侧，并用 arrangement 授权状态决定是否处理接口不等式。现已补齐变量/常量的严格不等式分支并移除该门控，直接回归通过；数组样例的两个配置均增加正面模型检查。
- R3 中 seed 1 / case 35 曾从 UNSAT 退化为 unknown。现在构造器数值常量字段不一致时，直接生成带等式解释的冲突；包括任意精度常量的专项通过。
- 查询快照迁移后的初版重复查表导致开销；后续改为透明哈希查找，并仅在要求参数转储时登记读取。性能仍须以最终对照为准。
- 初次 Coq EOS 运行在地址空间限制下因 OCaml 默认 domain 预留失败。设置单 domain 后，编译及独立内核重放成功。保留失败调度记录及成功记录。

## 不应从这些结果推出的结论

有限测试不能证明所有输入均正确。Coq 只证明所列数学规则及 Coq 路径检查函数，未证明 C++ refinement、PA 变换或整个 CDCL(T)。32 个 CNF 骨架也不是原始 SMT 查询的完整理论证明。

406 项命名控制、535 个字面量读取位置已经走统一查询快照；这不等于 406 项都完成了类型化语义整理，也不等于所有历史 gate 已删除。运行时全局信号恢复、其他全局状态及 CLI/库配置差异仍需后续处理。完整 PA 的证书和模型重建、完整分离逻辑及各语言的程序验证语义仍未完成。功能契约见 [IMPLEMENTATION.md](IMPLEMENTATION.md)。

## 版本与来源

最终 CLI SHA256：`411ad5f69cc26d87ab51428f55a348d00a5dd304203d8a417cf1bf75d21596b9`。单测 SHA256：`9b1a9586a2032255e98e341076911aeda5af71a2f73832b3083c221331eb75f0`。

R5 对应 R20 源码清单；服务器逐文件验证 234 项，哈希全部一致。PA 300 例使用冻结 R4 CLI（`8a8c1da191a030031ba1a4eab648ee2e79077e1b6b5428926eb023ce6ce30b28`）；PA 的两个实现文件和 `Solver_impl_checksat.cpp` 在 R4/R5 间均未变化，R5 还通过公共 CLI 功能测试。此处没有把 R4 的完整原生测试失败掩盖为 R5 通过。

`Presburger.cpp` 哈希为 `99de7065de13e84ae6fb5713da55a8a65e3430dc6603a01e332817088802ce9e`。Coq 证明源码哈希为 `c263d88174a8a635ac0e1122dd157cfda99ede0fef207a938f3f496c3f7e2705`。第一轮 `evidence/server/` 和 `final-source.json` 保持原样。

最终 Python 扩展 SHA256：`b47b1b29bff94692f053cddf0d02a5582574c613ed27c30173784a738a3b699d`。

| ExperimentOS 实验 | ID |
|---|---|
| `xolver-audit-implementation-r5` | `c715561908d3` |
| `xolver-audit-combination-implementation-r5` | `b262a885ac57` |
| `xolver-audit-python-implementation-r5` | `a577b2676594` |
| `xolver-audit-proofs-implementation-r5` | `5ddad951264b` |
| `xolver-audit-models-implementation-r5` | `165b29c2940b` |
| `xolver-audit-performance-implementation-r5` | `5b61bb88d172` |
| `xolver-audit-presburger-implementation-r4` | `fbd303c15c88` |
| `xolver-audit-formal-kernels-r3` | `8cea84d67fb4` |

[原生退出状态](evidence/implementation-server/implementation-r5/metrics.json)、[完整单测日志](evidence/implementation-server/implementation-r5/unit.log.txt)、[逐例回归](evidence/implementation-server/implementation-r5/regression.json)、[最终性能对照](evidence/implementation-server/performance-implementation-r5/report.json)、[数组模型检查](evidence/implementation-server/models-implementation-r5/report.json)、[PA 全输入与记录](evidence/implementation-server/pa-implementation-r4/report.json)和[Coq 内核检查](evidence/implementation-server/formal-r3/metrics.json)均归档。

[归档清单](evidence/implementation-server-manifest.json)包含每个记录的哈希；[R20 受测源码清单](evidence/implementation-sources/implementation-r20-source.tar.json)及[服务器逐文件核对](evidence/implementation-server/source-r20-check.json)绑定最终受测代码。后续文档整理不改变这些代码。

完整源码覆盖包清单见 [implementation-final-source.json](evidence/implementation-final-source.json)。对应源文件归档保留在项目 `build/implementation-final-source.tar.gz`（D: 上）；它不包含另一棵编译树。重放需要基线修订、相同子模块修订及该覆盖包。代码冻结后仅整理文档，另有 [冻结后代码核对](evidence/implementation-code-stability.json)记录。
