# 服务器验证记录

本文件保留第一轮的版本与结果。后续 PA、符号堆求解、配置迁移和扩展差分测试见 [第二轮验证记录](VALIDATION-IMPLEMENTATION.md)；请勿把本页的 11 例 unknown 和早期二进制当作最新状态。

执行位置是 Panda1 的 `/pub/data/jiafq/xolver`，最终测试由 ExperimentOS 调度。每个 checkout 只使用 `build/` 这一棵增量构建目录，写入由 `build/.writer.lock` 串行化；测试使用带 SHA256 的冻结二进制，构建锁随后释放。WSL 仅用于阅读、编辑、打包、Python AST / shell 语法检查及 Git 检查，没有在本地运行本轮求解测试或编译。

源码基线和子模块修订见 [baseline-provenance.json](evidence/baseline-provenance.json)，最终改动见 [final-source.json](evidence/final-source.json)。服务器逐文件核对了 83 个改动后的代码、测试和工具文件，与本地哈希全部一致。结果日志、逐例回归报告、证明产物和 ExperimentOS 记录保存在 `evidence/server/`；[归档清单](evidence/server-manifest.json)记录每个文件的 SHA256。最终验证的[单元测试日志](evidence/server/config-plan/unit.log.txt)、[逐例回归报告](evidence/server/config-plan/regression.json)和[退出状态](evidence/server/config-plan/metrics.json)可直接复查。

## 原始版本

基线源码为 `e927757f5a033e244e96d7d41234866fb783d038`，Release、proofs=ON，GCC 15.2。前置编译遇到 GMP 开发包搜索路径、CMake 4 旧 policy、GCC 15 缺少 SIZE_MAX 声明，以及静态依赖链接顺序问题；基线使用显式依赖路径、`-include cstdint` 和系统 GMP/MPFR 动态库，保留原项目及子模块源码。

| 检查 | 原始版本结果 |
|---|---|
| 单元测试 | 1492 通过，0 失败，3 跳过；500173 条断言通过 |
| 仓库回归 | 804 PASS / 808，4 TIMEOUT；每例 60 秒，4 worker 共享一个分配核 |
| CLI SHA256 | `ebac1749af42e1c2567a8a0497e0fc63cc1378a17e3b91f5dfeaf4e21387dbe3` |
| 单测 SHA256 | `063cc1eb3e6c3ff8028314f46bb24575b50e90f4753d46fda7ff67c196acf4e7` |

基线调度入口 `xolver-audit-e927757f-baseline`（`6c491f73900a`）的初次条目记录的是前置失败；上述完整结果以服务器重放日志 `baseline/` 为准，不能将初次调度失败读成通过。编译最终在服务器以低优先级、最多 8 个任务执行，避免把整次编译限制在一个分配核。

## 修复版结果与版本边界

以下各阶段保留各自二进制与日志。不能把某个较早二进制的结果未经说明归给后续版本。

| 阶段 | 结果 | 记录 |
|---|---|---|
| 原始修复版、相同 60s/4 worker 回归条件 | 单测 1514/1514、512307 条断言；804 PASS、4 TIMEOUT | `candidate/` |
| 证明崩溃与 stdout 修复后的完整验证 | 单测 1514/1514，0 跳过；808/808 回归通过；22/22 CLI/工具测试通过；已知缺口 1 项仍为 unknown | `final/`，EOS `f6bebd9fe559` |
| 类型化 portfolio 配置后的最终完整验证 | 单测 1516/1516、512331 条断言、0 跳过；808/808 回归、22/22 CLI/工具测试通过；已知缺口 1 项仍为 unknown | `config-plan/`，EOS `ce2c4d2d0d42` |
| Python 3.12 / pybind11 2.13.6 | 证明修复版与最终配置版均为 29/29 通过 | `python-before-config-plan/`、`python/`，最终 EOS `b5eb3defdf12` |
| 两个 oracle 的差分检查 | 200 个输入均获 oracle 一致结论；189 个确定答案一致、11 个 unknown；0 错误答案、0 崩溃、0 超时、0 oracle 跳过 | EOS `9950684ff809` |
| 46 例 UNSAT 证明语料 | 5 CNF 反证通过、32 骨架通过、9 未生成证明；0 checker 拒绝、0 执行错误 | `proofs/`，EOS `67f95c000ea6` |

最终完整回归按分配的单核串行运行，每例 240 秒；这与 60s/4 worker 的旧条件不同，不能据此宣称性能提升。证明修复版 CLI 哈希为 `9b9eb296762ef6bbedaf54001f9e6d8bd4cf38b9b32e237b27a42b57f3e4439b`。最终 portfolio 配置版 CLI 哈希为 `c91013eba0ff6ff2f98ff16ae56f9715e4ad735e4b3160ec51b521aaef9a3483`，单测哈希为 `32dccccedb6fbaef003952bf4c0ea9b0d1b036adf4aa3fba7cb08e2aa0e3832f`。

差分检查使用种子 1、17，各生成 100 例，覆盖 LIA/LRA 与 UF/数组/数据类型的组合。Oracle 是 Z3 4.15.4 和 cvc5 1.3.4（f3b21c4）；种子 1 有 7 个 unknown，种子 17 有 4 个。11 个输入及 oracle 结论均保留在 `fuzz-final-cases/`，没有把 unknown 当作已解决。该组和证明语料使用证明修复版二进制；之后的配置改动另有完整回归、配置边界测试和 Python 复验。

## 四个原超时案例的对照

每例独占分配核、240 秒上限，基线和修复版均通过。此对照使用 `candidate/` 冻结二进制，早于后续证明导出及配置清理。

| NRA 案例 | 基线秒数 | 修复版秒数 |
|---|---:|---:|
| nra_150_sat_melquiond2_hashcons_stress | 27.582 | 26.328 |
| nra_154_sat_kissing_4_4 | 0.1285 | 0.1444 |
| nra_197_sat_metitarski_sqrt-problem-Melquiond2- | 27.555 | 26.522 |
| nra_200_sat_metitarski_polypaver-bench-sqrt-3d- | 39.493 | 38.301 |

ExperimentOS `3395b93d41dd` 报告几何平均加速比约 1.00，95% 区间约 [0.92, 1.04]。仅四对样本，没有建立显著加速结论；本轮主要收益是正确性、状态隔离、证据边界和可维护性。

## 验证发现并修复的问题

- **增量构建误用旧对象。** 首个候选运行混用了旧对象，单测 4 项失败、工具 1 项失败，结果保留在 `candidate-initial/`。原因是打包保留的源码时间早于基线对象；现于构建锁内用 `tar --touch` 应用改动，再复用原 build 重建。
- **Assumptions 丢失。** eager NIA 候选搜索看到了 guarded 公式，却没有激活 indicator；补齐激活条件后，`x*x=2` 的 assumption 不再被错误判为 SAT。
- **多查询错误上下文。** 新快照回放依次执行各查询，避免用最终断言回答较早查询；假设不会泄漏。它是重新解析快照的正确性后备，尚未共享查询间搜索状态。
- **证明导出越界。** 4 个数组/UF 组合样例在原始版也会 exit 139；无 IR 来源的合成原子进入证书。生成端与重建端现在都检查范围，整份拒绝不支持证书；不会删除单个前提来拼出貌似完整的证明。
- **证据读取错误。** drat-trim 的 CR 前缀曾让 33 个合法输出被误判拒绝；现在正确处理行首空白并拒绝 `VERIFIEDgarbage`。CaDiCaL 的 `c ...` 文件日志也不再污染 SMT-LIB stdout。
- **原测试 oracle 不确定。** `nra_180_sat_geogebra_compositum.smt2` 原 `:status unknown` 曾被旧回归器宽松放行。Z3 得到 SAT，cvc5 在 30 秒内未完成；另构造 Q(sqrt(2),sqrt(5)) 中的精确见证，独立检查 7 个等式和 7 个严格正性约束。项目副本现标为 SAT；脚本见 [check_nra180_witness.py](evidence/check_nra180_witness.py)。共享原始数据集归档未修改。
- **策略配置边界。** `atoi/atol` 可产生溢出或尾随垃圾解析；现统一为受检整数读取，查询入口快照后纯函数构造计划。移除测试复制臂开关、无行为的空逻辑分支及误称测试已证明重入健全性的历史注释。

为固定最终 stdout 修复，中途停止过一次尚未完成的完整验证，其部分记录保留在 `final-before-outputfix/`；它不计入任何通过数量。早期失败和中止记录没有被覆盖成成功。

## 证据强度及未完成项目

DRAT checker 源码固定在 `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`；GCC 15 构建显式启用 `_DEFAULT_SOURCE`。合法反证接受、SAT 公式的伪反证拒绝已做冒烟检查。5 个 CNF 反证通过只证明提供给 checker 的 CNF 不可满足；原始 SMT 文本到 CNF 的转换仍属可信边界。32 个骨架还把理论 lemma 当作公理。没有运行 Carcara，不声称这些 Alethe 产物已经外部核验。

本轮没有完成证明助手中的形式化证明、全量 SMT-LIB 2025 扫描、ASan/UBSan 全仓库运行或独立 wheel 发布测试。Python 测的是服务器实际编译的扩展。完整 PA 消量词、SL 空间推理与归纳谓词仍未实现；新增内核仅覆盖已声明的整数证书规则和有限具体堆见证。

本次测试证明的是列出的输入和边界用例通过，不能证明仓库不存在其他 bug。运行控制项清单、未迁移的全局配置和后续验收条件见 [ARCHITECTURE.md](ARCHITECTURE.md)。

## 复现

服务器先运行 `bash tools/remote/build.sh <改动源码包>`，再用 `docs/audit/experiment-*.yaml` 提交相应 ExperimentOS 实验。Python 重建使用 `bash tools/remote/build_python.sh`，仍复用同一个 build 目录。各验证目录只冻结必需的二进制，不复制构建树。

收集日志和产物：`python3 tools/remote/collect_evidence.py --eos-db /pub/data/jiafq/eos/eos.db`。收集器只读 ExperimentOS 数据库，排除二进制和 build，产生逐文件哈希清单；历史原始日志始终留在服务器。
