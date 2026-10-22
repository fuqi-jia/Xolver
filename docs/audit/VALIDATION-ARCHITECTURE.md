# 分层重构与原生 DAG 入口的服务器验证

所有 C++ 编译、求解、差分、模型检查和性能测量均在 Panda1
`/pub/data/jiafq/xolver`，通过 ExperimentOS 执行。复用唯一增量 `build/`
并对写入加锁；WSL 仅做源码编辑、静态检查、打包和证据核验。

架构决定、已实现范围与剩余迁移见 [RESTRUCTURING.md](RESTRUCTURING.md)。
本报告区分 R7、R8 和最终 R9，失败记录不删除，不把中间版本测试冒充为最终测试。

## 最终 R9

| 检查 | 结果 |
|---|---|
| 新增关键用例预检 | 7/7，92 个断言；覆盖绑定、原生入口、模型重建、定义替换和类型化控制 |
| 完整原生单测 | 1535/1535，513090 个断言；0 失败、0 跳过 |
| 文件回归 | 820/820；串行、每例 240 秒上限 |
| CLI / 工具 | 36/36；原子覆盖工具另行 2/2 通过（共 38 项） |
| 已登记 known gap | 1 项仍为 unknown（KNOWN_FAIL），不是已解决 |
| 独立证据检查器 | 通过；接受正确 SL 模型/冲突与整数反证，拒绝篡改 |
| Python | 30/30 通过 |
| PA 自由变量模型专项 | 120/120 结论与 Z3、cvc5 一致；73 个 SAT 模型全部经两个 oracle 验证 |
| 组合差分 | 600 例，581 个确定答案一致，19 unknown；无错误结论、崩溃、超时或 oracle 跳过 |
| PA 300 例差分 | 290 例双 oracle 一致：270 个确定答案匹配、20 unknown；另 10 例 oracle 未共同给出确定答案 |
| 证明语料 | 46 例：5 个完整 CNF 反证、32 个骨架、9 个未生成证明；0 拒绝、0 执行错误 |

模型专项包含负数、任意精度整数、同名绑定恢复、同余、自由布尔符号、耦合自由变量
和量词交替。每个 SAT 模型的自由变量赋值都被作为额外等式加入**原始含量词公式**，
再交给 Z3 和 cvc5。120 例中无 unknown、模型跳过或坏模型。全部原始输入、模型输出、
固定赋值后的查询及工具哈希保留在 `pa-models-architecture-r9/`。

PA 300 例中，双 oracle 一致部分为 167 SAT、103 UNSAT、20 unknown；其余 10 例为 5 SAT、3 UNSAT、2 unknown。后者的 8 个确定答案没有计为经双 oracle 确认，总 unknown 为 22。

组合差分沿用种子 1、17、43、79、101、20261020，各 100 例；
unknown 数分别为 0、1、4、2、2、10。不能把未观察到错误答案说成全局正确性证明。

独立检查程序的实际链接命令只包含 `libxolver_checkers.a`、gmpxx、MPFR 和 GMP，
未链接 SOMTParser、CaDiCaL 或搜索实现。其构建依赖也不再要求构建这些后端。
链接命令见 `architecture-r9/checker-link.txt`。

## 性能

与上一轮冻结的 `implementation-r5/xolver` 比较，同一组 48 个原有回归样例、
每例 3 轮、交替执行顺序、每次启动新进程。48 对结果均一致，没有 unknown、
错误或超时。

baseline/candidate 耗时比的几何均值为 **1.000824**，按案例 bootstrap 的 95%
区间为 **[0.998200, 1.003536]**。本样本基本持平，**不能支持显著提速**。
它主要衡量原有 QF 路径，不能据此推断原生 PA 的大公式内存收益；服务器也并非全机独占。

## 中间失败及修复

- 分层编译暴露原来由传递包含提供的 `<functional>` 和模型类型依赖，
  以及 SL 辅助函数从求解器移到检查器后漏改的调用。
- 新用例的 Result 枚举需避免 doctest 的 ADL 字符串化冲突；
  PA 模型接入改用项目实际提供的 `RealValue::fromMpq` 工厂。
- 独立 checker 的 GMP 头文件传播不完整；解除公共后端链接后，
  静态 MPFR/GMP 的链接顺序需要显式调整。这些失败保留在 R1–R6 编译记录中。
- R7 原生单测 1535 项中 1534 通过，1 项失败、2 个断言失败。
  失败的新增测试按下标假定 AND 和等式子项顺序；改为按节点种类定位，
  并检查内层引用及恢复后的外层绑定身份。最终预检已通过，未删除相应语义检查。
- R8 补齐原生特征字段并统一两种读取器的检测规则。使用旧测试的重复任务已主动取消，
  记录为取消，不能算作通过。

R7 在完成文件回归后，验证脚本因运行中被原地覆盖而遇到 shell EOF 错误；该运行没有 CLI/工具终验结果。部署工具现改为原子替换文件，保持已打开脚本的旧 inode 可读，并加入打开文件描述符与前像篡改拒绝测试。R9 执行期间没有改写其验证脚本。

R7 的 PA 模型、600 例组合差分和证明语料结果与本轮已完成的 R9 对应检查一致。
R7 性能比为 0.999020、区间 [0.985653, 1.013003]，也不支持显著提速。

## 版本与来源

基线仍为 `e927757f5a033e244e96d7d41234866fb783d038`。
SOMTParser 基线为 `acdc6a0981b0e6612ed9cba70b16c80c7eb2c9df`，
本轮在其工作树修改 4 个文件，不能只用 gitlink 修订表示最终源码。
最终源码清单记录每个补丁文件的 SHA256 和各子模块基线。

R9 CLI SHA256：
`db34a2df24ae4883bb50a89e17a822a1c2a37993adf4cc26ed926d97805c8bef`。
Python 扩展 SHA256：
`0d66f66a5973d307c3055649a9e1cb61801bebf69c4b6d6b061d7d475c542fd3`。
R9 单测 SHA256：
`ce2a95cbe46766f59c25fa11cb875e043686b1e4045287d0c59eb12d5f5e891a`。
独立检查程序 SHA256：
`071012bd0a9178ffd62f6c345704f06afe448d5645112320065f215c9c9da1d8`。

| ExperimentOS 实验 | ID |
|---|---|
| `xolver-architecture-r9` | `713218a60087` |
| `xolver-audit-presburger-architecture-r9` | `f73aac79da45` |
| `xolver-audit-presburger-models-architecture-r9` | `c13596b06287` |
| `xolver-audit-combination-architecture-r9` | `93669b045800` |
| `xolver-audit-performance-architecture-r9` | `50af93329216` |
| `xolver-python-architecture-r9` | `4c77b9f1dd34` |
| `xolver-proofs-architecture-r9` | `4d4bb4a16080` |
| `xolver-overlay-architecture-r9` | `d84eaa22efa6` |

本轮 491 个源文件及 2 个说明文件的迁移前路径、目标路径和原 SHA256
见 `architecture-migration.json`。迁移在删除旧路径之前逐一验证并保存服务器
preimage 档案；没有复制或另建完整构建树，也没有覆盖前两轮证据。

## 可复核材料

- [最终源码及子模块补丁清单](evidence/architecture-final-source.json)。
- [服务器逐文件核对](evidence/architecture-server/architecture-source-check.json)，同时核对最终编译输入与 R9 快照一致。
- [证据档案 SHA256 清单](evidence/architecture-server-manifest.json)，包括中间失败与取消记录。
- [最终完整验证指标](evidence/architecture-server/architecture-r9/metrics.json)、[单测日志](evidence/architecture-server/architecture-r9/unit.log.txt)、[回归报告](evidence/architecture-server/architecture-r9/regression.json)。
- [PA 模型专项](evidence/architecture-server/pa-models-architecture-r9/report.json)、[PA 决策差分](evidence/architecture-server/pa-architecture-r9/report.json)、[性能原始记录](evidence/architecture-server/performance-architecture-r9/report.json)。

## 仍未完成

CoreIr 还服务于旧 QF 理论和兼容 API；408 个控制项中仍有 61 个 Text 解析待领域化。
PA 已新增自由变量模型重建，但量词消元证书、独立量词模型检查器仍未实现。
有限符号堆不等于完整 SL，归纳谓词和一般蕴含未完成。已有 Coq 数学规则未证明
C++ 实现和端到端求解流程，32 个证明骨架也不属于完整 SMT 证明。
