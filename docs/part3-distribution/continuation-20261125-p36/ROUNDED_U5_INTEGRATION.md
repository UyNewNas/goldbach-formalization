# Rounded U5 源码接入

状态：**源码已安装，待实际编译与完整验收**。本记录不给新模块登记绿色，也不改变已验收的原 literal rho 三模块的范围。

本次将固定提交 `92a7e0062be2d180a92ecbcda7368b77a82f506c` 中已独立审查的 rounded reuse 包安装到 canonical 路径，并接入已审查的 beta 误差候选。三个新编译入口为：

| 入口 | 本次源码结论 |
| --- | --- |
| `P3OriginalU5RoundedCountInsertion` | 同一个 rounded rho 的原 pair 计数入口、exact coprime numerator 和 signed discrepancy/centre 分解 |
| `P3OriginalU5RoundedModulusCap` | 原 U5 实际 raw support 导出的 level/rank，以及先于 N 和所有 pair 的统一正网格，使完整 rounded 模数小于 `N^(599/1000)` |
| `P3OriginalU5RoundedBetaReserve` | 实际 rounded 绝对质量由完整 residual mass 控制，随后支付同一系数的小 beta attachment 误差 |

## 已有工作的复用

P15 固定提交 `c6b89774822580c731a236ac66dcd7466ac8a0e6` 已包含 finite-cell rounding、beta compiler 和 canonical retained trace 的兼容修复；本次按原字节接入三份源文件。完整 residual universe mass 也直接复用该提交的原文件。

旧 U6 joint ledger 中的 quotient 定理实际上适用于任意外乘数。已将它原字节抽取到 `P2RoundedQuotientMinorant`，并让 U5 count 入口调用它，不再安装旧冻结候选中重复写出的有限求和证明。旧 mixed-fibre/physical-level 文件的前十三条声明抽取到 `P2RoundedFibreCore`，只保留八处已诊断的 `universe` 标识符 quoting；逆变换可恢复旧字节。

两份 full compatibility 文件保留其旧 namespace 入口，通过新模块导入已移出的声明；它们不属于此次选中闭包。抽取后声明的 defining module 已改变，后续审计必须按实际 owner 清单检查，不能用旧 namespace 前缀代替。

## 安装检查

安装后重新解析实际 canonical 文件。选中源文件由 264 增至 274，目标入口由 8 增至 11，兼容文件由 5 增至 7。原 264 份选中源文件哈希全部保持；没有覆盖已存在的 canonical Lean 文件。117 个外部 imports 保持原集合，没有新增缺失依赖或循环。

本次未改编译 runner、kernel replay、完整声明审计或缓存校验程序。源码哈希、固定 Git blob、旧阶段记录和独立审查绑定见 `ROUNDED_U5_INTEGRATION.json`、`SOURCE_SELECTION.json` 及 frozen source packet。

旧 P15 的 normal compile/replay 记录保持其原阶段范围。后续只有在源码、工具、依赖闭包、对象和完整 sidecars 的实际绑定满足条件时，才可复用对象；旧日志不自动成为本轮 owned 模块的完整验收。

## 未完成边界

三个新入口没有将 literal rho 与 rounded rho 识别为相同对象，也没有假设 rounding loss 很小。实际 mixed warm fibre 的有限墙覆盖、全 residual 求和后的 box error、raw density 的具体求值、whole-word tensor、common physical Q、family admission 和最终 PP 仍需继续完成。整个 P3.6 保持开放。
