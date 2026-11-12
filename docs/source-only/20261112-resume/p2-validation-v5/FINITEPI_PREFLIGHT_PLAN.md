# P2 r4 前置 FinitePi 严格审计方案

**建议在同一 GitHub job 内、原 102 项 build 之前，先构建并审计单个 ImbalancedChen.FinitePiIntegral。** 这个前置步骤的用途是及早获得原严格清单比较的真实结果，成功仅放行后续 102 项流程。当前是静态方案，尚无该探针的运行结果。

## 原失败和可复用输入

P4 运行 43108198136 对 146 个模块完成 kernel 重放，随后完整归属名录和序列化名录在 FinitePiIntegral 上不相等。旧日志没有打印冲突名，旧 ZIP 只留对象摘要。P2 r3 运行 43186809155、job 131075895931、头 dfda53cc0d9eceeb413a7f0c1ef5045ddd35c206 在真实日志第 1365 行完成同一 FinitePiIntegral 单元的构建。第 12 步因另四个模块失败，第 13、14 步跳过。五个 r3 修复单元均有 Built 记录。日志 241375 字节，SHA-256 e106227d45c388fc7fff8b3090c22dbc79d680dcfbab8123d2471ccc9086951e。

两个流程的目标源均为 3270 字节，SHA-256 22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c，Git blob 3f768c8c12dba787dd716f7b8854813f8eb094d9。P2 原始文件来自 eb035a259f2f40853e9899f6d98af25852184fee 的 ImbalancedChen/FinitePiIntegral.lean。它直接导入 Mathlib.MeasureTheory.Constructions.Pi 和 Mathlib.MeasureTheory.Integral.Prod，无其他项目模块直引。现有双类型与归属诊断模板 SHA-256 为 46eedd90437fae00921f2a5a6a39abb5996125f45033b230c17d1403d16eec95。

## 最小流程差量

1. 先完成现有 source/config/manifest 绑定、相同工具链、原 12 GiB trust-zero 串行 guard、固定外部依赖缓存和完整 102 导入图准备。沿用现有 prepare 对 Round6Audit 的处理，提取同一个按有序模块表生成 exporter 的函数。用完整 modules 生成现有 CandidateAudit.lean，除 r4 数学来源外，完整审计源码与原版渲染结果逐字节对照。再用单元素列表生成独立 FinitePiPilot.lean。它只导入 ImbalancedChen.FinitePiIntegral 和 Lean.Util.CollectAxioms，modules 数组也仅含前者，同样删除不属于 P2 的 finalBridge 特殊分支。保留整个诊断、类型导出、所有原拒绝条件和结尾计数。可将 pilot 放在项目根并复制到 LOGS，保留两份 exporter 与各自 SHA。
2. 使用原项目与原环境，在新步骤内依序以原 target 拼法执行 `lake build ImbalancedChen.FinitePiIntegral` 和 `lake env lean -DwarningAsError=true FinitePiPilot.lean`。两次各留独立 stdout/stderr 原日志，用 set -euo pipefail 贯穿 tee。对实际模块 olean 记录构建后、pilot 后 SHA 并检查相等。复用同 job 的真实 .lake/build 与 Lake 依赖 trace 给后续完整构建。保留完整 102 的后置编译/重放清单。
3. 前置成功须解析这一份独立日志。要求恰一条对应的 SERIALIZED、非空精确含重数的清单、每个名称恰一条 DECL、同一所属模块、等数量完整双类型与 collectAxioms，仅 propext/Classical.choice/Quot.sound，原 unsafe/partial/axiom 拒绝与 MODULE/COUNT 一致。记录实际源、对象、模板、生成的 pilot、完整日志 SHA、run/job/head 和结果。失败时原审计器在 throw 前刷新 P0_ROUND6_INVENTORY_MISMATCH，保留完整两侧、差异重数、canonical owner/index 与在加载模块中的出现位置。解析器或退出状态失败都中止全 build，原 always runtime/retain/upload 仍收齐日志和已存在对象。
4. 前置通过后执行原完整 102 项 build/snapshot、102 项 leanchecker 精确 census、完整 CandidateAudit、after 与 before 源及对象快照一致、实际运行守卫、归档及原 final acceptance。完整审计仍含 FinitePiIntegral。导入全局的首次归属可随已导入模块及顺序而变，单元环境通过不能预测 P4 的 146 模块环境，也不能代替 P2 的 102 模块环境。两环境若结论不同，以完整环境中原严格门及差异日志裁决。此方案没有单独的 Y18 或全 P2 验收。

真实 R3 归档服务端记录为 artifact 13934007506，1906971086 字节，SHA-256 52cc7470415283c388efe76da1f593464675be06825ecd7c1f766ec1a77f3ddd。本次未下载这份大包。原 retain 归档 sources、实际存在的 .olean* 及各模块 lib/lean 同名 facets。失败发生于正式 snapshot 前，尚无完整前后比对或全量验收。跨 run 恢复仍须对确实存在的每个文件、实际 imports/setup、配置/工具链/ABI、依赖和编译命令独立绑定；当前核定可恢复对象数为零。前置步骤可直接复用已锁定的官方依赖缓存。

## r3 首错的来源

首错位于 P4AOriginalRange32MassCeil.lean 第 137 行。eb035a25 的 ActualThirdOriginalSymmetricJensenLeaf.lean 第 253 行定义 OriginalThirdTriangleMomentsSourceOnly.prismMass，第 523 行定义 OriginalThirdSortedHalfIntegralSourceOnly.SymmetricFullBox，均在 ImbalancedChen 下。symmetric_mass_formula 所在 namespace 局部 open 这两处，调用方不能藉此解析两个裸名。恢复这两个已有常量的可见性不增加前提，旧声明头没有成功 elaboration，审查应区分文本头不变和恢复原意。其余三个模块的准确诊断分别在原日志 1915–1951、1954–1981、2099–2260 行。现场记录没有触发清单比较，不能用这些失败猜测任何 FinitePi 冲突名。
