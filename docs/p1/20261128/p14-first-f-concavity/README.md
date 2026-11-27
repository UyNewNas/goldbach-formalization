# P1.4：原 firstF/Q 局部微积分已验收

`P5OldFifthFirstFConcavity` 已从源提交 `4a396d6` 的实际编译失败继续完成。原 firstF 在闭区间 `[2,4]` 上的凹性与单调性均已证明；对 `2≤b≤4`，原 Q 在 `[0,b−2]` 上凸且单调。最终 `frozenUpperPositiveKernel_ge_Q_no_calculus_input` 直接使用已证凹性，消除调用方此前必须额外提供的 calculus 前提，保留原 `2<b≤4`、五坐标严格为正及实际新 residual 的条件。

三处导数证明把目标显式写为原函数，再调用原 `HasDerivAt.congr_deriv`，避免 `convert` 留下额外函数等式。原导数公式、对数上界、曲率证明和闭区间端点不变。另显式选中原 `P5OldFifthPointwiseQ.Point` 与原 `P1OriginalFifthRawBoxSelectorEquivalence.rawCandidate`，并闭合 `1∈Ici 1`。这些是原证明的表达/命名空间修复，没有把待证界改成假设。原 CRLF 完整保留。

## 验收范围

`formal-00001`：normal **9.256196 秒**、精确新模块 kernel **10.154226 秒**、完整 owned 类型/表达式/宇宙/公理审计 **7.974154 秒**，均退出 0。共 **24 个 owned 声明，0 个私有声明**，包含全部生成声明。仅依赖 `Classical.choice`、`Quot.sound`、`propext`。

原 PointwiseQ 的 23 声明验收、源文件、五项输出及两份日志共九项输入指纹前后一致，旧模块 normal/kernel 次数为零。冻结 Member guard/core、Lean/Mathlib 依赖及资源参数不变。验证只写隔离输出，没有改写活动 Member 缓存。采用 guarded direct Lean，不声称 Lake named-target 或全导入闭包重放。泛用驱动回执内的 `whole_P1_5_complete:false` 是继承的通用限制字段；本轮实际模块和复用清单明确属于 P1.4，完整 P1.4 同样未闭合。

原 source4a 失败日志、原源码及 `formal-00000` 失败快照全部保留。`formal-00000` 已闭合三个导数目标，仍暴露 Ici 的简单比较和 rawCandidate 的命名空间问题；下一次只补齐这两处。打包门在缺少独立复核时按预期拒绝归档。独立只读复核无阻断，没有运行 Lean/kernel 或改写源码。原源码内 source-only 注释保持为历史字节；正式验收以本回执和已冻结快照为准。

**完整 P1.4 仍开放。** Key 的新纯函数查回草稿、完整 stored-parent max/floor、后续 endpoint 和 reserve 连接都未由本轮证明。没有重新全表排序。P1.5 也保持开放，原 ProperPower 登记 18/21 未改。

[验收](ACCEPTANCE.json) · [独立复核](INDEPENDENT_REVIEW.json) · [证据包](p14-first-f-concavity-evidence.zip)

归档：580950 bytes，46 个成员，SHA-256：`1ca7ea30fd8cc1caeff5793fc6cde843d6f7e2d10ace032403188df02cf284e1`。CRC 与每个索引成员已复核。
