# AG 真实两次结果已绑定；collector 待实际返回

**原 21 个 formal targets 已实际接受 18 个。** AG manifest 保留的 16 个历史 prior，加上 ReserveBranches 与 AtlasRoughPrime 两个本轮首次接受 owner。三个 proper-power target 仍为 P3 HOLD，整体 P1/P1.5 未闭合。

| 原接受 owner | 接受任务 / run | owned/public | audit |
| --- | --- | --- | --- |
| ReserveBranches | `job_83532ebe8bdd423caa1a7610aac08ae7` / attempt-00000 | 13/13 | `3c62877f43ddf925ee34` |
| AtlasRoughPrime | `job_0ff7bb5706c04f94a026aee1a0d5a316` / attempt-00001 | 6/6 | `bde2141e3b95bd7e5707` |

两次任务均 exit 0，normal/kernel/full-owned/standard-only 及 final stock 成功。Later2 只复用 ReserveBranches 的原接受 binding，首次接受 AtlasRoughPrime；没有失败或未启动目标。两份 raw RESULT 已从本地 capture 去除包装字段后按原格式复原，字节数/SHA256 均逐一命中 actual metadata；对应 WORKER 的重建指纹也匹配。

`ACTUAL_INPUTS.precollector.json` 已绑定这两次原始结果、实际 task status、metadata 和来源包装。`LATER2_TASK.json` 的原始 `{status, submit}` 包装完整保留；提取的 status 只用于兼容本地生成器输入，原文件及 JSON selector 也一并固定。

**实际 collector、READ 与 public 摘要仍未绑定；最终生成器未运行。** 输入 state 仍为 HOLD 状态；只有真实 collector 完成后才可建立最终输入并生成最终 ledger。此前 `FRAMEWORK_STATE.json` 的 17/21 以及 AE 的两份冻结快照均保留原字节。

三个 proper-power / 19 项 P3 read-only device HOLD、FixedM 原字节缺失、literal historical medium 的同源字典及 full signed bound 缺口、`hSmoothSignedPP` premise 均保持。Residual、outer payment、AD 算术修正仍为 SOURCE ONLY。TrimLogAccuracy 新独立 probe 仅处于准备阶段，没有接受记录，也不计入原 21 targets。
