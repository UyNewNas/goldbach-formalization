# P1 固定源码交接：70ad4d7

定向核对完成于 2026-10-12T05:25:09.326669+00:00。本次接收的是**已经远端固定、尚未编译的实际源码 checkpoint**，包含四个生产 Lean 模块。

完整提交：`70ad4d737a2ff4a77413a5975af2fb41bdfb7d66`。Tree：`d287e728ca8d5825455728065ef60122dc6cf56a`。唯一父提交为共同证明基线 `1a80c1bcce67886f699d097fc37fd245cd3620bf`。

## 独立核对结果

本地 git show/ls-tree 与 GitHub 同 SHA commit/tree 一致；完整远端 tree 没有截断，312 个 blob 路径/模式/对象均与本地固定 tree 相同。共同基线的 303 个 blob 全部未变，新增9个P1所有文件。四个生产源和 HANDOFF 的远端内容均与本地固定对象逐字相同，重新计算的 Git blob SHA1 与 SHA256 均吻合。

四生产文件也与04:43:19 UTC冻结候选逐字相同，故本次新增的是正式供货身份，证明状态没有因此升级。公共根导入没有修改；仓库内的 INTEGRATION.patch 仍是待 P0 处理的建议补丁。

| 生产模块 | Git blob SHA1 | SHA256 |
|---|---|---|
| `ImbalancedChen.ActualSelectedPrefixLowerCellSum` | `64e73f036cd309512ea5513377cb0528e65ed524` | `48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714` |
| `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` | `6a535380f1bb4074e06ff8ce4180eaae63d2e9fe` | `c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1` |
| `ImbalancedChen.HistoricalPrefixCertificate` | `7507cc1734d4f8ef5c7653f4c7bf46d8e7fc668a` | `347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1` |
| `ImbalancedChen.OrdinaryLowerFourFrontier` | `05f0e3758e0b6fa0cfa6b3002e9c61ce164489ae` | `97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8` |

其他5个新增文件：`verification/parts/p1/HANDOFF.md`、`INTEGRATION.patch`、`LevelCheckProbe.lean`、`Part1HistoryAudit.lean`、`check.sh`。

## 验证边界

提交信息和固定 HANDOFF 明确标识 SOURCE_ONLY_NOT_COMPILED。四个生产模块及两个独立检查模块的严格编译、原版内核重放、公理审计均仍待实际回执。提交自述的静态检查不在本次被改称 Lean 验证，也没有被重跑。

本次只读复用既有 ledger-final 的2026-10-12 05:20:16.208188 UTC观测：P1依赖闭包547/688，四生产目标完成记录为空。没有重读运行时闭包或干预构建。

保存了 52 个源码 theorem/lemma 声明头；它们明确标为源码提取，编译器确认类型数为0。

## 仍未闭合的输入

- **P1**：Subsequent strict target compilation, original kernel replay and all-declaration axiom census for all four production targets plus two standalone verification targets; current dependency successes do not replace these gates.
- **P1**：The separately reported independently compiled inherited-fifth integral real source remains source pending. Joint historical fifth Tendsto, sixth/eighth layers, full adopted policies, truncation and compiler composition remain open.
- **P2/P1**：Instantiate adopted historical tables/common refinement; prove D.a ≤ D.b and D.levelCheck = true, and independent square/envelope licenses bound to source rows.
- **P2/P5/P1**：Bind actual adopted lower-fourth cells/caps to the proposed restoration integral and then certify that actual integral numerically.
- **P1/P3/P4-A**：Physical support and whole-box signed-factorization licenses, complete raw policy/density, parity dictionary and paid boxed-compiler error for the same actual coefficient/rho.
- **P3**：Full-modulus distribution and errors, common thresholds/endpoints, fixed polylog variation and frequency budgets, actual roughness comparisons, and analytic small-modulus SW premise.
- **P1/P2**：The coarse two-chart saving still needs a physical-domain change-of-variables/coverage dictionary before attaching to first-exit density; its closed-corner residual-ratio issue needs an interior approximation and paid arithmetic boundary reserve.
- **P4-A/P5**：Same-real-rho K density and complete Chen mean/c proof; P5 waits only for P4-A, not P4-B.
- **P4-B/P5/P0**：Actual hUpper/hLower suppliers and final unconditional entry remain open; no structural/typeclass repackaging of these inputs.

独立第五层积分候选在该固定源码中仍为 source pending；四个新文件不被当作那个口述候选的已验证替代品。P5仍只等待P4-A的同一实际rho密度输入，不等待P4-B。

## 对既有最终台账的补充

这份增量为正式供货身份提供补充证据。既有 ledger-final 在生成时只记录了新的 local HEAD，还没有完成这个同 SHA 远端核对；其历史内容保持原样。本次没有修改或重跑该台账，也没有把四个P1候选计入已核验生产组件。后续可依据 fixed-source-aliases.json 关联相同源码的正式供货提交，再等待对应验证回执。
