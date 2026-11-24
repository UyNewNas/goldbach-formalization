# Batch8 normal 补审核：精确既有云祖先来源对齐

**本地准备已 exit 0，冻结 11 个实际 Built 目标、460 项完整项目源闭包。** 这是补审核计划及原证据整理，不是新的 kernel / full-owned 验收；没有重跑 normal、Lean、Lake 或云任务。

## 有界修正

旧生成器 `bf59b75d…` 原样保留在原目录，并在本目录 `history/prepare_batch8_normal_audit_bf59.py` 再存一份。它的拒绝揭示了真实来源差异：三份已有云祖先是已发布 a5a donor 修补，不能误归到 normal15 的旧 blob。

修订版只增加固定三模块 allowlist，绑定 review commit `ccb0f2e25c288a5c865241f392cc5586e6bc2847` 中 `batch8-preserved-cloud-dependencies` 的精确 package / manifest SHA。三个模块都必须是非 normal 目标，并逐项核对：

- 原 Batch8 完整 source context SHA `abb849aec311b84e039b6c3ecfdde710f72517f6ab41064420e96149432d2fa2`。
- 独立只读云导出原字节 SHA `fa817eb6c859fd85601d2c89f5ebd1b0f04217277d7be0d030f2fa65434614c8`，其真实 source bytes 与 source-plus-five 指纹。
- 已有本地 P2 Git 仓库中的不可变 donor commit `a5a42f8f70418a7b2b8a378713911e829786ec8b` 及精确 blob。
- ccb review canonical source、ccb 发布包 source、donor source、独立导出 source 四方逐字节一致。
- normal15 中旧 preimage 与原对齐 manifest 精确一致；项目 imports 不变；所有新旧来源分别记账。

目标自身仍严格绑定 normal15 的源码与 Git blob。其它祖先继续要求 normal15 / 实际 Batch8 context / ccb review 三方完全一致。没有取消 ancestor 检查，没有开放任意 overlay，没有改 e9 runner 或审核 gate。

## 三个已核来源与实际使用范围

| 现有模块 | SHA-256 | 进入本次 460 闭包 |
| --- | --- | --- |
| `P2PositiveAffineSimplexLogJensen` | `2c4cac96d6b340d91478be773a80ccead2004a49e217026a5914ebd879e5101f` | 是 |
| `P2DegreeSixLogGapSoundness` | `50efb68de1d444a77b8374e4c7245bba0b28977de006879f3a466aed1f4ef39c` | 是 |
| `P2OriginalLogMomentQ96Checker` | `49dddfb3fd522baed9938278d1711030ce204e0954c83758590b173e4197925c` | 否，仅保留固定三项 provenance |

因此计划的 `expected_project_sources` 恰为 460 键，未为 Q96 扩大闭包。使用的两项在 source metadata 中明确记为 a5a donor origin，另记 actual normal build context 为 15fbb；不会给它们套用 normal15 的旧 blob。

## 实际冻结结果

三个原 normal 组的实际 Built 数为 3 / 3 / 5，总计 11；组整体退出非零不抹去其中真实 Built。全部原日志、命令结束记录、Built / failed 集合、安装记录、Git show reads 和实际 context 均通过原有 gate。11 项如下：

- `ImbalancedChen.P2CompiledCausalPrimeSourceLower`
- `ImbalancedChen.P1Pair12RetainedSignedSource`
- `ImbalancedChen.P5OriginalCommonRefinedAncestry`
- `ImbalancedChen.P2OriginalLowerSelectedCapConstructor`
- `ImbalancedChen.P2OriginalSaving19SourceMeasure`
- `ImbalancedChen.P4AOriginalSecondResidualSupplier`
- `ImbalancedChen.P2HistoricSieveStateInduction`
- `ImbalancedChen.ActualThirdOriginalP4AOrdinaryBCandidateLeaf`
- `ImbalancedChen.ActualThirdOriginalRoundedStoredQueryIntegerConsumer`
- `ImbalancedChen.ActualExtendedThirdCompactSignedDensityLimit`
- `ImbalancedChen.P4BSmoothProfileMixedFrechetBudget`

前一轮 audit17 的完整接受回执已绑定：17 模块、534 owned declarations，状态 `PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS`，receipt SHA `c48dabe909ff7aad3db10982c24a1298afb6a4d91ee50bb10b44e0d7051d018d`。本计划将其排除，不重审；这不等于本次新 11 项已经接受。

并发输入来自根代理 `context-recovery/batch9-filtered-normal-inputs.json`，SHA `5dbe2bb3d39c9e537ed886c6ba1ad9c2906516fd21bff7efdd08c8498b62a531`。实际传入 29 normal + Higher 共 30 个写目标，与本次 460 项审核闭包交集为空。

terminal 代理独立末检确认：11 目标准确对应原 Built；460 键恰为 ccb import 闭包；全部 SHA 同时匹配 ccb 和实际 abb849 context；30 个写目标无冲突。其末检没有修改计划或重复生成原证据。

## 执行接口保持不变

沿用 exact e9 runner：先 `--prepare-only`，然后在原 state1 serializer 内显式 `--lane 1`。lane0 为空，不允许默认双 lane。runner 自身提供 guard；保留完整 source gate、源码及五产物、named leanchecker、全 environment-owned 类型/公理、前后 no-build gate。此次只执行本地 Python 准备。

## 文件与复现

- `frozen/AUDIT_PLAN.json`：可交根代理发布的冻结计划。
- `frozen/PROVENANCE.json` / `PRESERVED_SOURCE_BINDINGS.json`：完整来源与两个实际使用的 preserve 祖先。
- `frozen/NORMAL_EVIDENCE.tar.xz`：被使用的完整原证据，外加精确独立三源导出；不含搬运的编译对象。
- `frozen/SOURCE_GRAPH.json` / `SELECTION.json` / `MANIFEST.json`：精确闭包、实际选择和文件 SHA。
- `PREPARATION_COMMAND.json`：本次实际本地 argv、输入 SHA、exit 0 和时间。
- `STATIC_CHANGE_REVIEW.json`：旧 gate AST 保持检查；另验证其它 review commit 和将 preserve 源当 normal target 都立即拒绝。
- `GENERATOR_ALIGNMENT.patch` 与 `history/`：完整有界改动及旧版保留。

所有任务状态仍为“11 项 normal 已有，新的 kernel/full-owned 待根代理执行”；没有通过计划生成增加任何新的数学接受信用。
