# P1.5 — 独立新增 TrimLogAccuracy 目标

本次把已经完成整模块 elaboration 的
`ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy` 接入独立单 owner
验收路径。原 21-target runner、manifest 及其 18/21 接受计数保持原范围。
本文件是执行入口的发布说明；正式 normal/kernel 是否接受，须以本次
发布之后的实际任务和原始回执为准。

## 所证明的估计

源码中的唯一公开定理为
`eventually_original_singleton_atlas_trim_logAccuracy`。固定
`0 < kap0 < 1`、自然数 `A` 和 `eps > 0` 后，最终对每个 `N`，统一于
实际 profile 参数 `kap`、collar order `B`、有限模数集合 `Q` 和实系数
`rho`，只要 `Q ⊆ Finset.Icc 1 N` 且 `|rho q| ≤ 1`，便有

\[
\left\|\operatorname{trimReserve}
  (\operatorname{actualLicence}(\mathrm{kap},B,N),
   2N,N,\mathrm{kap0},Q,\rho_{\mathbb C})\right\|
\leq \mathrm{eps}\,\frac{N}{(\log N)^A}.
\]

这里仍使用原始有限 `Q` 与原 signed `rho`，阈值先于 `kap,B,Q,rho`
选定。没有把目标 trim-error、smooth proper-power 或 medium 估计加入
假设。`kap0` 与实际 profile 的 `kap` 仍是定理声明中两个各自明确的参数。

证明复用 AtlasTrim 的精确 prefix 字典和已接受的 primitive prefix
budget，将右侧展开为

\[
3C N^{1-\mathrm{kap0}/2}
+12N^{1-\mathrm{kap0}}
+12N^{1-\mathrm{kap0}}\log N.
\]

三个既有 power-log 供应分别支付 `eps/3`。最后一步用
`(add_le_add (add_le_add h1 h2) h3).trans_eq (by ring)` 合并；没有重证
已接受的 divisor、零差项、source reindexing 或渐近估计。

## 源码身份与实际整模块检查

canonical 文件精确采用 AD 发布中的修正稿，4303 字节，SHA256：

`b0786de15bf78fed3751fc408735482b807e39931e87056d3d60780fa2123bb4`。

来源为 AD `e91af3a5c407bdeea243af7dd3c4248949d83e9b` 的
`docs/source-only/20261126/p1-atlas-trim-log-accuracy-budget-sum/`。
原 source-only 文件和原 review 保留；canonical 的历史开头注释也逐字
保留。后续形式状态由绑定这一精确源码的实际回执确定。

整模块 probe `job_7665d03cf175443da5d86004875cb7a6` 实际返回 0，
任务总时长 106.961555 秒，Lean 步骤 17.435 秒。它通过原 serializer
和 guard 执行 `lake --no-build env lean`，没有请求输出对象，也没有
重建任何已有项目模块。原始 probe 报告为 2875 字节，SHA256：

`eb98e6b13ba803051820a5637cad7c3c512ffc41f8090997cf2e07203557b2e7`。

此结果仅说明整模块可 elaboration；正式 acceptance 仍单独执行。

## 新目标与原依赖的边界

新模块唯一 direct import 是原已接受的 AtlasTrim。其 153 个既有
依赖与 AE 原接受前缀一致；连同新模块，项目源码闭包为 154。该闭包
不含 held P3 dependencies 或缺失的 FixedM 文件。

独立入口继续读取原 AE LowerTrim / AtlasTrim 及原 AG
ReserveBranches / AtlasRoughPrime 的接受回执。新 module 的 normal
build 和完整内核导出审计单独记账，原历史 owner 不重编译、不重绑。
源码安装和编译分别执行；任何意外已有产物、未完整的 prior attempt
或上下文差异都会保留原状态并 HOLD。

P1.5 仍未闭合。原三项 proper-power/P3 HOLD、缺失 FixedM、literal
historical medium 的同源供应和完整 signed bound，以及
`hSmoothSignedPP` 的条件边界均保持；本 trim 估计没有消除这些缺口。
