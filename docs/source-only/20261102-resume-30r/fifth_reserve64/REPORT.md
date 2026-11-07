# R05 — actual full-archive reserve64 payment

**SOURCE ONLY / UNCOMPILED / kernel_verified=false / formal_credit=0.** 两份新 Lean 源码共 11 个定理，为 Q07 已扣除的真实 `indexedActualReserve64` 补上逐 parent、全 292633 原位置和原预算的实际供应。没有运行 Lean/Lake/compiler、有限 guard、数值程序、CI 或 Git。只写本目录，无子代理。

本轮恢复时发现闪退中断最后一次写入使 Schedule 文件为 0 bytes；已从本会话完成的源码恢复。最终字节与声明位置以 REGISTRY 为准，未把中断前的 hash 当成交付。

## 原稿核对与复用范围

先读 R/BRIEF、Q07 REPORT/REGISTRY 和 Q23 最终 review。读取原 `../goldbach-research/fifth-prefix-subdivision-refinement.tex` 全文及 certifier 的 `split_bound/full` 段，核对了 292633 原 parents、每父完整 `2×2×2×2×4=64` 分割、原 mask/固定 old planes，以及逐父 `max(old,childsum)`。原 tex 113–134 行要求 whole-parent maximum；149–164 行给原精确端点和安全舍入的严格余量。原 adaptive tex 43–61 行要求先固定 buffered partition 再取 N，逐步回收端点积分。主 manuscript 451–509 行的两笔 reserve 是密度逼近和编译两种开支，不能合并。

搜索 production、历次 source-only、hidden/ignored `.lake/proof-continuation/source-reviews/drafts`。精确复用如下；完整路径、raw SHA256、import、声明位置见 REGISTRY。`wholeActualReserve64` 不是已验证的旧声明名，交付不引用它。

| 既有来源 | 本次实际使用 |
| --- | --- |
| D `P5AllChildrenReserveReassembly.lean` | `sum64_reserve_eq_single_raw_reserve`，把真实 64-child reserve 精确合为一笔 raw omitted volume 与一笔 retained modulus；不重写分割/有限可加性。 |
| F `P5HistoricalMask56FullSourceChildren.lean` | 实际 `indexedActualReserve64` 定义及 `selected_strict_owners_eq`；reserve 定义本身对全部 ArchiveIndex 适用，无 mask56 过滤。 |
| C `P1OriginalFifthActualCrossingSections.lean` | 已证明的真实 selected/firstStop owner 对称差体积 `428/75 * e / 400^4`，不是假设五维体积小量。 |
| E/F indexed archive、typed base geometry | 原源位置/重数、真实 licensedOwners 的 0/e selected/firstStop、全部五个 lower keys 在 1..77、`licensedIndices=univ`。 |
| F `P5HistoricalCanonicalFilterReserve.lean` | 实际 zero-buffer omitted cost 的 history/filter 精确拆分及每父 `12*(4e+2h)` strip rate。 |
| H uniform gate payment | 原有限正 gate margin、`licensedOwners=adoptedOwners`、真实 gate rejection=0。 |
| H `P5HistoricalGatePaidReserveSchedule.lean` | 既有 `gatePaidEnvelope`、其连续性/零点及 `exists_gate_paid_buffer`。不新建 envelope，也不重新证明连续性半径。 |
| Q `P1HistoricalFifthActualHistoryAdmission.lean` | 全实际源行的 history 空集及逐父/bank history cost=0；同 e/q/chi/omega。 |
| Q `P1HistoricalFifthFullOriginalFloorEnvelope.lean:101` | 原完整 `storedNew−oldBranchDefect−actualReserve64≤archiveFifthIntegral` 仅作为对接位置，未复制或重证。 |
| `P4AAll22OriginalKLedger.lean` | 原 `densityReserve` 及其正性，保持与 `compilerReserve` 分开。 |

143 个 typed blocks、72 个 stored old/new blocks 继续沿用 Q 的对象和 pins。本任务不转写数据、不重建 child facts、Jensen receiver、stored maximum 或积分组装。reserve 支付使用原 typed 行；72 个 stored fields 只在现有 Q envelope 一侧出现，本次不解码或重算它们。

## 新增的实际推导

`P5HistoricalActualReserve64Budget.lean` 首先从真实五坐标 key bounds 推出 `fixedParent=raw.originalBox`。借既有 strict-owner 恒等式证明

```
rawRetained(i,e,q,chi,omega) = indexedDomain(i,e,q,chi,omega,e).
```

最后的参数是 **e**。D 的完整 64-child 重组在这里保持 buffered retained set，不能把它直接换为 zero-buffer domain。新域包含关系是

```
rawOmitted_e ⊆ indexedOmitted_0 ∪ ownerSymmDiff_0_e.
```

两个集合均为原同组 licensed owners 的真实域，保留 fullCell 中的历史/firstStop 与严格 gates。没有把 open failures 删除为零测墙。

C 的实际 section/Fubini 界控制对称差；retained volume 至多原 raw volume `1/400^5`。非负 mass/modulus 逐项相乘后得到

```
indexedActualReserve64(i,e,q,chi,omega)
  ≤ original rowEnvelope(i,e) + indexedTrimCost(i,e,q,chi,omega).
```

其中 `rowEnvelope = rowModulus/400^5 + rowMassBound*(428/75)*e/400^4` 是原对象，未把 literal 积分误差的数值结论拿来充当 child reserve。

在原 `chi=e/20`、`h≤e/20`、`h≤omega/2`、`0≤omega≤1/800` 和 `e≤archiveGateMargin/4` 下，H 的 gate=0 与 Q 的 history=0 使 `indexedTrimCost=canonicalFilterCost`。既有每父 strip 率满足 `12*(4e+2h)≤64e`，故

```
each actual reserve64 ≤ rowEnvelope + 64*rowMassBound*e,
sum_(all original indices) actual reserve64 ≤ gatePaidEnvelope(e).
```

这里的 `64` 是 H 已有 strip 估计系数；不是为 64 子盒各收一次 parent mass。原每父 64 children 在 D 中已精确合并，没有 owner 数、排序 factorial、Chen quarter 或新增归一化系数。

`P5HistoricalActualReserve64Schedule.lean` 使用原 `exists_gate_paid_buffer eta`，先选正有理 e，再取一个 aligned q。得到真实全档 reserve `< eta`；在同一 witnesses 上同时保留 history=0、gate=0、licensed=adopted，以及已有 old-literal error `< eta`。这两项各自 `<eta`，**未声称其和也小于 eta**；如后续同时收取两笔费用，可在同一个 theorem 取 eta/2。

原预算特化给全档 reserve `< densityReserve/8`，数值保持

```
145007961227048312210593427530128000784681 /
11807308407697609823574244952794825721118720000.
```

还可在同一 e/q 下同时取

```
reserve64 < min (densityReserve/8)
  (3037921066812732539869/302231454903657293676544 - 10051/1000000).
```

这直接对接原 subdivision 的严格安全舍入余量。只写出一个新的闭合 rational-margin `norm_num` 证明体，状态 **UNEVALUATED**；没有计算 archive floor 总量或对数据运行 guard。原第三项已占用的 `u_d/4` 没有再花一次，distinct compiler reserve 也没有被识别成这笔 analytic loss。

## 实际移除的前提与剩余边界

不再需要 caller 假设全档 reserve 小量、逐父 omitted-volume 小量或任意 buffered retained=zero-domain 等式。输入只剩原 e/omega 范围、原 mesh inequalities 和正 tolerance；真实域转换、体积支付和存在量词均有严格 body。

该供应属于 **(2) 原稿可补的遗漏推导**。未发现坏档案行或原稿矛盾。**(1)** 导入部署、elaboration、API 与 kernel 接受尚未检查；所有继承 F/G/H/Q 的有限 archive bodies、binary-to-typed authentication、相关生产源码 guards 和本次单个新 rational-margin body 仍未执行。元数据 hash 不是数学认证。

Q07 全档 envelope 的 `oldBranchDefectQ` 仍由 R04 另供。这里没有重证或假设未扣债 stored floor、完整87策略、同一物理 rho、All22、完整两笔 reserve、PP/K。即使本次真实 reserve 已有源码供应，上述 broad endpoints 仍不能据此关闭。

## 静态交付核对

只做源文本/import/声明清点、raw byte SHA256 和 JSON 解析；未做任何数值重放。新文件 intended modules 为 `ImbalancedChen.P5HistoricalActualReserve64Budget` 与 `ImbalancedChen.P5HistoricalActualReserve64Schedule`，未安装到 production。REGISTRY 登记全部直接 import 的 exact source、所用传递来源、原稿 pins、11 个新声明、剩余前提与禁止执行状态；支持脚本只生成元数据。
