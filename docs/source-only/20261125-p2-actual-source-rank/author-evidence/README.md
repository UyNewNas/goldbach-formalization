# Γ5 实际 U4 源：秩与物理 plateau 候选

**Core 已有验收收据；其余三个实际源模块仍为 SOURCE ONLY。**

共四个 Lean 模块、12 个源码声明。主代理报告作业
`bf050ecbd6a443f58fac442473a5528c` 已完成 Core 的 normal compile、stock replay
和 full-owned audit，拥有 1 个声明。Core 最终源固定为
`991d1db3a0cf3d7f291b84ff38bb421dc0011b09a4c2b8848f4a0077b972dc76`。
本地后加的 ` (s := xs)` 是与该编译字节之间的唯一差异，现已撤回；移除这 10 bytes
后逐字节哈希吻合。为保留已验源码，Core 源头的历史 source-only 注释也保持原样，
当前资格状态由本说明及 `REGISTRY.json` 的收据记录承载。

其余 11 个源码声明无本轮验收收据。Core 的纯条件性秩引理通过验收，不能据此认定
实际 arithmetic source 已获资格化。源码声明数 12 不等于本轮 audited owned 总数。
每个模块的当前源 SHA256、逐条结论边界见 `REGISTRY.json`；本子任务没有修改原 P2
checkout、调用云端命令或提交 Git。

## 来源选择

- 当前 P2 参照：`work/p2-formal-proof`，HEAD
  `e008ae002d4cec5f01b127a11dbb13016be38c97`。
- 固定手稿：1106 版本，commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`。
- 从原 `P2FiniteMarkedGamma5SeedPlateau.enhanced_position_source_one` 的 `.U4`
  caller 出发，保留相同 `LevelIndex`、`badLabels` 和 `roughNumbers` 条件。
- `rootHistory_coherent` 的准确 owner 是
  `Part5OriginalH430RequestedMember`；它的 `Coherent.letters` 给出旧槽素性。
  `rootQ` 的准确 owner 是 `Part5OriginalH430FrozenIntegerSupport`。
- 曾缺失的 history owner 已由来源审计恢复原字节，固定来源为
  `UyNewNas/goldbach-formalization` 的 commit
  `20701a39ebd15e41b39b8f1a9f5a977312169352`。完整 immutable path、Git blob 与
  SHA256 位于相邻目录 `../reused-h430/OWNER_PROVENANCE.json`。源码恢复不等于
  编译或验收；其传递导入闭包仍需资格化。
- 锁定 mathlib 为 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`。官方原件 API
  核对见 `MATHLIB_API_AUDIT.json`；已将 List 乘积单调性的 import 更正为
  `GroupWithZero.List`，并显式导入 `Ring.Finset` 提供 `Nat.cast_list_prod`。
- 主代理已把 ActualRank 和 SeedPlateau 接到保留原 FQN 的
  `Part5OriginalH430HistoryScaleCore`、`Part5OriginalH430HistoryRoughnessCore`
  与原 band 轻量来源；选择清单见 `../h430-core-extraction/MINIMAL_SOURCE_MANIFEST.json`。
  此导入重绑保持 actual-source 的原假设与结论，仍需其独立资格化。
- `P2SeedOmegaLiteralFibre` 的 `071f…`/`7fdc…` 差异是 a0/a2 owner 搬移，不是
  unused import 清理。新 cutoff core 与旧 Fibre 会形成重复 def owner；精确差异、
  toolchain 源码依据和主代理选择的尚未执行替换计划见
  `SOURCE_COMPATIBILITY_REVIEW.json`。此处没有更改 cloud Fibre 或 graph manifest。

## 手稿对应与缺失项分类

| 固定 1106 手稿位置 | 本候选采用的事实或边界 |
|---|---|
| `sieve-appendix.tex` 1090–1101 | 深度至多 440 给固定正残余指数，再除以 6 得共同素数 cutoff；有限选择先于 N。 |
| `sieve-appendix.tex` 584–620、633–660 | 原 Γ5 母域、含等号的坏 square、同一余商粗糙 cutoff 保持原样。 |
| `coefficient-appendix.tex` 318–331 | 有界 labelled-slot 秩、共同正 cutoff、完整乘积 O(N) 与混合 Euler 预算是不同要求。 |
| `argument.tex` 715–734 | 当前具体 frozen 常数对应现有 U3/U4 入口；本候选只接 `.U4`，未覆盖其他 generation-248 根。 |

本次未发现共同 cutoff 到源秩这一步的实质数学缺口。稿内略去的是初等推导：
若完整列表长为 h，每个槽至少为 N^a，且完整乘积至多 N，则 N^(a h)≤N；
N≥2 与 a>0 给 h≤⌊a⁻¹⌋。Lean 只需列表乘积、实幂单调性和自然数 floor API。
历史 owner 的来源解析及整个导入闭包的可验证性属于资格化边界。

## 四个最小模块

| 模块 | 具体新增结论 | 结论边界 |
|---|---|---|
| `P2MarkedSourceRankCore.lean` | 一般完整 List 的共同正幂下界与产品上界推出 `length ≤ floor(a⁻¹)`。 | 纯条件性初等引理，单独不供应实际源。重复因子与空列表均保留。 |
| `P2FiniteMarkedGamma5ActualRank.lean` | 真实 `.U4` 源的旧槽素性/下界；`old ++ qs ++ primeFactorsList m` 的逐槽素性与共同下界、准确乘积、乘积≤N、长度公式；导出统一总秩。 | 无新增 floor/rank 假设。仍依赖未资格化的历史 arithmetic imports。 |
| `P2FiniteMarkedGamma5ActualEulerBudget.lean` | 把导出的实际总秩送入已接受的 `finPhysicalProfile_boundedRank_mixedEuler_budget`；C 先于 N、source、width 选定。 | 只提供实际来源所需秩上的 Euler 预算，不构造完整 Family。 |
| `P2FiniteMarkedGamma5ActualPhysicalPlateau.lean` | 逐槽实际 physical point 的下界、与原 log point 的准确字典、physical/finPhysical profile 在原源上等于 1。 | 复用已接受 physical equality 与原 SeedPlateau，不把领口外 profile 等同于 sharp indicator。 |

该入口的固定参数严格使用旧定义：

\[
a_\Gamma=\texttt{frozenLeafCutoffFloor}
=\frac{11}{2304\,101^{440}}>0,
\qquad k_*^\Gamma=\lfloor a_\Gamma^{-1}\rfloor_{\mathbb N},
\qquad b(N)=N^{a_\Gamma}.
\]

真实合同的假设只有：`N≥2`、`0≤t≤1/12`、原 mesh 约束、原 `.U4` root band、
实际 `LevelIndex`、原 `badLabels` 成员关系及原 `roughNumbers` 成员关系。
物理 plateau 与 Euler 结论另沿用原有 `width>0`。调用者不提供旧槽素性、槽下界、
完整乘积界、秩界、ordinary-child admission 或 prime-product licence。

## 复用链与逐条语义边界

1. `RequestedMember.rootHistory_coherent` + `HistoryQuotientCounts.history_integer_roughness`
   + `SeedHistoryMass.scale_and_alpha` 供应实际 old slots 的素性、共同下界与产品正性。
2. 原 `pair_data` 供应两个 fresh slots 与原 prime window；`mem_roughNumbers`
   供应完整 `primeFactorsList` 尾。使用 `m>0` 的原结论，包含 `m=1` 的空尾。
3. 原 `actual_raw` 的 product 分支与 `source_fullProduct` 供应
   `old.prod * qs.prod * m ≤ N`；没有重证明 Γ5 几何或原产品 gate。
4. Core 只在上述真实推导结束后使用。使用 primeFactors 的集合成员关系只为证明旧
   槽下界；真正秩始终来自完整列表，不消除重数，不合并等乘积的 marks。
5. 物理接线重用 `logPoint_prefix_eq_log_product`、`physicalProfile_eq_original`、
   原 `enhanced_position_source_one` 和现成 `physicalToFin` 等式；未重新实现平滑函数。

没有关于完整 P2、全部稿内 families、selected-source licence、collar 支付或同系数
PP/VM 的新增结论；Γ5⁻ 也没有被变成普通反馈 child。新候选中的公开声明和直接
imports 均列于 `REGISTRY.json`。当前静态扫描无 `sorry`、`axiom`、`admit`、`unsafe`；
此扫描只排除文本洞，不替代 Lean 编译。
