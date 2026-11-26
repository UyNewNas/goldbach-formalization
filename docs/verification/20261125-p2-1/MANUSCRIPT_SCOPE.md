# P2.1 手稿对应与查询接口范围

> **2026-11-26 核验更新：** 固定五根查询闭包已取得真实 P2 云端验收：140 个项目模块、18,581 个唯一归属声明、26 个具名公开目标，以及五根联合导入。源码快照为 `00af18335dcebcc5e24571e33be7791ff718fbff`；最终回执绑定核验提交 `1de0453bee55bf1128be422787216937b8fda9c9`。完整归档发布进度及原始回执见[本轮结果](../20261126-p2-1/README.md)。下文保留早期基线、范围分析和当时的待核验状态；它们不代替最新回执。

手稿版本为 `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 的 20261106 英文发布稿。下述行号针对该提交。核对时，`master` 的 `numerical-appendix.tex`、`sieve-appendix.tex`、`argument.tex` 与该提交的对应 Git blob 相同。Lean 源码定位以 `UyNewNas/goldbach-formalization@a929011ec95843553fc2e10b7291c8077e0952c0` 为基线。本文记录陈述、对象和调用关系；编译、内核核验及其对象版本应以本轮单独的验证记录为准。

## 手稿锚点

| 发布稿位置 | 适用于 P2.1 的数学内容 |
| --- | --- |
| [numerical-appendix.tex, 94–120](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L94-L120)，`num:log-enclosure` | 在分母 $Q=2^b$ 上用 $\lfloor Qx\rfloor,\lceil Qy\rceil$ 包住区间，乘法取四个端点乘积的极值，除法要求分母区间有正下端点。对数以 $z=(x-1)/(x+1)$ 展开，配显式几何余项。此处 paired 对数例程使用 96 项、工作分母 $2^{224}$ 和返回分母 $2^{160}$。 |
| [numerical-appendix.tex, 122–175](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L122-L175)，小节 *Enclosing delayed functions and integrals* | $A_+(s)=sF(s)/(2e^\gamma)$、$A_-(s)=sf(s)/(2e^\gamma)$ 的初支与延迟积分逐格传播。弦积分的权为 $(j+1)\log(1+1/j)-1$ 与 $1-j\log(1+1/j)$，二者非负；$j>n$ 时，积分弦误差至多 $1/[12nj(j-n)]$。Buchstab 的相应分子是 $s\omega(s)$，初支在 $[1,2]$ 上恒为 1，之后满足 $(s\omega(s))'=\omega(s-1)$。 |
| [sieve-appendix.tex, 222–251](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex#L222-L251)，`sv:literal-density` | Suzuki Proposition 11.8 与 Lemma 14.7 提供引用的退出级数和有限秩夹逼输入。对 $p\mid N$ 的删素比较、先选秩再令 $N$ 增大，是稿内对一致性的论证。查询使用既有归一化实际函数及其延迟积分性质。 |
| [sieve-appendix.tex, 563–582](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex#L563-L582)，`sv:omega-envelope`；[argument.tex, 840–862](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/argument.tex#L840-L862)，`lem:current-omega-refinement` | 对 $v\ge u\ge1$，稿内证明 $\omega(v)\le\max(1/u,70893/125000)$。稿内还证明 $s\ge1$ 时 $\omega(s)\ge1/2$，以及 $s\ge7/3$ 时 $\omega(s)\ge11/20$。这些常数及其适用区间可从已有证明复用。 |

## Suzuki 点查与区间查

| 消费者及原始参数 | 需要保留的对象与语义 | 已定位的 Lean 入口 |
| --- | --- | --- |
| 原公开点查，$n=16384$，终点 12，整数分母 $2^{112}$ | 目标是归一化的真实下筛函数及其零延拓。$q\le2$ 返回零。$2<q\le12$ 时，整结点直接读取原分子；非结点以 $i=\lfloor nq\rfloor$ 作定向弦插值，上端加 $\lceil 2^{112}/[8n(i-n)]\rceil$，再定向除以 $q$。$q>12$ 时，下端来自终点 12 的真实下函数界，上端来自该处的真实上函数界。返回整数精确乘 $2^{48}$，按 $2^{160}$ 解码。 | `ActualThirdOriginalRationalQuery` 定义整数与有理接口。`Certificates/OriginalNodeArraysV1/All40PublicQuery.public_compact_query_value_encloses` 的结论限于 $[2,12]$。在 `ActualThirdOriginalStoredQueryAllBranches` 中，`CheckedBlockTable.rational_query_encloses_all` 覆盖所有有理数；原 40 块表的实例为 `All40CheckedTable.literalCheckedBlockTable`。 |
| 同一函数的紧区间查询 | 对 $2\le l\le x\le h\le12$，左端的定向下界和右端的定向上界包住整个区间内的实际函数值。这里可用实际下函数的单调性。 | `P0RationalQueryPublicAPI.rangeQuery_sound`。点查与区间查的输入域应分别记录。 |
| paired `Ordinary.f`，$g=16384$，终点 8，整数分母 $2^{80}$ | 历史算法用上下分子的双层整数梯形舍入、误差项、结点或分子插值以及定向除法。$q\le2$ 为零，$q>8$ 走该表自身的终端分支。同一真实下函数在这套算法中对应另一对整数端点。 | `P2HistoricSieveTableSemantics.sf` 与 `P2HistoricSieveStateInduction.sf_contains_actual` 对所有有理 $q$ 给出包含关系。`P2HistoricBackendTypeAdapters.sourceSf_contains_actual` 和 `P2HistoricalSavedFloorFullBinder` 直接消费该结论。 |

点查在精确结点取该节点值。另有一种查询面向分片常数亏损表：在整个闭支持上取相交格的最小值，结点处计入两侧。该规则用于 $h_{248}$ 等亏损数组。原稿对这两种操作分别给出了依据。[原公开点查与终端分支](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/numerical-third-compact-source-review-20261010.txt#L144-L154) · [闭格亏损读取](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L876-L884) · [paired 原估算与独立上界](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/corpus-renewal-paired-certificate-v2-20261010.txt#L85-L97)

## Buchstab 区间上界与证书路线

`P2BuchstabRationalSemantics.check_cell_sound` 把通过对应有限校验的有理格数据连到实际 Buchstab 函数。`P2SeedOmegaRationalRangeEnclosure.actual_buchstab_range_enclosure` 将格界用于整个查询区间。这一接口需要针对所选数组满足的校验条件。文中四前缀 switched 核在格上的实际查询对象为 $\omega((1-S)/z)$。[numerical-appendix.tex, 425–445](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L425-L445)

作者表使用网格 4096 和 80 位定向精度。独立 N48 重放使用网格 8192、112 位精度与 48 项对数展开，先在 $[2,3]$ 用 $s\omega(s)=1+\log(s-1)$，再传播延迟积分。它扫描从 $\lfloor8192l\rfloor$ 到 $\max(\lfloor8192l\rfloor,\lceil8192h\rceil-1)$ 的格上界并取最大值。`OriginalPairedN48RawQueryFamily.original_raw_query_uniform` 的源码对 $2\le l\le h<10$ 和每个 $s\in[l,h]$ 给出定向上界，前提为 `SourceProducerValid p`。使用具体独立数组时还要把该前提落实到所选数组；基线中的候选材料位于 `docs/source-only/20261028-resume-30{d,f}/certificate_omega/`。两条路线共用实际函数与闭支持。消费某套历史整数端点的声明需额外标明其生产器与所证端点的对应。[两种网格的一手记录](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/proof-library/source/sharp-248-four-min48-independent-review-20261008.tex#L40-L49)

P2.1 的核对止于指定计算定义对实际函数的定向查询界，以及在声称具体表身份时所需的证明。各专项积分采用的其他网格、四前缀全部行的费用、保存 floor 合计与最终系数归属于对应的下游数值义务。这里的源码定位本身只支持 Lean 定义和声明层面的识别；外部脚本的完整执行语义、历史序列化字节与证书文件身份均需各自的证据。

## 确定性 Buchstab 闭区间接口与既有证据

`ImbalancedChen.P5Z.AutomaticBuchstabIntervals.actual_interval_bounds` 是一个可直接复用的公开根。其唯一定量输入是正整数网格参数 $m$ 和有理端点 $1\le l\le u\le8$。对每个实数 $s\in[l,u]$，它给出 $\mathrm{intervalLower}(m,l,u)\le\omega(s)\le\mathrm{intervalUpper}(m,l,u)$。两个端点均为确定性递推产生的有理数。相交格由闭不等式筛出，内部结点包括左右两格，边界 1 和 8 由各自的端格覆盖。调用者只需给出几何定义域。现有消费者 `P5ZU1011OriginalSixteenTightSwitchedBoxes` 已使用该入口。[查询与格定义](../../../ImbalancedChen/P5ZU1011AutomaticBuchstabIntervals.lean) · [实际调用处](../../../ImbalancedChen/P5ZU1011OriginalSixteenTightSwitchedBoxes.lean)

这个定义域足以覆盖上文识别的四前缀查询窗口。已有 N48 坐标源码中，`all_native_raw_query_range` 给每个原生行的有理参数界 $2\le l\le u\le8$。因此，若验收项是该窗口中一个可构造的真实函数区间查询，可直接核验此公开根，无需另行复刻作者的 Q80 Buchstab 数组。若验收项指定历史数组的某个整数值或保存 floor，该生成器的区间包含定理并不提供所需的整数等式。数值附录 122–143 行对延迟函数的通用讨论未指定上界 8，使用其他区间时需保留 `P2SeedOmegaRationalRangeEnclosure.actual_buchstab_range_enclosure` 的校验与索引覆盖前提，或另行核验确定性任意有限范围的 `P2SeedOmegaGeneratedRangeRate.generated_actual_range`。本条 $[1,8]$ 范围的验收仅对应上述窗口。[原生行范围](../../source-only/20261028-resume-30f/certificate_omega/OriginalPairedN48AllNativeQueryGeometry.lean)

| 可定位的历史记录 | 可计入的证据 |
| --- | --- |
| `P5ZU1011AutomaticBuchstabIntervals.lean`，SHA-256 `5f2b919315e50437ebddb0ac121aa9a64f606df8c70989bba4b5bf360247b051` | 10 月 25 日 batch21 的身份清单与当前文件逐字节匹配，清单模式为 `SOURCE_ONLY_UNCOMPILED`。截至本次独立核对，在既有材料中尚未定位到该根同源码的正常编译、内核回放、公开类型与传递公理完整回执。适合复用源码并补该根验证。[来源清单](../../source-only/20261025-code-only/batch21/source-manifest.json) |
| 其前置模块 `P2BuchstabRationalSemantics.lean`，SHA-256 `61be50d893630adbe13cc83e6a26c59743adab725c5c54ed754639aa9093665e` | 11 月 23 日已有同源码正常编译、指定模块内核回放与 57 个公开声明的类型及传递公理记录，可复用。包括带 `check m cs = true` 的整格结论，以及具体五节点半格表 `halfMeshSeed_checked`。这两项与上层区间根分别计证。[前置模块历史证据及回执路径](REUSED_EVIDENCE.json) |

## 原 compact Q80 查询与 P2.4 的分工

1106 数值附录 198–205、230–233 行把 $I_{3,c}$ 计入上密度，并要求其紧域分割和边界上估。作者计算该项时使用 `certify_extended_prefix.py` 的 `SieveTable(16384,12)`；配对项 `Ordinary.f` 另用同一精度下终点为 8 的表。独立 P112 弦表也有终点 12，但其舍入运算和原 Q80 表不同。[数值附录](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/numerical-appendix.tex#L198-L233) · [作者程序](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/verification/data/certify_extended_prefix.py#L51-L116)

P2.1 在提交 `8703e635` 中逐字节采用 P2.4 提交 `63fcd869` 的 `P2OriginalCompactQ80Table.lean`，SHA-256 为 `e9f37ac098bb46dc8befa0211d7c39ac8a0907ef675b9ebca824ffa58d49e66a`。该文件作为第五个根模块，仅直接导入已有的 `P2HistoricSieveStateInduction`。四个待验定理属于 `ImbalancedChen.P2OriginalCompactQ80TableSourceOnly`。其中 `table12_encloses_actual` 覆盖索引 16384 至 196608 的节点，`numerator12_contains_actual_L` 覆盖正分母且 $2b<a\le12b$ 的分子插值，`point12_contains_actual` 覆盖任意整数分子和正整数分母，`sf12_contains_actual` 覆盖每个有理查询。该源文件的正常编译、独立内核重放及全部自有声明的类型和传递公理审计仍待取得同源回执。[P2.4 原始源码](https://github.com/UyNewNas/goldbach-formalization/blob/63fcd8691951b552078d928bb840c5eef46d0221/ImbalancedChen/P2OriginalCompactQ80Table.lean) · [P2.1 采用记录](COMPACT_PROVIDER_REUSE.json)

本批次核验的是上述数学查询。P2.4 的数组与缓存实现另有 `point_eq_historical`、`tableArray_lookup_historical` 等接口；历史序列化数组的字节身份、自适应分割树、叶序与整数 charge、每叶积分以及归档总和需各自的证据。此前 P2.4 的 339 模块依赖清单及 22 个 CI 来源文件记录了准备工作。P2.1 的五根完整清单和验收命令另列。[P2.4 分工](https://github.com/UyNewNas/goldbach-formalization/blob/67e0791e62db299690d29f19440bcf579e5e1492/docs/superpowers/plans/2026-11-25-p24-original-compact.md#L3-L20) · [当前目标](TARGETS.json) · [验收计划](AUDIT_PLAN.md)
