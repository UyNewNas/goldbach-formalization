# P2.1 手稿对应与查询接口范围

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
