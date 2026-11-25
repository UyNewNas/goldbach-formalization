# P1.5　原策略第四、第五层修正的极限

在源提交 `089a7f99646fe1921d0cd1450485561e6b52b5e4` 的第七轮投递时，选定的 23 个 Lean 模块已有 **21 个**取得正常编译、独立内核检查和全部自有声明的类型与公理回执。第四层完整均值在这 21 个之内。其余两个模块是实际第五层无截断控制 `P1ActualVariableFifthUntruncatedDomination` 及依赖它的 `P1ActualVariableFifthFullMean`。下文列出三个公开定理的数学陈述；整条均值链的验收以最终逐模块回执复核为准。[第七轮记录](round-07/README.md) · [回执复核程序](review_retained.py)

## 同一策略上的三个极限

令 $z_N=N^{19/96}$，$C_N=\mathtt{singularSeries}(N)$。以 $T_3(N),Q_4(N),Q_5(N)$ 分别表示原第三层、实际第四层和实际可变第五层策略的保留多项式值。三者在同一个 `roughPrimeUniverse N (cap N) 0 z_N` 上求值，素数权为 $1/(p-1)$，递归从空历史 `[]`、实参 `true` 和初值 $1$ 开始。第五层继承同一个实际第四层，保留原 `rawQ3`、`firstStop` 和各前缀的准入判定。对重叠且获许可的行取实际最大值；第五层用旧、新端点各自判定本层立方条件。空历史仍在保留支撑中，模数 $d=1$ 的系数为 $1$。[有限差恒等式、空历史与模数一](../../../../ImbalancedChen/P1OriginalFourthFifthTotalTupleSource.lean#L50) · [手稿第四、第五层换帽公式](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L109-L153)

共同参数为 $e\in\mathbb Q$、$e\ge0$，$\chi\in\mathbb R$，$m\in\mathbb N$，$0<\omega<19/96$，以及 `cap : ℕ → ℕ`。固定第四层有限行集 `rows4 : Finset ProducerRow` 和许可谓词 `licensed4 : ProducerRow → Prop`；涉及第五层时另固定 `J5 : Finset (Label5 m)` 和 `rows5 : Finset (FifthRow m)`。以下均沿正偶数 $N\to\infty$，即 `atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}`，并要求沿此滤子最终 $z_N\le\mathtt{cap}(N)$。记 $w_N=\log(N)/C_N$。

| 归一化后的保留多项式差 | 极限 | 额外网格条件与公开定理 |
|---|---|---|
| $(T_3(N)-Q_4(N))w_N$ | $I_4$ | `logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2`。[第四层策略差定理](../../../../ImbalancedChen/P1OriginalVariableFourthFullSourceMean.lean#L116) |
| $(Q_4(N)-Q_5(N))w_N$ | $I_5$ | 对共同参数及上述第五层数据成立。[第五层策略差定理](../../../../ImbalancedChen/P1ActualVariableFifthFullMean.lean#L86) |
| $(T_3(N)-Q_5(N))w_N$ | $I_4+I_5$ | 需要第四层网格条件。逐个 $N$ 相加时，同一个 $Q_4(N)$ 精确消去。[总差定理](../../../../ImbalancedChen/P1ActualVariableFifthFullMean.lean#L107) |

$I_4$ 是 `fullActiveIntegral e chi m omega rows4 licensed4`，在全部启用的原分支标签上累加实际第四层核的无截断积分。$I_5$ 是 `fullSelectedIntegral e chi m omega rows4 licensed4 J5 rows5`，在 `selectedFifthCells e chi m omega J5` 的每个完整单元上积分实际第五层核后求和。因此“完整”对第五层指给定选择及其全部单元内部积分，结论仍保留 $J_5$ 和两层生产行参数。[第四层积分定义](../../../../ImbalancedChen/P1OriginalVariableFourthFullActiveIntegral.lean#L240) · [第五层积分定义](../../../../ImbalancedChen/P1ActualVariableFifthUntruncatedDomination.lean#L263)

## 如何去掉正截断

固定截断 $a>0$ 时，原有限和按同一前缀规则精确拆成 $F_N=P_N(a)+R_N(a)$。$P_N(a)$ 是对数坐标带正下界的贡献。第四层按实际活跃分支细分，第五层按所选单元求和。两层分别得到 $P_N(a)\to I(a)$。[第四层正截断定理](../../../../ImbalancedChen/P1OriginalVariableFourthFullActivePositiveLimit.lean#L236) · [第五层分拆](../../../../ImbalancedChen/P1ActualVariableFifthGlobalSourceAssembly.lean#L104) · [第五层正截断定理](../../../../ImbalancedChen/P1ActualVariableFifthGlobalPositiveLimit.lean#L37)

小坐标部分保留原算术符号，并估计其绝对值。第四层存在 $D>0$，对 $0<a$、$4a\le\omega$，最终对偶数 $N$ 及任意上限、行集和许可谓词均有 $|R_N(a)|\le Da$。第五层固定其行数据后存在 $D>0$，对 $0<a\le\min(19/96,\omega/6)$ 和满足上述最终下界的上限，同样最终有 $|R_N(a)|\le Da$。第五层使用实际末坐标的逐项界及移动中间壳层的算术矩估计。常数先于 $a$ 选定；充分大 $N$ 的阈值可依赖 $a$。[第四层余项](../../../../ImbalancedChen/P1OriginalVariableFourthFullSmallRemainder.lean#L248) · [第五层余项](../../../../ImbalancedChen/P1ActualVariableFifthUniformTail.lean#L143)

在积分端，同域上的可积上界控制实际核，从而 $a\downarrow0$ 时 $I(a)\to I_4$ 或 $I_5$。第五层用原 `rawQ3` 到初始端点的粗核控制实际第四、第五端点间的连续核差；有限的有符号算术密度没有由此得到单调性。给定 $\varepsilon>0$，先选 $a$ 使 $Da<\varepsilon/3$ 且 $|I(a)-I_i|<\varepsilon/3$，再令正偶数 $N$ 足够大，使 $|P_N(a)-I(a)|<\varepsilon/3$。三角不等式给出表中前两个极限。[第四层可积性与截断极限](../../../../ImbalancedChen/P1OriginalVariableFourthFullActiveIntegral.lean#L107) · [第五层连续控制](../../../../ImbalancedChen/P1ActualVariableFifthUntruncatedDomination.lean#L281) · [固定版手稿的有限策略实现及截尾](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L273-L302)

## 仍须估计的物理计数误差

上表的被估对象是保留多项式差。单素数分布估计还要对同一个物理有符号系数，控制实际素数计数与精确互素均值之差，尺度为 $H_N=C_NN/(\log N)^2$。U06 的短中段结果控制 $R_{\rm free}-\mathtt{remainingRow}$，并留下显式余项。从释放平方自由约束后的 `free` 回到物理系数 `rho`，还要支付碰撞恢复并在同一参数族上汇总。[U06 合同、余项及原稿定位](../u06-reuse/CONTRACT_REVIEW.md) · [固定版原稿单素数分布公式 `eq:current-PP`](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex)

`middle N Q c` 保留模数族 $Q$ 和对应权 $c$。两项历史误差 `comparisonMiddle`、`savingMiddle` 分别使用 `(S false, R false)` 与 `(eight false, six false)` 的实际支撑和符号权。OneLong 源码候选移出单长素数子和后，还留下对应的 `historyRemainder`，其中 `retainedAtlas = trimReserve + Σ(mediumAtlas + remainingTypeIAtlas − properPowerReserve)`。这些项仍需在各自原系数上估计。即使表中三个均值全部取得回执，单素数分布、两项历史误差及其在同一阈值上的合并仍是整项 P1.5 的独立义务。[两个历史的精确对应](../../../source-only/20261123-yellow-node-owners/y01_gain_reserves/ImbalancedChen/P1Full87HistoricalMiddleSmoothing.lean#L118) · [OneLong 源码边界与余项](../../../source-only/20261125-p15-historical-onelong/README.md) · [OneLong 依赖源码核对现状](history-source-recovery/README.md)

稿件依据固定为 `UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a` 的 `paper/release-20261106/en`。工程计划列出的定位为附录 F.2、F.3 和命题 D.3；上述密度差与有限策略实现另可按 `sieve-appendix.tex` 的固定标签 `sv:even-gain`、`sv:odd-gain`、`sv:literal-density`、`sv:finite-realization` 核对。[工程计划](../../../superpowers/plans/2026-11-25-p15-actual-means.md) · [稿件文件与 Git blob 清单](../../../source-only/20261123-resume/ten-task-continuation/PUBLIC_SOURCE_MANIFEST.json)
