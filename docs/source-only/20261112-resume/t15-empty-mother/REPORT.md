# T15 · Y18 原 Γ 母词列表的空词保留项

原 U5 根的 `emptyJointError` 恒等于零。原因在发生次数上。产生 `sourceTest` 的 Γ7–Γ21 字典含 22 个带重数的词，每个词至少有两个位置。原完整 21 项公式另含同前缀的 Γ1，其两个系数 4、1 继续进入各自的筛数。本次给出 2 个 Lean 源文件、17 条定理，状态为 **BLUE / SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED**。P3.6 总节点仍黄，正式信用为零。

## 从稿内的 Γ 项到实际发生列表

固定原稿 `9731290e8f53cffda44129906cde6a965eaa869b`。原 `replacement-second-seed-route.tex` 97–151 行列出 21 项、四个半开素数区间和次末已标素数决定的商 cutoff。Γ1 的点态系数是 $4+\mathbf 1_{A=0}$。带原标记整数 $d$ 作加权和后，其两个筛数是 $4\Phi_{s_0}+\Phi_{\phi_1}$，分别使用同一物理 $Q/d$ 的两个幂次。原 `own-chen-table-insertion-chain-20261009.tex` 293–336 行保留相应的 $4H(s_0)+H(\phi_1)$ 反馈。Γ2–4 选 1 个新素数，Γ5–6 的原生分支各选 2 个。原生 `SecondFunctionalMotherCarriers.lean` 55–71 行把这六项与后续词列表分别构造。新定理 `gamma_one_weighted_same_prefix` 直接对该原生 Γ1 求和，允许任意旧权重，原来的两个系数都保留。

实际 U5 正源使用 `P2OriginalU5ExactNormalizedSource.sourceTest`，由原来的 `actualGoodMass_eq_sourceTest` 接到标记根。它对 `secondFunctionalMotherPrefixIndices`、每个 `secondFunctionalMotherGammaWords i` 和该词的 `rootLabels N t cs` 三层求和。17813c8 的 `sourceTest_eq_occurrences` 已把前两层逐字展平到 `originalMotherOccurrences`。0632f2e 中留下的 `emptyPairError` 正好在这个相同的列表上求和。该列表中的 Γ7、Γ8 两个两位置项在原 W2 的有效普通子查询中仍有各自的公式。本结论只处理上述有限 U5 源所使用的发生列表。

原生依赖固定于 `09b97db5764ade1246bfb77206baa1b124760958`。其 `SecondFunctionalMotherLabels.lean` 8–13 行给出下标 7 至 21，`SecondFunctionalMotherBandFormulas.lean` 6–22 行给出每个下标的完整列表，`SecondFunctionalMotherFinite.lean` 8–14 行已按原字典证明 $2\le |cs|$。下表直接按原词位置归类。同一个词在两个 Γ 下标出现时，两次均计。

| 词长 | 原 Γ 下标 | 发生次数 |
| --- | --- | ---: |
| 0 或 1 | 无 | 0 |
| 2 | 7、8 | 2 |
| 3 | 9 至 15 | 14 |
| 4 | 16 至 19 | 4 |
| 5 | 20 | 1 |
| 6 | 21 | 1 |

字典默认分支的值是空列表，它贡献零个词。`[0,0]` 则有两个颜色为 0 的素数位置。既有 `P2EnhancedOrderedReciprocalBudget.wordBudget_eq` 独立保留同一组发生次数，给出 $2X^2+14X^3+4X^4+X^5+X^6$。新证明从原生逐发生长度下界经 `List.mem_flatMap` 得到 `original_nil_count`。既有 `root_word_length` 在实际半开颜色过滤、端点或缺失素数的区间、以及商约束之后仍给出 `x.1.length = cs.length`。某色的重数可以为零。每个实际出现的标号仍至少有两个位置。空区间只会删掉不合要求的整数元组。

## 保留算子的完整整数与物理均值

原 `distribution-prime-product-completion-20261010.txt` 120–148 行的 (T) 在固定模数槽分组上恢复同一个系数。已标记部分原有的重数在外部标量，只有有序残余槽除阶乘。150–170 行的 (F) 分离几何变量。两式均没有重写 Γ 词表。固定原稿 `manuscript-body.tex` 258–316、451–469 行给出相同有符号系数、单独的物理支撑及小/粗素数附接。原筛模数树自身也保留空粗前缀，$d_{\rm rough}=1$ 的正号可接受小素数上侧系数。该正号来自 `actual-k-compilation-joint-audit.tex` 13–21、71–88、110–131 行。

设标记对 $t=(p_0,p_1)$，$d=p_0p_1$，正整数商 $n=x.2$。对保留代码允许的形式参数 `cs=[]`，`root_word_length` 强制 `x.1=[]`。完整整数因此是 $dn$，它仍服从原 `rootLabels N t []` 的 $n>0$、商素因子下界与 $dn<N$。保留的逐行算子为

$$
 \sum_{q\in \mathcal Q}\rho(q)
 \sum_{x\in\mathrm{rootLabels}(N,t,[])}
 \operatorname{smoothTrim}(T,dn)
 \left(\mathbf 1_{dn\equiv N\pmod q}
       -\frac{\mathbf 1_{(dn,q)=1}}{\varphi(q)}\right).
$$

`literal_nil_marked_kernel` 逐项核对这一式子。原列表对该算子的发生系数为 0，因此每个标记对的 `emptyPairError` 先消失，随后外权 $\sigma(t)$ 与完整模数和均可原封保留。`original_retained_eq_head` 直接由旧保留分解得到。原词有正长度且 $n=1$ 的商项，包括 Γ20/21 的单位商面，继续存在。此证明无需质数残词的 $r=N$ 分类、HB 单位对数槽、任何新终端估计或 $\Theta$ 的正下界。

## 接回已有付款

- 在 `physicalUpperModuli N nu epsilon retain cap` 上，原 full、rank $\le k$、rank $>k$ 三种系数都保留了自己的小素数附接，三个空词和分别精确为零。任一标记子族 $S$ 的 `selectedEmpty` 也为零，故 `selectedResidual = selectedGamma`，可同样用于补集。
- 在 153bb09 已有的低秩范围 $0<\kappa\le0.01,\ 0\le\nu\le1,\ 0\le\epsilon\le0.001$，现在原 Γ 误差本身满足原任意对数精度。
- 在 b538b42 的范围 $0<\kappa<1,\ 0\le\nu,\ \nu(k\,19/96+\epsilon)\le(1-\kappa)9/20$，同一原 Γ 误差也接回了 rank $\le k$ 的预算。原实际 compact 策略的 full 减原 rank $>k$ 余项满足原预算。所有阈值仍先于后选的系数、$k$（在可变秩声明中）和外权。超出该范围的分布及剩余高秩误差没有从这条恒等式获得估计。

## 复核与交付

分类上，稿内的 21 项分支和原生最小词长已经写明。将该事实接到后来的 `emptyPairError`、`emptyJointError` 以及物理和选族终端是缺失的有限推导。对这一明确的 Y18 减项无需新的分析前提。完整 P3.6 仍有实际 causal 同 $Q$ 覆盖及正质量、高级别系数和其余全源 (S)/(F) 等独立任务。

两份新文件的 SHA256 分别为 `5d5071bb93f3522db2747e820a7f70822252237356942acb0f314e4d9b53c79c`（Source）和 `b8bfd896626719d02ef5f0bc8a9013e8b13ae2ad9818cfcb7f98605661bf2c43`（Physical）。`REGISTRY.json` 收录每条新定理的行号、原稿与原生出处、字节哈希和状态。`IMPORTS.json` 锁定新模块的直接依赖，及历史组装提交 `f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784` 中递归可达的 335 份项目源码。其中 309 份在给定现行头 `3d15576a2eb00ba03deb3cf54f170c0a7f91c1f9` 同路径同字节，26 份来自已登记的历史分枝。外部依赖按原 manifest 固定。

静态核对发现 12 份历史模块在 13 处向 `List.mem_cons_self` 显式传了本应隐式的两个参数。`DEPENDENCY_API.patch` 为将来的独立导入映射提供这 13 处精确改写，各自的输入和输出哈希在 `IMPORTS.json`。原仓库与历史文件均未改写。新源码、导入和这份兼容改写都没有运行 Lean、Lake、LSP、stage、proofguard、数值或证书程序。送 T16 单独按承诺的字节复核，独立的结果记录在同级 `t16-empty-review`。
