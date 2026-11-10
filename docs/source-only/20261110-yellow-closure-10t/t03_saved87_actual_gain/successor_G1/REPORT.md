# 原 G1 的普通筛导数表、逐盒积分与同一第四层积分

原稿的 G1 是 `10601625247768616959055 / 2^78`。本包的两个末端是 `P1OriginalFourthCofinalGain.exists_cofinal_original_fourth_gain` 与 `exists_cofinal_union_fourth_gain`。对每个 `epsilon > 0`，存在一个 `e0 > 0`，对每个有理数 `0 < e < e0`、每个 `0 < omega ≤ 3/200` 及任意既定 `mMin, qMin`，存在 `q0 ≥ qMin`，使所有 `q ≥ q0` 满足 `mMin ≤ refinedMesh q` 及

```text
currentUpperEighteenGains 0 - epsilon
  < originalFourthIntegral (P4AOriginalNewFifthUnion.original e q omega)
```

第二个末端对 `P4AOriginalNewFifthUnion.data e q omega` 给出同一不等式。新增第五层的构造保留此前的第四层字段。T05 的 `beforeEight` 以负号扣除第一个末端的这个积分。误差 `epsilon` 随这次扣除支出一次。这里的量词顺序允许原有的精度、粗筛阈值和粗网格要求同时成立，并且先于目标 N。十二个新增 Lean 文件共 80,741 字节。作者与 T09 完成了这些源文件的数学审读。有限证明、elaboration、kernel 与 axiom readback 均待远端。

## 8193 个原端点

原稿 `fourth-prefix-stronger-refinement.tex` 从 `eq:fourth-stronger-target` 到 “A positive derivative numerator through argument five” 指定普通归一化 `upper = suzukiContinuousUpperFactor/(2 exp γ)`。从原 delay equation 取 `H(s)=s upper(s)`，在 `1<s≤3` 有 H=1，在 `3≤s≤5` 有 `H(s)=1+∫₃ˢlog(t−2)/(t−1) dt`。在 3 左侧连续补零的 integrand 给出真正双侧的 `H′(3)=0`。由此得到 `−s² upper′(s)=H(s)−s log(s−2)/(s−1)`。已有的 `q_monotone` 给出上下 Darboux 夹界，也给出 `N` 在本区间单调不增。此处使用的已有 Q80/JTable 引理是 `q(v)=log(v−1)/v` 的单调性和奇次幂对数余项不等式。G1 中出现的函数始终是普通 Suzuki 上筛函数。

程序 `certify_fourth_prefix_stronger.py` 的 `log_bounds` 与 `derivative_table` 保留 m=4096、Q=2^80、24 个逐项向下取整的对数项、尾项分母 49 及 j=0 的精确零上界。累计和以 Q 起步，先验证当前存档数加上向上取整的惩罚等于累计 credit，再加入这一格向下取整的左 Darboux 项。每一格的真实积分夹界分别证明了这两步的方向。旧源 `P1OriginalFourthRawTableMetadata.lean` 的 8193 个顺序十进制 token 已逐项与原 JSON 字符串比对。首项为 1208925819614629174706176，末项为 39643994026485390435670。核对过程只读取文本。

`P1OriginalFourthN8193.original_all_endpoints (j : Fin 8193)` 对原表的每个 j 给出存档数除以 Q 小于等于真实 `−s_j² deriv upper s_j`，没有调用方输入。末项给出 `original_N5_pos`。对向上取整的原端点，`original_ceiling_lookup` 适用于整个前面的真实参数区间。证明从上述真实解析推导与闭合的原整数递推两部分相接。旧源中的列表、parser 与 SHA 单独只能定位输入。

## 每个原盒的四次 Q80 取整

原稿 “Correlated affine bounds”“Four positive subintervals of the cap difference” 与 “Integer implementation and independent finite geometry” 指定同一行的旧六分量包络 L、新选定子积端点 M、S=x+y+z+w 和相关剩余量 R₀、R₁。代码沿用原 `integerDelta`、`integerR0`、`integerR1` 与原生产程序的 old-piece 编号转换。第 k 段从该行的下端 w 和真实右插值端点取得精确的非负上取整索引。四次积分使用 `upper(s)−credit/s` 的导数符号。相邻真实筛函数差抵消，留下

```text
4 (M−L)/(x y z w) · Σ credit(k)/(4 R_left(k) R_right(k))
  ≤ 4 [upper((L−S)/w)−upper((M−S)/w)]/(x y z w²).
```

该式包括 R₀=R₁ 的情形。原第四坐标的一次抵消给出左边的 w 次数。对原 17 字节记录和该记录闭盒中的 t，`original_row_density` 自动生成四个索引。

每个旧分量按原整数中点挑一个仿射上片，平局挑第一个。十六个角点用真实两分量新帐篷减去所选旧片的最大值。每种角点的乘积重心权具有恰好 `volume/16` 的积分，仿射片精确重构。每个角点差均在每个 “新片减所选旧片” 之下，这给出全盒的真实 gap 积分下界。`original_average_gap` 在向下取整的十六角均值和单独导出的全盒相关下界之间取最大值。全盒 (M>L) 来自单独的有符号几何检查。

记整数坐标格 `n=204800`，仿射格 `D=6553600`。四次 `unitExpr` 分别向下取整。物理宽度比为 `∏(hi−lo)/∏hi`，平均 gap 为 d/D，插值分母为 `A_j/(4D)` 和 `B_j/(4D)`。约去四个坐标尺度得到原式 `16 D d (∏ widths) n_k / ((∏ hi) A_j B_j)`。每次取整后才合并。求和时用相同的 8193 个原数建只读数组。全行总和 guard 的输入是原 loader 的实际 decoder 与原 62,885,159 字节，并在解析失败时返回 false。`adopted_gain_le_sum_limiting_row_integrals` 左侧为发布的 G1，右侧为所有原始出现次数的真实原盒积分之和。

## 同一棵第四层树

`P1OriginalFourthGuillotine` 在 16 位坐标立方体中按轴中点分开实际原记录。当左右行可能沿某轴相交时该轴不可切。每次成功分隔都给出一侧 `hi≤mid`、另一侧 `mid≤lo`。采用真实半开盒后这两个集合严格不相交。最多 64 层涵盖四个 16 位坐标。旧程序先分到各个 1024 单位的根盒，再执行同类的分隔。新检查从同一绝对坐标系的共同根向下，每层验所有经过的行。原程序报告的 9963 个根与 7607322 个访问节点是历史记录，证明使用新检查的实际分隔与全原行列表。

`P1OriginalFourthTrimmedLimit` 采用共同内缩宽度 `1/(n+1)` 和共同缓冲 `min(commonMargin/4, 1/(n+1))`。每个原盒的坐标边界为零测，几乎处处最终被内缩盒覆盖。正号的真实缓冲密度受同一盒上可积的无缓冲密度支配。普通上筛函数在法定参数处连续，给出 M−2b 趋于 M 的极限。没有把负的有符号变动换成正部。积分的实际归一化由 `(2 exp(−γ))·(2 exp γ)=4` 得到。

T02 的共同历史在各内缩盒上构造实际 active label 和原 first-stop、third own cube 许可。该 label 上有真实旧 `Gamma≤L`，相同历史上的新最大值包含 M−2e。方向与原上筛的反单调性相合。所有实际 active branches 均有原来的非负可积主函数。在每个 t 上，半开原盒至多有一个测试值非零，且它被一个真实 label 的分支核控制。对其余分支使用已有非负性，积分后得到原 `fullActiveIntegral`。这支付了 T05 的 `originalFourthIntegral`，另一项 common fourth requantization 仍单独进入后续账目。

## 原件、依赖与审查

原稿和软件的 `9731290e` 与 `ba6ec11d` 版本整棵树为 `4df4763ce4d22730fb3c30b816244e9c51c04a19`。原 NPZ、原表 JSON、程序、结果及原 17 字节 wire 的实测 SHA/大小均列在随附 REGISTRY。T02 的六件包和 T05 的第五层联合构造保留其既有指纹。旧 `P1OriginalFourthRawTableMetadata.lean` 是额外必需的源输入，须安装到 `ImbalancedChen/P1OriginalFourthRawTableMetadata.lean`，其中已有的节点序列无需另写。原数据 wire 复用已发布的 `dbdbb0303f866afd17698c40b1c4d413beb7ca79`，安装位置是源 loader 同目录下的 `provenance/original-fourth/FourthRows17LE.bin`。本包没有新增二进制或数值数据。与原 full87 和 T01 v3 两份安装清单相接后，额外导入的 19 个旧模块中，18 个生产模块的完整路径和字节均已在提交 `6848b4a` 中找到；余下一件是上述原始 metadata。增量所涉及的 14 个外部 import 在 T01 固定的完整 Mathlib 与 native 包树中均有精确路径。若以后用改动了先前三层实际决策的另一棵树，需重新建立该树与当前第四层积分的关系。

对应原稿的缺步是可补的解析推导、原行数值与实际几何及同一历史积分的组装。旧核对此前只能支持其中若干定义与单行一向许可。原论文中的精确式和下界方向可由上面的源候选推出，静态审读未发现实质数值矛盾。源文件未改已有声明，没有新增目标等价假设。T09 对首五源的审查是 `G1_DERIVATIVE_AND_FOUR_QUARTER_REVIEW.md`，SHA256 `f0e46dce14f87c10858e350c0c7be636876087181faba1d89de5257ebb49d103`，对后七源的审查是 `G1_FULL_ARCHIVE_COFINAL_GAIN_REVIEW.md`，SHA256 `2513902c5435b1ee974ddd5e382ce960a0281c4587e7ebe80aa649c55374a38f`。

远端仍须核对精确声明类型、axiom、原 8193 项整数循环、T02 的全行几何检查、四段分别向下取整后的总和以及全行 guillotine。后面三个 guard 均涉及 3699127 个原记录，资源可行性尚未实测。此处没有运行 Lean、Lake、LSP、检查器、数值回放或 CI。其余 G4/G7–G14 所属的第六层项、common fourth 修正、相同系数的分布误差与最终 K 还需要各自的账目。
