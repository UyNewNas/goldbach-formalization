# 原 HB 分组导数的复用范围

**T01 的 15 份源码可以按原身份复用。本次新增 Lean 为零，主表颜色维持。** 我核对了原稿两段、四份较新的 P3 源、15 份旧源及两次独审的五份记录。此判定只确认导数适用于哪些实际因子以及安装时该用哪些字节。

原稿 `9731290e` 的 prime-product completion §2 对每个原素数坐标分别作 order-three Heath–Brown 展开。每个展开变量只有一个原始组主。§4(F) 的 ψ 因子允许不同组尺度 R_i，输入是该组变量的乘积。原变量位置、同组多个变量以及重复求导方向均保留。若收缩到任意实际有限 occurrence 编号，J_i 就是 owner 的纤维。全乘积 η 同时依赖各轴，在已有乘积公式中另占一因子。

`actualPsi_eq_groupTensor` 对每个 U_a、R_i 为正时给出平移量 log(groupBase_i/R_i)。`groupLog_shift` 使某一方向只移动自己的组，`occWord_groupTensor` 因而给任意有序导数词的逐组次数 (w.map owner).count i。它允许重复的求导方向和空纤维，也允许各组的正尺度独立变化。真实组帽使用确定的实值 χ、ψ。复数 Fourier 端经过 `coordWord_euclideanLift` 和 `integral_norm_coordWord` 的线性嵌入及测度变换。T06 自身的 `childLog_iterated_ofReal`、`shiftedChildTensor_physical` 连到原复 child，物理平移是 log(U_a/2^label_a)。因此这一实际组帽计算已具全阶源。P3 的任意重叠子集与任意复 χ 有更宽的量词，`allocatedGroupJetSum_axisDeriv` 的一般公式仍只给一次求导。这不构成上述真实分组导数的欠项。

`occWord_four` 与 `occWord_refinedChart_exact` 保留不同因子的交叉导数。`exists_refined_fourier_budgets` 需要实际 Family、正 T、正 U 与 R、m≤6kStar，常数先于目标。具体上界质数对的 `exists_refinedUpper_fourier_width_budget` 使用 0<b≤1、正 κ、ν、r、width，2width≤baseline−νr，N>0，d≤12，正 U、R，给每个真实细 child 的 mixedD、物理 Fourier 衰减、积分范数与频率截断误差。这个具体出口消除了抽象 Family 前提。全部 atlas 的算术收缩、权重复原、模数相位和增大分辨率的总费用不能从单个 chart 推出。一般 W_T 的 mixedEuler 或 integrated class 仍须从实际 caller 取得。有任意 owner 的解析公式也没有独自把整个整数列表 atlas 重新编号并求和。

我在不可变 P3 树 a29bd6b4 和根快照 71b47b30 上用完整 Git blob 比对。P3 树持有 7/15。根快照持有 10/15，已含两份 T06 源及 P5AdmissibleAllRankIntegerGeometricFamily。其余五个有原历史登记和本地原字节，但不在该根快照中，分别为 P5GroupedOccurrenceLogShift、P5OccurrenceLeibnizAllocation、P5AllWordAmbientOccurrenceBound、P5GroupedAmbientOccurrenceChain、P5MixedEulerTwoStepLeibniz。机器记录逐项给出两棵树出现的路径、精确指纹及建议安装模块。它们是已恢复的旧依赖。未来安装还须解析全部导入，15 项名录只覆盖本次复用核对范围。

主表若说明 P3/PP 欠项，可注明实际分区组帽全阶公式已存在，尚欠的是未覆盖 caller 的原 W_T 与全 atlas、全 signed PP。原 P4A 密度结论及已有绿色数保持原裁定。本次没有执行 Lean、守卫、数值、CI 或远程写入。
