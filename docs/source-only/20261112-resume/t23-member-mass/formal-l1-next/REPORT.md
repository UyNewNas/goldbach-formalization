# T23 固定路径的 native 质量与外层算术归一化

本轮固定主镜像 4733b07d186b2b6aad89e5b9b782c35cc27ebd37、P5 原历史来源 001d139e667eb5cb42f1e9ca8f02de221b00db5c 及原手稿 9731290e8f53cffda44129906cde6a965eaa869b。七个文件均为未运行的 Lean 源候选。2026-11-12 首轮三份作者源及 T18 的原审单保持冻结。现存 Nov3 逐行统一银行/Buchstab 许可和 Nov6 原实际物理 trim 精确为零继续由旧源码给出。

## 全路径上已落入候选源码的结论

1. **连续物理密度。** 任取真实两种根之一、固定至多 440 步的 shape、mesh、末端 extreme/open/singleton atom。同一 native 图以一个实根坐标及各步真正的零、一、二个新素数坐标作积分变量。令 I 和 S_n 分别为理想与 finiteTau n 冻结完整 QueryMember，W、V_n 为实现后物理密度。NativeMovingDensity 先从完整 Member 中推出每条已接纳的路径所有 word 坐标至少 b = min(1,a,F/6)，F = (11/384)/101^440。理由是最终残量至少 F，每个已接纳前缀残量不小于终值，每个新坐标至少为当时残量的六分之一。字长至多 881，故词乘积至少 b^881，两侧各自在自己的实际集合上一致有界于 K = 4/(F b^881)。原根带及这些 Member 的全部 native 积分点都在源码所取有限闭盒 B 内。
2. **移动冻结集合上的真正绝对 L1。** all_shapes_frozen_density_L1 给出 ∫_B 1_{S_n}|W−V_n| → 0，包含 S_n 中理想路径未接纳的点。原 R15 的逐点残量扰动现在拥有从完整 Member 导出的统一前因子，绝对率为 r_n = (4/b^881) levelError(n,finiteTau n)/F²。all_shapes_integral_bound 给出两侧各自延零后 ∫_B |1_I W−1_{S_n}V_n| ≤ r_n vol(B) + K vol(B∩(I△S_n))。两个集合都是完整图上的原递归 Member 加末端 atom，二者在同一坐标中独立取值。对含活动步的任意混合路径，本轮只在该式左边的物理密度部分给出无条件趋零。
3. **继承/固定路径的完整 L1。** InheritedMemberL1 的 inherited_full_native_L1 允许任意长度的 retain、transport、W1Fixed、W2Fixed 混排，任意实际固定 Program、各槽常量、原两种根和两种极性全部 401 原子。此时唯一独立 native 变量是根 t。每个根常数门的理想等值集合在 clamp 外可由三个 t 覆盖，clamp 上原、冻结查询一直相等。固定查询原样重设，retain 原样继承。父上界 L/c≤C 即使取等号也在向下降低 L 时成立，失败点由残量收敛最终仍失败。由上述事实逐原递归门得到 a.e. eventual QueryMember 等价，以实际物理根密度的统一包络做 DCT。两边都真实延零，使用相同 t。
4. **活动查询的联合积测度。** NativePrefixFubini 将已审 NativeProperSections 的五类原查询非零斜率和截面单点公式用于原 nativeProgram 的任意深度已实现前缀。joint_active_null、joint_strip_L1 对任意 σ 有限前缀测度及可积联合测试密度给出完整闭管的绝对 L1 消失。actual_prefix_strip_L1 给出源/冻结前缀实例，actual_prefix_pair_strip_L1 把 W2 较小素数独立加入积空间，仅在较大素数切片；所以较小坐标和全部前缀同时积分。它们计算的是给定父状态下五类活动查询的闭带，并未把继承常数面拿去作单点零集。

## 真实算术外层

1. **原所有 owner、全部几何 Member。** OwnedPrimeBoxWeight 从原 Valid 的 CutoffFits、最后 argument≤6、F≤L 以及完整 path 的 ceiling 不超过字中每一坐标，推出每个实际字母 p≥N^(F/6)，这个下界趋于无穷。真 Θ/H_N 的乘积中，同一素数第一次和再次出现有各自的 localPrimeFactor。与 actualPrimeBoxTestSum 的真实因子 ∏1/(p_i−1) 比较给出逐项绝对界，统一率为 (1+4/N^(F/6))^881−1 → 0。primeBoxWord_ofFn 接到原 Fin r 素数盒。没有平方自由或排序后去重前提。
2. **按有序算术字的一次归一化。** AbsoluteWordBox 的 uniform_wordBox_normalization 对任意预先固定的正素数盒、固定字秩、给定 ε，给出单一 T。对每个偶数 N≥T，预算同时覆盖原两个根、细精度 n、m、mesh、允许的 tau 和随 N 变的 |w|≤1。对每个盒内有序字 v，直接在它自己的 keyAt(N,n,m,k,tau,v₀) 上试验是否存在实际 owned member。存在时累加 |Θ/H_N−(4/L)∏1/(v_i−1)|，不存在时为零。源中用真正的 actualPrimeBoxMass 总量界及 literalScale→1，故容许 w 不连续并且随 N 变化。同一字只一次。此结果支付算术前因子的差；更改所测试的 Member 或 winner 还会产生另一个误差项。
3. **已发射位置的重数和外层预算。** EmittedPathMultiplicity 证明 history 映到真实 (edgeShape,prime₀,prime₁) 路径后无重。每个父只执行自身 resolve 所选的分支，故 retained 的 cell 索引即使在几何形状中消失，仍无兄弟重号。W1/W2 和 Buchstab 各自来自去重的 Finset.toList，W2 不同 component 的自然标签也保持独立。实际 fibreMark 的位置权之和至多一。EmittedWordBox 再把固定形状和原有序整数词解回上述路径，在 W2 中明确将原 word 的 [大,小] 解至 (小,大) 的物理坐标。actual_shape_word_mark 给出按 o.current.old 筛选原 occurrence 列表后系数绝对值≤1。emitted_owned_word 复用 rootHistory 的 pathCode、pathPrimes、Member、realization，保留原 root tag、root prime 和 keyAt 并给出完整 owned 几何字典见证。uniform_emitted_box 将真正的位置系数接到同一 ∑|w|·|Θ/H_N−box| 的外层预算，允许另乘任意有界字标记。原动作符号及同一乘积上的不同有序字没有并掉。

## 剩余的接口

- 对任意活动路径，R14 的 changed_QueryMember_strip 是在共同已接纳前缀上递归的析取，其中既有当前 fresh 坐标的单点截面，也有只依赖父 query 的 gate、只依赖较小 W2 坐标的 rows 以及结构常数/上界。NativePrefixFubini 的解耦图参数是固定前缀 × 最后活动实数（pair 增加一实数）。要把混合路径的 vol(I△S_n) 化为趋零，尚需沿原 nativeSlot 的时间次序把各个最先变化的原 gate 分别搬到对应的积图，处理 frozen index n 所改变的父态和此前的接纳，并把零 arity 的结构稳定性归纳拼接进该图。R14 的 changed-row 集合可包含弱上界恰取等号的点，单纯把其整个闭带当作可删的严格面没有许可。上一轮纸证与反例继续有效。本轮没有把 vol(I△S_n)→0 放进任何宣称无条件全 L1 的定理前提。
- 原实素数盒 ContinuousOn 的极限定理不能直接用于这些变动的指示函数。将连续几何比较传给算术 Θ/H_N 的原两层量词还需固定理想图的 proper-frontier 小积分连续外包、其补集上的一致签名稳定，或对每个固定 n 完成 Jordan 延拓后再取外层 n 极限。这里给出的 uniform_emitted_box 有算术前因子误差所需的真实 T，未向几何集变动或整个 count source 推广。
- 当目的是同一固定形状的真实 emitted 列表时，本轮给出位置总系数≤1。原 receipt 中每个 q 的计数、银行 base 与 adopted whole-source 身份、不同形状的总重、430+11 同一因果实现继续保留各自独立条件。已经在冻结 REPORT 的 .transport 194 附近出现的集中字族仍可使相对自身 Θ 的相对误差达到 1。没有把变化 marks 的自归一律补进原稿。

## 验证边界

静态比对原来源、定理形状、积分域、误差量词和 SHA。未运行 Lean、Lake、LSP、proof guard、数值 producer 或证书，没有增加 kernel credit。正式范围以 T18 本轮单独签发的审单为准。

