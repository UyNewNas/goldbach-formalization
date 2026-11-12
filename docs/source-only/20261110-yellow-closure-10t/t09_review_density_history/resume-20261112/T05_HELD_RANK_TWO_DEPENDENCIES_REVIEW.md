# 旧六个 helper 在实际双素数付款中的用途

**裁定。** 原 rank2-global 的数学范围维持，但旧六件不能凭内容定位列为已编译、已可安装，也不能凭 `complete_module=false` 推出粗秩二的真实 W 识别缺失。直接双素数差与移交两张原 atlas 使用不同的入口。在原选择表中，从 `P2GammaPrimeLocalConductorSaving` 追溯的 266 个 ImbalancedChen 模块没有碰到这六件；整个 `P4BOriginalRankTwoSampleConductor` 的导入树有 1730 个可定位模块及这六条旧边。前一计数说明导子原语的依赖，后一计数说明 Lean 安装整个文件的依赖。二者都不是完整 CI 验收。

**真正使用的截断。** `P4BOriginalRestrictedAtlasProper.eventually_subset_atlases` 通过 `P4BActualUpperRoughPrimeReserveZero.exists_actual_upper_roughPrimeReserve_zero` 实际调用旧 IndependentTestPrimeChartUniformCutoff 的 `independent_test_chart_cutoff_eventual`。对于一个带原 ψ 的非零双素数项，实际 Fin 2 廓形给每个素数 p 的 N^(19/96)<p≤N；chart 的非零项给同一位的 R_j/2≤p≤2R_j 及非零 ψ。零项直接消失。以固定 K≥2 和正 a=19/96 选择共同 N₀，然后处理任何原宽度、标签、素数词、Q 和 ρ。旧尺度引理 `active_psi_scale_each` 是 Forall₂ 列表的直接同位比较；正尺度 argument 至少 N^a/2，至多 2^(8K+2)N^K。旧解析 `eventually_subpower_envelope` 将 rough cutoff 压到 N^a 之下，完整两素数词的 roughWord 因而等于 1。没有以未给出的 W 身份为假设。旧 cutoff 后文的 `independent_group_selected_W_atom_eventual` 属于另一条几何/模数原子识别路线，完全没有用于上述推论。相反，如果不接实际原双素数 floor、ψ 窗和 cap，这一泛截断本身不能独自支付 rough reserve。

**秩二与秩四。** 前三个旧模块分别给四坐标候选的光滑零延拓、原四维盒范数、以及真正需要绑定数据的 OriginalFourSelectedSmoothWBinding；第四模块给出现坐标的微分分配和乘积规则。经 NativeSelectedFourIntegerProfile、NativeSelectedFourOrderedEuler 等文件引入这些名称，并不把四元数据强制转换为双元数据。`P4BArbitraryWidthUpperPairProfile.profile` 在 Fin 2 的正正交域上明确用 `smoothPrimeVariableProfile`、外域零延拓；`actual_original_caller` 在原标记素数上辨认它，`licence` 从自身的光滑性与实际值构造。粗秩二的 head 变差和两次局部导子界也没有把四元 mixed-jet 或 selected-W 条件挪进 caller。四元完整 W 的历史 hold 原样保留，与本次 Fin 2 付款分开。

**精确互素均值。** MellinExactMeanInsertion 在 `P5IndependentPrimeSourceWordDictionary` 这条物理路径上只用到 `functional`、`residueKernel`、`exactDiscrepancy` 三个有限定义。核等于同余指示减 `1_(gcd=1)/φ(q)`；真实词保留原标记、乘积、同一 Q 和带符号 ρ。这里不调用 Mellin 积分估计，也不要求把两张表分别取绝对值。粗秩二的素数差照旧无需对全模数额外假设；升到合计 atlas 的终端照旧需同物理非零系数的 599/1000 支撑和此前已供的真幂处理。粗秩至少三及完整 PP 未付。

**原件的形式问题。** 原 cutoff 源 80344489… 的 :197 将 Real.rpow_mul 用于错误方向。锁定 mathlib e4c91783… 的 Real.lean:414 为 x^(y*z)=(x^y)^z；欲合并嵌套幂须反向使用，先明确把自然幂改写成实数幂。在 :93–99 上界还须把 js.length=k 写入乘积估计，再同乘首因子；在 :145–148 下界要显式处理乘法结合。这些都是 :208 的真实 proof-body 路径；相应的等式/不等式在既定参数下成立。其他部位的乘法括号、有限和除法和 grouped_local_x_floor:293 的交换次序影响整模块形式安装，不是这条数学归约的新假设。除此之外，确切的更深一层旧四元模块 e3280f5e… :175–178 自身也有一处未采用正确幂方向的四元定理；秩二用该文件的 :22，并不用该条 :175。这一项与六件的原始 ready=false、尚未闭合的完整导入图分别保留。此报告以历史原件为对象；后继修订只在独立选本中验收。

核了六个原件与十四个已定版消费者/供应者的字节身份，逐条核了原稿对象和相关声明调用，未执行本地 Lean、guard、数值或 CI。机器清单仅供发布本次独审记录；没有批准把六个历史原件直接装入生产 driver。
