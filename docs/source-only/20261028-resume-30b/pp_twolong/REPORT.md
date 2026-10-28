# pp_twolong 第二批：连续模态质量与实际有限核重构

交付 `Part3TwoLongContinuousModeReconstruction.lean`。第一批源码 SHA 保持 `2fce2a53…750e26`，未作修改。第二批是闭合的局部必要步骤，未编译、正式信用 0；原任务完整口径仍 `task_complete=false`。

连续质量现在不再假设 N2 代价的可测性或可积性。代码先把 literal `secondJet` 的二阶导数恒等式延至零点：cutoff 和其导数在零点附近恒零。通过真实联合可测性及 Mathlib 参数 Bochner 积分得到 `t ↦ N2(twist t)` 强可测。再沿第一批已导出的实际二次频率界，证明任意 retained coordinate cube 上

`∫ |selectedAmplitude| N2(twist ξ_i) N2(twist ξ_j) ≤ C²(1+H)^4 ∫ |A|`。

只需 Fourier 振幅 A 的 L1 性和真实频率坐标约束；没有使用频率 cube 的体积，也没有把未知 N2 积分作为前提。

对每个实际整数长变量对，`modeIntegrand_integrable` 由短相位单位模、cutoff≤1 和 `|modeIntegrand|≤|A|` 自动提供积分性。`reconstructedProfile` 明确定义为同一个 selected amplitude 与两个 literal twists 的积分。随后 `reconstructedCore_eq_integral` 通过有限 residue kernel 求和及 Fubini，证明 AP count 与 exact `1/phi(q)` coprime mean 的同系数恒等式。`threeBrun_integral` 同时处理 upper/gap1/gap2 三份有限 Brun 系数；`sameRho_threeBrun_integral` 继续保留有限物理 signed rho。代码没有假设 `hUpperExact`、`hGapExact`、`hP2` 或最终 E4。

精确边界仍保留：实际 HB all-rank log-chart 的 A 与 Fourier inversion、原稿三份 upper/gap profile 及 smooth interval/strip witness 必须另行绑定。这里三个 Brun 核是明确 reconstructed profiles 的实际 count/mean；不能把其换序恒等式冒称原稿全部三核身份已经建立。原始 fixed-m P1/P2 也仍未供应，注册表明确列出支持 `[1/2,5/2]`、primitive a、q-independent alpha、exact mean、q=1、非互素 m 和 Brun scale 归一化的完整接口。short-product 的 M 因子在后续对 alpha_m 求和时产生，不加入逐固定 m 的 P2。

未发现新的原稿数学缺口。源码静态审阅范围、精确导入 SHA、必要步骤和剩余义务均见 `REGISTRY.json`；未执行编译、数值 checker 或额度检查。
