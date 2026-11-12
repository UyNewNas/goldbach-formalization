# 真实矩形系数上的完整模数截频与局部支撑

五份源码接在十源 high-remainder-next 后。原 Q、c、β 与对齐 k 都和 Fine-density 相同；原十源和旧 attachedUpper 的截频实现保留原字节。新增数值文件为零。这里记录静态源码，尚待内核验收。

## 局部尺度与真实支撑

在一个含实际非零 integerProfile 的原 HB 互补纤维，整数坐标在原有序矩形上，首尾均按原单位/右闭 dyadic 所有者处理。同一纤维的标签 C 在看头整数、系数、模数和频率以前固定，x=U·lower(C)。真实 η 和双 ψ 给 N^(1−κ₀)/4≤x≤exp(1)N；旧 moving-residue 尺度定理给 exp(−1)x≤N≤x^(1+κ)。这一尺度比较对每个坐标成立，无须该坐标中选原 medium。

`P4BOriginalHighRankLocalLevel.eventually_live_level` 取 0<ζ≤1/400、0<κ≤ζ/10000 和 κ₀<κ/(4(1+κ))。原 Fine 实际支撑 d<N^(599/1000) 推出 d<x^Θ，其中 Θ=1199/2000。20ζ+Θ<1 和 40ζ+3Θ/2<1 同时成立。固定 1/2<b<1 后，`exists_direct_trim` 在任意预给正上限和 κ 下选择正 κ₀，并同时给出 κ₀<1、19/96<baseline b κ₀。物理半乘积门与 extra trim 均采用同一 κ₀。实数 κ 只控制局部 moving residue 与谱范围。

## 同一原系数的截频

`exists_complete_mass` 允许任意 S⊆Q 和原母的任意实际整数子集 I⊆rectangle；进入估计前只删除 c(d)=0 的模数，AP 与精确互素均值同步。每个剩余模数都从真实 Q 继承 squarefree、正性和 |c|≤1。用 D=⌊N^(.599)⌋，直接调用旧的 `actual_hb_mass_polylog` 与 `exists_uniform_exact_product_payment`。中心积=N 的项保留 D·τ(N)^h，其中 h≤12；由 .599<1 估计为 O(N)。共同常数在所有政策、β,k、宽度、模数、原组、HB 阶和整数前选定。

令 L=logScale(countingScale N)，F=paymentExponent 12 0。取预定分辨率 m(N)=⌊log N⌋ 和 s(N)=1/(m(N)+1)。`P4BOriginalHighRankPostModulusRow.H N A` 是 L^(A+15+24+F+3)。同一个 H 用于所有模数、两原标签、HB 阶、整数互补窗口及 β,k。24 支付实际混合导数造成的 s^(−24)，F 是已有完整模数矩的固定阶，15 支付原图表/标量的 14 与互补窗口的 1。`eventually_local_twists` 从同一 x 的 N≤x^(1+κ)、κ≤1 给出各保留实际频率 |ξᵢ|≤(log x)^(bandwidthOrder(A)+1)，阈值先于局部 x 与每个频率。

`exists_row_payment` 直接组合原 `exists_actual_upper_cube_tail`、`discrepancy_tail_le`、上述同系数矩以及原 `selected_cutoff_payment`。单位块没有被严格左端条件排除。对原整数子行的完整 Q 算术，单行误差至多 C N/L^(A+15+3)。`truncated_eq_band` 给有限频带上的真实原母振幅乘原 HB 算术，其积分使用同一 AP 与精确互素均值。

原 firstMedium 存在时，`exists_split_payment` 在真选择坐标用预定互补标签分块，付至 C N/L^(A+14+3)。一个子纤维若没有真实非零源点，用原完整整数和先付零，等价地可用十源的完整反演再付零；未将空蕴含逐频零。firstMedium 不存在时保留整母的完整原 no-medium 算术。随后 `exists_all_mother_payment` 用原 `groupEval_sub_le` 两次和 `sourceScalarMass_le`，在所有 chartBank N 2 标签和有序 HB 矩形上给出

    norm(modes(S,c) − band(S,c)) ≤ C N / L^(A+3).

这一步保留分互补支出的 log^39 恢复账。上述结果限定在写出的 m(N)；原十源全合法 s 的母振幅界 C L^14/s^24 继续独立有效。

## 正计数终端与实际欠项

`P4BOriginalHighRankPostModulusCount.exists_trimmed_RealB_le_band` 对充分大偶数给真正的

    RealB(b,N) ≤ X_s · physicalDensitySum(Q,c) + Re(band(wholeHigh,c)) + η H_N.

源同时给 X_s≥0 和 X_s/(N/log N) 距 log(1/b) 小于 η。共同 m,r,n,e,q,a，ω=νβ²、ell=νβ 与对齐 k 用于密度、支撑和主频带。外层 ζ 先控制局部许可，κ≤ζ/10000 后κ₀可按上式先选，m(N) 与 H(N,A) 是预选函数。Fine-density 的 .599 与 K 主项可用同一 β,k；此处没有重新选择 β,k 或额外支出 compiler/density 储备。

有限频带内原分布项仍待算术估计。其中包括低首 ≤μ 的真实全槽许可和标量恢复、分组 (T) 与全局碰撞 (C)、medium 的原槽辅助 SW 和完整绝对谱 7/32、no-medium 的真实一/两长槽及其精确均值。中心积=N 的 Fourier-tail 上界和原 (C) 中跨组重复素数的界是两个不同的费用。已有真实卷积/谱供应和相关缺口分别见十源报告及本包 REGISTRY.json。完整 PP、无余项的最终 RealB/K 和 1+1.7482 仍依赖有限频带主项。

原稿依据为 9731290e 的 completion §§1–4、§10，特别是 (S)、(F)、完整模数之后的截频及原局部层级条件。本包属于原稿内现有估计的实际调用补全。未运行 Lean、Lake、LSP、guard、数值验证或 CI。
