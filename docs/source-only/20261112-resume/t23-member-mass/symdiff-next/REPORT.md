# T23 · 原生混合 Member 的对称差与双侧物理积分

固定原始根 $k=U_3,U_4$、原 Program 网格、含任意原动作的完整 shape 字、上下表极性及原 401 个原子之一。用同一原生向量 $x$ 生成两侧的根坐标、每个动作实际读取的零至两个素因子坐标、每个 cell 和整个递归 Program。理想侧从 `sourceRoot k 0` 出发，冻结侧从 `frozenRoot n k (finiteTau n)` 出发。五份新增 Lean 源给出

* 两个完整 `QueryMember` 在根带内对几乎处处的 $x$ 最终同真同假。
* 在 $B=[0,1]^{\mathrm{NativeSlot}}\cap\{t\in\mathrm{rootBand}(k)\}$ 内，普通实测度 $\operatorname{vol}(B\cap(I\triangle S_n))\to0$。
* 深度至多 440 时，两侧真物理权重各自在自己的完整 Member 上延零，足够细时均可积，且 $\int_B|1_IW-1_{S_n}W_n|\to0$。
* 每个固定 Program 网格和正误差下，深度 0 至 440、每个深度全部 shape 字、两根、两极性及全部 401 原子可共用一个冻结精度下界。这个下界控制上述两个连续误差。

## 原坐标、活动行和等号

`Part5OriginalH430FreshAxis.avoid_graph` 在原乘积坐标上选一个真正读取的坐标，使用保测的子类型乘积分解和 Fubini。其余坐标固定后，该方向上的单点等式为零测。`active_avoids` 直接调用上一轮固定的 `query_knot_comparisons` 和 `section_zero_iff`，覆盖 W1、W2 单点、W2 有序双点和上下 Buchstab。W2 双点先固定较小坐标，再对较大坐标积分。五类都保留原父残量和原查询分母。

`Part5OriginalH430MixedGateStability.local_stable` 使用 R14 的 `localDomain_iff_rows` 及其完整 `localRows`。由同一新坐标排除 $z_j=cL$、$z_0=L/s$ 或 $z_1=L-2z_0$，其中系数直接取该动作原端点。固定读数、相同 ceiling 和 cell 条件两边相同。弱 cap 行 $L/c\le C$ 在正 $c$ 的等号处用 $L_n\le L$ 保留；其余符号由正残量和收敛给出。父参数与每个阈值同时保留两个方向的弱比较，因此上下表离散结点的等号判定也保留。

`Part5OriginalH430MixedNativeWalk.walk` 在原 `Member` 的递归定义上归纳，复用 R14 首个门分歧的原行、实际 `advance`、`Member` 和终端 `QueryMember`。归纳守卫仅要求理想父路径此前各 `LocalDomain` 成立。如果该步理想门失败，冻结方最终也在该步失败；如果成功，则对子状态继续归纳。每一层均证明实际父状态对尚未读取的坐标独立。retain 继承已有符号，固定 W1/W2 和 transport 写入同一固定值，根 clamp 由原 `ideal_clamp_preserved` 全精度精确保留。根非钳位的真等号只用 `proper_root_fibre` 给出的三个一维点支付。整个证明不要求预先有一侧全程通过，也不把整条等号层删去。

## 终端和量词

第四个模块的 `full_program_eventually` 适用于固定字上任意共享的 cell 选取函数，特别包括原生 canonical Program。`nativeSet_eventually` 使用固定源中实际的 `nativeSet`；`mixed_difference_volume` 在原区域的有限体积上用被 1 支配的指标做 DCT。`fine_extended_integrable` 用已经固定的单侧物理权重界证明两边可积。`mixed_full_native_L1` 将对称差结论接入已审 `all_shapes_integral_bound`，使用原来的 `rate_tendsto`、残量下界和乘积下界。`finite_mixed_native_threshold` 对每个依赖的有限索引取共同最终事件。没有额外的零边界质量、同余归一化、全程成功或误差趋零前提。

`shared_owner_difference` 允许两侧同取任意 $O_n$，以上述全域普通体积控制 $(B\cap(I\triangle S_n))\cap O_n$ 的绝对体积。这只给共享限制的结论。跨图 owner 对应、随整数变化的原子计数权、带 adopted mark 的算术筛变、430+11 的联合实现和完整 Y24/H34 仍待独立证明。冻结精度是 $n$，此处未产出算术参数 $N$ 的阈值。

指定完整 Program 的结论直接使用原 cell 所有权。第五个模块从原 cellMember_unique 沿整个已通过的 Member 递归证明 canonicalProgram 的每对 cell 等于给定 code，得到 fixedSet_eq。它将固定 Program 的原 QueryMember 精确识别为 canonical Member 与该 code 的所有权纤维之交。fixed_density 在两侧把权重识别为给定 code 的原 realize 物理权。fixedSet_measurable 和 fixed_fine_integrable 给出可测与足够细时可积，all_fixed_program_threshold 给出所有真实 Program（含全部不同 cell）的双侧完整 L1、对称差体积同一阈值。空域也在量词之内。

## 核验状态

本轮是 source-only，未运行 Lean、Lake、LSP、proof guard、数值 producer 或 CI，未取得 kernel credit。五份源的 SHA-256、行数、公开定理和所依赖的历史 Git blob 见同目录 REGISTRY；先前两轮的作者材料和审签维持原冻结字节。相同根、相同 slot、相同方向和原等号处理是本轮独审的核心范围。
