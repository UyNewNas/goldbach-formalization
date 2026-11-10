# G6 原第三回退增益独审

准予将本次冻结件按原始源码公布。新增原账第 6 项在同一扩大第五 bank、同一个实际第四及同一带符号物理系数上有完整的候选证明。T05 的 `exists_paid_density_and_count` 因此有 12/22 项源码依据。全 All22、P4A.4/P4A.5、最终 K 与实际分布估计仍待证明。

**原数值。** 已核对原 `third-prefix-fallback-pair-20261009.tex`、生成器文本、原 JSON、原独立复核及反馈汇编。实际档案的 196,731 字节与补充中的 `G6_ORIGINAL_WITNESS.json` 逐字节同源，SHA256 `0401062c690c7993fd34722dca97d3c504f3e72f83d87659f597d135490d50a5`。`Archive.Checked` 逐行绑定原位置、分支、三个网格索引、四角的最大新参数、16 项向上 log 与原 Q96 floor。原 `u²(1−v)` 的矩、正斜率与使用上端 `(1−w/2)w³` 的正分母齐全。每张 8×8×32 网格逐行核证，终端求和为 `3097012678584315027795429 / 2^96`。原稿备用子区 `15/2238884` 与其重叠，计账只用前一个值。闭 `decide` 的正确性仍待远端执行。

**物理积分。** 两支 `k=−3,1` 取 `x=μ+hu`、`s=μ+khuv`、`z=sw/2`、`y=s−z`。`Jacobian.derivative` 对实际 `Fin 3 → ℝ` 映射求导，`determinant` 给 `k h²u s/2`，`abs_det` 和 `chart_injOn` 在各开盒供给换元。故 Jacobian 中已有 `s/2` 及从 `(x,s,z)` 到 `(x,y,z)` 的单位行列式。`Slope.certified_derivative` 使用 `[2,4]` 上普通下筛 `log(q−1)/q` 的导数下界。`ChartIntegral.pointwise`/`estimator_mass` 得原系数 24 和逐盒有理下界。`Regions.unique_region` 以 `s` 在 `μ` 的两侧及同支逆坐标独立保证唯一性。连续有限和测试的每点至多一项非零，`PrimeTests.kernel_density` 乘上同一 `∏1/tᵢ` 后恢复 `4( f̄_new − f̄_old )/(xyz²)`。边界测试趋零或留在开域中；这里无需对同域增添另一份有序排列。

**因果与符号。** 原 G6 作用在 `μ<x<19/96`、`s=y+z`、`2v(x)−1<s<x`、`5/9≤2z/s≤1`。它保留原已通过的第三奇节点，替换其后的 lower residual。入射质量带负号，故原减新为 `g_N(p₁p₂p₃)(V⁻_new−V⁻_old)`。`Occurrence.row` 在真的 `beforeThirdPolicy` frontier 证明此式；非活动行两套 continuation 相等，旧拒收行贡献零，在活动行上用原第二、第三 guards 不交来恢复当前 `secondStage` 父。`original_increment` 保留 `List` 出现次数再按实际递减 prime tuples 重索引。原第二条带须 `y>2v(x)−1≥3/16`，这里 `y≤247/1728<3/16`，可将两项同时入账。

**有限选择与误差。** `Admission.exists_trim_admission` 在相同原数据上构造旧第一 label 的 firstStop、原第一及第三 cube、实际 coarse 第三激活、三素数的严格次序。`z≥5/96` 给统一正下界；用于残余和素数测试的盒为 `[1/32,19/96)`。`ActualGain.row_lower` 对全部实际命中行用同一个下筛均值误差阈值近似两 cap，在未修剪的完整求和中保留可能为负的有限 residual 差；非命中且测试为零的行通过精确恒等式处理。旧帽 `originalSeed≤v(x)` 的方向和普通下因子单调性提供所需下界。`exists_actual_gain` 先选测试修剪，再选足够小 `e` 与足够大 `q`，对每个 `a≤1/800` 最后取偶目标 eventual N；有限质量乘上两 cap 一致误差。局部 `cap=N`。

**终端。** `PaidDensity.replace_third` 在原 `beforeEight` 中用 `−G6` 替换 `+normalize(thirdIncrement)`，原第四积分、第五重新量化、第六改变量都仍在同一侧。对已有 11 项的 admission/order 只收紧 `e` 并增大 `qMin`，两次自由容差各得 `η/2`。最终计数直接调用既有 `P4AOriginalNewFifthPaidDensity.exists_paid_density_and_count`；该源使用整棵扩大树的普通端点并付一次 beta/完整 `u_c`。单列的 `exists_joined_positive_presieve` 没有被再次插入这一计数证明。相同 `r,n,a,e,q` 先于 `ν,βMax,β,τ,N`，原 `u_d/4` 也保持原位。最终 `physicalDensitySum`、`realPhysicalDistributionError` 和除数大函数均用同一 `moduli N w` 与 `rho`。后者仍是显式待估项，`q<N^(599/1000)` 是 support 上界，不能作为 L23 高秩分组许可。

**复核范围。** 作者 `G6_REGISTRY.json` 为 40,820 字节，SHA256 `29ff789b0cc68df1dcef055556d91116eef3b4676a207c4dbc51c459e05b28d5`，`G6_REPORT.md` 为 `637e6cc2de21ec2bc02b0063a617de68f2c724da337208031e7bdb35efea73ae`。复核了登记的 50 个本地引用（48 个唯一路径）、十份候选源的真实直接导入、三份版本化原稿本地字节与七个终端。`ActualGain` 的 SHA256 为 `bad6adecc9c900ac4e7cd791e0fe024a331821d07f8397302b1b2a3580bad109`，`PaidDensity` 为 `99a937917d86c48987b2f7e656a594e821a70686fa5952a3295227ccc072d0a0`。静态数学审查未发现需退回的 G6 原对象、符号、规格或预算错误。实际包仍有 elaboration、4096 行闭检查资源与 kernel 依赖风险。本次没有编译或重放数据。

远端复核须固定注册的 Lean、Mathlib、native 与先前 G3/full87 依赖，按直接图放置原 witness 到 Archive 源的同一目录。先验证 Archive 的解析、16 个切片和精确总和，再验 `row_eq_physical`、`original_increment`、`exists_actual_gain` 及三种 joined/paid 终端，保存精确类型与 `#print axioms`。当前保留 G1、G4、G7–G14、原 root/common 余项、剩余 `3u_d/4` 和同系数分布；无新增 kernel 已证状态。
