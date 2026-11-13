# 原 singleton 单长槽四份基础源码独立审查

**结论** 允许在有限恒等式、原模数系数、有序短元纤维和实际一变量 profile 全轴定量界的范围内按源码归档。整支原单长槽的渐近估计为 HOLD。本文审查的是冻结的四份 Lean 文本以及作者文件清单，未执行 Lean、Lake、LSP 或证明辅助程序。核验状态为 source-only，kernel 未验，formal credit 为 0。

## 已核的源码范围

- **原模数和移动剩余类。** `physical_data` 对原 `live P` 给出 $0<q\le\lfloor N^{599/1000}\rfloor$、$\gcd(N,q)=1$ 与系数模至多 1。`physical_read_live` 对任意复测试给出去零的精确恒等式。`free_data` 在同一上界与同一互素条件下对 `products P` 给出 $J_0(\omega)!$ 的界，其证明保留原记录及重数。该界在先固定 $\omega$ 后统一。两个通道以完整模数为自变量。图核的同一个系数乘在 $b\equiv N\pmod q$ 的计数项及带 $1/\varphi(q)$ 的精确互素均值上。
- **原图中的有限行。** `OneLong` 要求原 `firstMedium = none` 且 `longBlocks.length = 1`。`noMedium_exact_partition` 把这个实际子和及其余项归还原和。`source_to_actual_rectangles` 针对单标签 `[cj]`、任意原 `Q,rho`、相同 `N,K` 及 $2N$ cap，把真子和精确改写为有原符号和标量的有序 HB 行。$B=6$、$\mathrm{kap0}=\mathrm{kap}$ 与两个原模数选择由通道定义保留。原分母是整个组的对数。长 Möbius 归零的逐项引理需要截断 $y<\operatorname{lower}(b_a)$。从所有活原图得到这一条件的共同阈值仍在终端接线范围内。
- **每一个短元纤维。** `restrict` 与 `insert` 就选定位置互逆。`sum_rectangle_short_fibres` 与带 cap 的版本逐有序短元列求和，重复块标记及乘积相同的不同短元均保留。正的短积 $m$ 给出精确长区间 $U<n\le\min(2U,\lfloor2N/m\rfloor)$，空区间取宽 0。`short_card` 计原有序盒的总列数。`actual_width_sum_le_twoN` 在一张有原几何非零点的块图上，从 `scalarProfile_support` 得到总宽 $\le2N$，逐纤维没有模数依赖。把未选定位置的维度上界与 `OneLong`、原阈值合为全图估计仍须接线。
- **严格 rough mask 和 profile。** `actual_long_profile` 给出长角色 one/log 在 $U<n\le2U$ 上的精确整数值，原 `roughOneSlot` 原样保留。$\psi(b/R)$、complete trim、分辨率为 6 的实际 `ambient`、完整组整数的 reciprocal-log、长角色的可选 $\log n$ 都在规定的位置。固定延拓 $\eta(2v)\chi(v/2)$ 在闭区间 $[1,2]$ 为 1、外支撑在 $[1/2,4]$。$\mu$ 的逐项结论覆盖块系数可能相消的情况。
- **定量全轴界。** `realProfile_uniform_euler` 在 `complete_chart_word_budget` 中取同一实际参数、rank 1、单坐标和两个导数词 `[]`、`[0]`。中心 $t_0=\tfrac12\log 2$ 位于原 plateau 的内部。在原尺度 $X$ 固定 $U_s=Xe^{-t_0}$ 后，沿坐标的小平移恢复 $X e^t$。这给出原 profile 及其 Euler 一阶导数的 $\log(N+2)^{12B}$ 上界。`longProfile_uniform_C1` 取 $N,m,U>0,\ U\le 2N$，在全实轴控制函数模与普通导数模之和，常数在所有 $\mathrm{kap},N,c_j,\mathrm{kap0},m,U,\mathrm{useLog},v$ 之前选定。它只对固定 cutoff 使用紧性。因 $v\ge1/2$ 且活区 $Uv\le8N$，长对数及导数合计至多另加一次 log。所得右侧为 $C_B(1+\log(8N+8))^{12B+1}$，原 $B=6$ 时指数为 73。

## 尚待证明

完整 E5 估计要求在此实际有限行上把核连到 `profileError`，按真实 rough 集合与宽度施用 `actual_chart_one_long_finite`，并用同一阈值恢复全部短列、块图及母图。上述四源没有这条终端声明。若沿此固定 polylog 次数继续，短系数、模数和全集图恢复费用还须共同结算。原 comparisonMiddle、savingMiddle、完整的最终矩形中段及 whole PP 均未付款。本包不改变颜色或主证明状态。

## 冻结证据

作者 REGISTRY 的 SHA-256 为 `e9bb01bc30e358a8de7c7f60181c2727991212091c568e04c851e421f4de06e9`，FREEZE 的 SHA-256 为 `864a103c11a62b085ed07e101cf177562b41fd21f2d5b9712cc1471bd78a6f6c`。独立重算清单内 9 个文件、REGISTRY 及 FREEZE 的字节数、SHA-256 和 Git blob SHA-1。四份 Lean 共 46,328 字节。另以静态读取核对 38 条依赖或原文定位与其历史清单的指纹。旧依赖仅定位。

