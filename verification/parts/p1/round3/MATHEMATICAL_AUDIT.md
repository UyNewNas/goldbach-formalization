# P1 round 3：历史第五层构造的数学边界审计

## 1. 审计身份与结论

这是下列三个**指定源码版本的只读语义审计**。审计期间没有修改源码、运行 Lean、运行 checker 或替代实际公理审计。最终可验收状态以本轮最终回执中的源码身份、真实编译、原版 checker 和完整声明审计为准。**后续 cutoff 扩展或源码修订不在本次观察范围。**

| 文件，均相对于仓库根 | 观察到的 SHA256 |
| --- | --- |
| `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean` | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` |
| `ImbalancedChen/ActualHistoricalFifthCellIntegral.lean` | `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de` |
| `ImbalancedChen/ActualHistoricalFifthSavingIntegral.lean` | `667c6cf7122640210488d984cc0faa669ea4055e0daea9674f4e76b2be7b5e7c` |

在这些版本所声明的范围内，未发现 cutoff、历史祖先、old/new own-cube 或 prime-box 归属的语义混淆。第三个模块已经写出 literal nested saving 到 tuple correction，以及实际 fourth-policy 减 fifth-policy 的桥；这改变了上轮“该桥尚未写出”的源码状态，但本审计不据此宣布其已经编译通过。

## 2. 固定 cutoff、枚举 cap 与残差商水平

积分对象使用固定的 `D : ImbalancedChen.HistoricalPrefixCapData`，在引入 `N` 前给出全部有限数据；尤其 `D.a`、`D.b`、`D.m`、各层选中 cell 和有理 cap 均固定。原始素数 carrier 为

\[
z_N=N^{D.b},\qquad
\mathcal P_N=\{p:\ p\text{ prime},\ p\nmid N,\ 0\le p<z_N\}.
\]

`cap : ℕ → ℕ` 是有限枚举上界。极限定理要求沿正偶数目标最终有

\[
N^{D.b}\le \operatorname{cap}(N).
\]

该条件供应两个具体步骤：

1. `HistoricalUpperFiveCellGeometry.lean` 中的 `ImbalancedChen.mem_historicalUpperFiveFrontierTuples_iff_log_on_cell`（观察版本第 218 行）和 `ImbalancedChen.historicalUpperFiveFrontierTuples_cell_filter`（第 263 行），通过 `ImbalancedChen.mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap` 消去辅助的 `p < cap`。
2. `ActualPrimeBoxOwnCubeResidual.lean` 的 `ImbalancedChen.exists_actualPrimeTupleOwnCubeMinus_uniform_threshold`，用最后素数的
   \[
   p_4<N^{D.b}\le\operatorname{cap}(N)
   \]
   向 compact residual supplier 提供覆盖。

**cap 覆盖的是 residual 的素数筛选 cutoff \(p_4\)，不是商水平 \(N^\lambda/P\)。** 真实残差保留 `actualSmallRosserMinusDensity N cap p₄ (N^λ/P)`，\(P=\prod_i p_i\)。无需假设 `cap ≥ N^λ/P`；当前源码也未加入该假设。

### 有限身份与极限的不同范围

| 定理，命名空间为 `ImbalancedChen.HistoricalPrefixCapData` | 当前范围 |
| --- | --- |
| `actualHistoricalFifthSaving_eq_fifthPrimeCorrection` | 任意 `N cap : ℕ`；两边使用同一有限 carrier，因此无需 cap 覆盖。观察版本 Saving 第 68 行。 |
| `upperFourthToFifthSaving_eq` | 允许任意 `z : ℝ`；需要 `1 < (N : ℝ)`、`D.a ≤ D.b` 和 `D.levelCheck = true`。观察版本 Saving 第 160 行。 |
| `tendsto_fifthPrimeCorrection`、`tendsto_actualHistoricalFifthSaving`、`tendsto_upperFourthToFifthSaving` | 固定 `z = N^D.b`，需要 `0 < D.a < D.b`、`0 < D.old`、level check 和 eventual cap 覆盖。 |
| 上述 `_ceil` 特例 | 用 `Nat.le_ceil` 内部供应覆盖；原 `p < z` 仍严格。 |

若 \(z_N\) 恰为整数或素数，`Finset.range (Nat.ceil z_N)` 与原严格条件均排除 \(p=z_N\)，没有端点变成 `≤` 的问题。

**裸 floor 并非同一枚举。** 例如 \(N=10\)、\(b=1/2\)、\(z=N^b=\sqrt{10}\)、\(p=3\)：\(p\) 是素数且 \(p\nmid N,\ p<z\)，但 `Finset.range (Nat.floor z) = Finset.range 3` 排除了它。这是 carrier 层的反例；当前 ceiling 定理不能支付把 cap 改成裸 floor 的误差。若改用 `floor z + 1` 并证明覆盖，可接一般 cap 定理。

## 3. 历史 parent、真实素数和 Ico 唯一归属

观察版本 Geometry 第 34、41 行给出的共同区域为

\[
R_j=C_j\cap
\{t_0>t_1>t_2>t_3>t_4,
3t_0<D.old,
t_0+t_1+3t_2<D.cell3(j_3)\}.
\]

第三层门读取同一 fifth cell 的有效第三祖先。第四层只供应旧第五残差

\[
D.old5(j)=D.cell4(j_4),
\]

其中包含第四层未选中时继承第三层的 fallback。第四层没有被额外加入第五 candidate 的 parent admission。

Geometry 第 152 行的 private `historicalUpperFive_parent_valid_iff` 保留完整 `FirstExitValidSelection`，利用普通 parent 等价式和 root-to-third level 比较化为两个 cube 门；它没有直接删去完整乘积许可。

真实算术条件通过以下供应完整保留：

- `ImbalancedChen.roughPrimeFinset` 和 `ImbalancedChen.mem_roughPrimeUniverse`：`p < cap`、素性、`¬p ∣ N`、原下端和严格上端。
- `ImbalancedChen.mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap`：同一 carrier 的 `StrictAnti p` 和真实 parent `FirstExitValidSelection`。
- `ImbalancedChen.mem_actualPrimeBoxTuples_iff`：每个坐标满足素性、`¬p i ∣ N`、\(N^a\le p_i<N^b\)。
- Geometry 的 `mem_historicalUpperFiveFrontierTuples_iff_log_on_cell` 和 `historicalUpperFiveFrontierTuples_cell_filter` 双向使用上述接口，未换成未删目标素因子的 carrier。

处理坐标为严格递减的 \((p_0,\ldots,p_4)\)，历史反向存储为 `[p₄,p₃,p₂,p₁,p₀]`。Saving 第 31、45 行的两个 history normalization 定理通过 `ImbalancedChen.primeHistoryTuple` 恢复实际自然数积、最后素数及祖先坐标，没有隐含排序替换。

Ico 的唯一归属链为

~~~text
ImbalancedChen.logPrimeMeshCell_unique
→ ImbalancedChen.historicalPrefixLookup_on_cell
→ ImbalancedChen.historicalPrefixLookup_apply_sub
→ ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub
→ ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_eq_cell_indicators
→ ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection_eq_cells
~~~

内部网格墙按原逐坐标左闭右开归属。CellIntegral 第 74、88 行分别给出未选中 cell 和所有选中 cells 之外的实际 residual 差恰为零；第 137 行是有限精确分区。因而从 `w=0` 的原 carrier 限制到选中 \([N^a,N^b)\) cells 的过程中，没有另行丢弃小素数尾项：该**差**在选中区域外由相同有效第四祖先 fallback 而精确为零。此有限身份不使用连续零测。

## 4. old/new own-cube、符号和归一化

`ImbalancedChen.actualPrimeTupleOwnCubeMinus` 对每个 \(\lambda\) 单独保留

\[
\mathbf1_{\{Pp_4^2<N^\lambda\}}\,
\operatorname{actualSmallRosserMinusDensity}
(N,\mathrm{cap},p_4,N^\lambda/P)
\frac{\log N}{\mathfrak S(N)}.
\]

新阈值是 `D.cap5 j`，旧阈值是 `D.old5 j`。CellIntegral 第 183 行的 `fifthCellPrimeCorrection_eq_residual_sums` 是 **new minus old**；两项使用共同 \(R_j\)，各自保留自己的严格 own-cube 指示。

第五 own-cube 不进入 candidate enumeration，旧门拒绝、新门接受的 candidate 仍在 sum 中。`ImbalancedChen.actualPrimeTupleOwnCube_iff` 和 `ImbalancedChen.actualPrimeTupleOwnCubeMinus_primeHistoryTuple` 分别供应严格 logarithmic gate 和原历史实际商水平的精确身份。

Saving 第 68 行将 literal nested saving 乘**一次** `Real.log N / singularSeries N` 识别为已经归一化的 tuple correction。第 160、190 行的符号为

\[
\operatorname{RetainedPolynomial}(upperFourth)
-\operatorname{RetainedPolynomial}(upperFifth)
=\operatorname{actualHistoricalFifthSaving}.
\]

它的极限为 `D.fifthCorrectionIntegral`。当前模块不另外断言 saving 非负，也不声称两项完整单独密度分别存在极限。

## 5. 实际离散边界质量的供应链

### 5.1 单素数端点、目标素因子删除和分母移位

`ImbalancedChen.actualPrimeReciprocalWindow_difference_le`，位于 `ActualPrimeReciprocalMass.lean` 第 50 行，在 \(0<N\)、\(2\le A<U\) 下证明

\[
\left|
\sum_{\substack{A\le p<U\\p\ {\rm prime}\\p\nmid N}}\frac1{p-1}
-\sum_{\text{supplier window}}\frac1p
\right|
\le \frac{2\log N}{A\log2}+\frac6A.
\]

有限源码分别支付目标素因子删除、\(p-1\) 到 \(p\) 的分母移位和两个端点原子。随后

~~~text
ImbalancedChen.actualPrimeReciprocalMass_difference_le
→ ImbalancedChen.tendsto_actualPrimeReciprocalMass
→ ImbalancedChen.tendsto_actualPrimeBoxMass
→ ImbalancedChen.tendsto_actualPrimeBoxTestSum_cube
~~~

供应真实目标删除的多维连续测试函数极限。其底层 Mertens 输入为冻结依赖已证明的 `MathlibNt.SieveTheory.PrimeReciprocalLogScale.tendsto_primeReciprocalLogInterval`。

### 5.2 混合 Ico 和严格 affine 门

`ActualPrimeIcoCellTestFunctions.lean` 第 32 行的 private `affineSandwich_test_error` 对每个点证明

\[
|\mathbf1_Rf-fr_m^-|
\le |f|(r_m^+-r_m^-).
\]

该点态估计包括实际素数恰落在墙上的情况，不以墙上无素数原子为前提。

同文件第 71 行的 `ImbalancedChen.tendsto_actualPrimeBoxTestSum_cube_affineSandwich`，在证明中的 `he`（第 113 行起）乘实际非负权 \(\prod_i1/(p_i-1)\) 并求和，得到

\[
|S_N(\mathbf1_R f)-S_N(fr_m^-)|
\le S_N\bigl(|f|(r_m^+-r_m^-)\bigr).
\]

右端是真实素数和。其极限使用 `ImbalancedChen.tendsto_actualPrimeBoxTestSum_cube`，连续 ramp-gap 的积分再由 `ImbalancedChen.tendsto_integral_affinePrimeGateRamp_gap` 趋零，完成最终 \(\varepsilon\) 估计。

连续零测链是

~~~text
ImbalancedChen.affinePrimeWall_volume_zero
→ ImbalancedChen.ae_primeAffineGate_no_wall
→ ImbalancedChen.tendsto_integral_affinePrimeGateRamp
→ ImbalancedChen.tendsto_integral_affinePrimeGateRamp_gap
~~~

`integral_affineSandwich` 是同文件第 49 行的 private 连续积分身份；零测结论只在连续积分及连续 dominated convergence 侧使用，没有据此从实际离散素数和中删除边界。

**实际依赖与文本先后顺序须区分。** 点态误差引理在第 32 行先于连续身份；总 Tendsto 证明第 82 行先重写连续积分，第 113 行以后才实例化有限加权误差。因此不能写成“源码已先独立证明实际 wall mass 的 Tendsto = 0，然后才使用任何连续零测结论”。正确表述是：已有独立点态控制，连续零测仅处理连续积分，完整算术极限始终用明确的有限加权误差支付实际原子，依赖不循环。

`ImbalancedChen.primeIcoBoxGateForms` 加入下端 `-proj`、上端 `proj` 和 caller 门；`ImbalancedChen.tendsto_actualPrimeBoxTestSum_cube_IcoCell_affineGates` 保留原 Ico 算术归属，供应其真实积分极限。

### 5.3 真实 residual 和本轮 saving

完整调用链为

~~~text
ImbalancedChen.exists_actualPrimeTupleOwnCubeMinus_uniform_threshold
→ ImbalancedChen.tendsto_actualPrimeBoxOwnCubeMinus_error
→ ImbalancedChen.tendsto_actualPrimeBoxOwnCubeMinusSum_IcoCell_affineGates
→ ImbalancedChen.tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates
→ ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthCellPrimeCorrection
→ ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection
→ ImbalancedChen.HistoricalPrefixCapData.tendsto_actualHistoricalFifthSaving
→ ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving
~~~

`tendsto_actualPrimeBoxOwnCubeMinus_error` 对任意固定附加区域使用一致实际 residual 误差和有界真实 prime-box mass，不要求有限 lower sieve 密度非负。Old/new 的 own-cube form 分别由 `primeOwnCubeGateForms` 加入；`primeOwnCubeGateForms_ne_zero` 和六个 parent forms 的非零性供应适用的连续墙结论。

## 6. 尚未闭合及不能扩大宣称的范围

- `D.levelCheck` 只检查三层有限 **old ≤ new**。它不证明 mask 的 square/envelope license；`StoredHistoricalBoxPermit` 的实际采用表和有效历史 old 身份仍须连接。
- 本审计三模块是固定历史 upper third/fourth/fifth 构造的组件，未完成手稿全部采用上/下 policy、所有层的积分组合。
- 当前已有 nested fifth saving 桥的源码；其真实验证状态以最终同源回执为准，不能仅据本语义审计升格。
- 新的任意 cutoff、移动网格或裸 floor 变化未包含在观察范围；没有为这些变化提供额外边界支付。
- 当前边界供应足以给出所声明固定 cell 上的真实加权极限；没有交付全局有效数值边界常数或完整有符号误差账。
- Saved-floor 的真实语义、其他保留/截断项、实际系数支持与因子分解、物理 majorant、完整 \(K/c\)、`hLower` 和 `hUpper` 仍为独立输入。它们没有被作为新积分公式的合法性假设。
