# Moving-wall payment：独立静态审查

审查者：`/root/p36_cache_review`。

**结论：未发现数学量词、支付方向或已定位源码表达上的阻断项。可以继续后续静态集成和正式验证；本结论不是 Lean 编译、kernel replay 或 owned type/axiom 验收。**

## 固定审查对象

- 新桥 `P3OriginalU5MovingWallPayment.lean`：8,944 字节，SHA256 `28b1032a2231d391b96f2bdfe644d6c7efd486e9ac5e062e8c7a4979066ea9e2`，五个 theorem，无新增 coefficient、carrier 或算法定义。
- main 基点：`4d1b2ed5abfe0772a8b3f1c52931a3f6f954cd27`。
- 当前 prepared payer：`P2CanonicalWallFullResidualPayment.lean`，SHA256 `5e935c38a45cb38cee5d505585beed3d2f38dda0a6ad63eab0ca7245b1687860`。它已显式补入既有 `PrimeHistoryLogCoordinates`。本报告绑定这一修正后的依赖图；旧 90 模块图不再表示当前状态。
- fixed-width supplier：`P3OriginalU5FixedWidthSlabReserve.lean`，SHA256 `76e20ecdebb2d2d2accecef691544181703ed32cd8b38f10704100d3e18ed68a`。

相关旧 API 的固定 P15 文件 SHA 与当前被调用定义/声明均已核对。payer 原证明的完整复用、逆还原属于 source_recovery 的独立审查范围；本次检查其被消费的实际 arithmetic interfaces，以及当前 imports/source hash 绑定。

## 五条定理

| 定理 | 独立检查 |
|---|---|
| `exists_fixed_width_linear_center_reserve` | 直接调用旧 `linearCoefficients_ne_zero`、`exists_nonzero_coordinate` 与 `linearSlabMass_eq`，把新 fixed-width supplier 接到一般非零连续线性形式；没有重新证明线性表示。`d=0` 时函数空间为 singleton，线性形式必为零，与 `hL` 矛盾，分支正确。 |
| `linearSlabMass_mono_radius` | 只扩大绝对值半径，实际 prime tuple carrier 和 summand 不变。集合包含方向正确，使用实际 prime weights 非负性。 |
| `actual_wall_union_le_sum_slabs` | 左侧每个实际 tuple 在至少一条闭墙带中，选择该项后由其余项非负得到逐点不等式。有限求和交换没有更改权重；多重覆盖只向上计数。 |
| `exists_fixed_width_uniform_centers_reserve` | 每条行先以 `eta/(k+1)` 得到正宽度及 threshold；取 `insert 1 (image width)` 的有限 minimum，取所有 threshold 的 finite supremum 后再与 2 取 max。所有 center 都在共同宽度及共同阈值之后。 |
| `exists_uniform_centers_full_residual_wall_payment` | 先从旧全 residual envelope 取得 `C>0`，再以 `eta/(2*C)` 支付墙带。原 `wallRoundingCharge_le_two_mass` 的完整 residual 因子和系数 2 均保留；`Even N` 和任意后选 enumeration cap 的量词也保留。 |

## 量词与边界情形

最终定理的实际顺序为：固定 `omega,v`、固定有限行 `L` 及其 properness、给定 `eta>0`，然后

\[
\exists\delta>0\;\exists N_0\ge2\;
\forall N\ge N_0\;\forall\mathrm{cap}\;\forall\mathrm{keep}\;
\forall\tau\;\forall c,
\]

并在 `Even N` 下得到实际 `wallRoundingCharge < eta`。所用的 `C` 仅由固定 rough exponents 的已有供应产生；finite minimum 和 finite supremum 的被选对象也不依赖后来的 centers。因此 centers 可以任意依赖 N、pair、cap 等后来输入，定理无需其极限或固定中心假设。

`k=0` 时 widths 集合仍含 1，故 minimum 为正；threshold 的空 supremum 不影响 `max 2 ...`。墙带并集和 slab 总和都为空，严格预算来自 `eta>0`。对一般 k，

\[
k\frac{\eta}{k+1}<\eta
\]

留下严格余量，所以证明把每个单行严格界弱化成非严格求和界也是安全的。零维且有非零行的情形不可能；零维、空 family 的情形仍有效。

有限 minimum 的正性证明分别处理 dummy 1 和实际 width。每个元素均严格为正；没有把一般无限下确界错误当作正数，也没有在 min 之后缩成零。

## 实际载体与完整质量

`linearSlabMass`、`actualPrimeAffineWallStripMass` 使用同一个 `actualPrimeBoxTuples N a b`，权重均为

\[
\prod_i\frac1{p_i-1}.
\]

需要准确区分两个端点约定：**墙带是闭条件** `|Lx-c| ≤ delta`，而原 **prime box 是半开条件** `N^a ≤ p < N^b`，同时保留 primality 和 `p ∤ N`。本桥没有修改任一个约定，没有删除恰好落在墙上的 prime atom，也没有把 target-deleted carrier 换成连续体积。

令实际 strip mass 为 S，完整 residual mass 为 M。末步使用的三个量化关系恰好是

\[
\operatorname{charge}\le2SM,\quad M\le C,\quad 2CS<\eta,
\]

其中 S 非负。由此推出 `charge < eta` 的方向和因子正确。没有把 residual divisor 求和截成单一 tail，也没有把 signed coefficient 当成非负；旧 payer 已使用绝对系数差的单位界。

## 依赖与源码检查

已独立按真实 imports 重建修正后的图，并逐一比对所有节点 hash 与当前 `DEPENDENCY_PREFLIGHT.json`：目标闭包 **100**；固定基点 selected **280**；并集 **283**。新增选中模块仍恰好为既有 `AffinePrimeWallReserve`、prepared payer 和新 bridge。无 missing、cycle 或新增 external import。新加入的 `PrimeHistoryLogCoordinates` 及其传递节点已属于原 selected 集合。

没有发现本桥中的 `sorry`、新增 `axiom`、`unsafe`、`native_decide` 或 implementation escape。上述是源码检查，不代替实际完整 serialized declaration/type/axiom inventory。

## 仍然开放的范围

这里的线性行 L 和有限索引先于 width/threshold 固定；定理没有声称对任意随 N 改变的行方向统一。warm catalogue 的 coordinate/cube 行是固定模板、只有 centers 变化，因此预期接线与这一范围相符。

本桥没有证明 actual mixed catalogue 的 canonical-prefix membership、跨 rough rank 的有限并及统一细网格选择，也没有给整个 rounding loss、density、common-Q、tensor 或 PP 记信用。它没有把这些结论作为输入。正式 strict compile、official kernel replay 和完整 owned 审计仍全部待做。
