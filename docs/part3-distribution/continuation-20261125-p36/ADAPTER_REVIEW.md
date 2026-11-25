# P3.6：U5 物理模数上界应接入哪里

## 审查状态与结论

这是只读源码审查及后续接线建议，**不是 Lean 编译或内核验收回执**。审查基于本轮集成提交 `aa0f93b87cfd976ca5185e1293c1930562577d8a`、既有 P3 基线 `ef1479c272bdd6b24800fa10409d793f0a2fe95c`、下列既有 Y05/Y06 档案，以及 2026-11-25 最新 P3.5 记录提交 `1847d4c446be7ea2e8a83046f2561dda7a537ab5`。未为本审查新增 Lean 定理、改写系数或扩大编译闭包。编译状态以另附验收回执为准。

本轮 `selected_integerRho_nonzero_modulus_lt_theta` 最直接的消费位置是既有 `P5OriginalU5ClassicalComplement.beyond`：该载体已经保留真正的 `integerRho ≠ 0`，且已经进入 `exists_original_count_beyond_classical` 的未支付 `branches`。新上界可把这个实际余项的模数范围限制到

\[
  \operatorname{panModulusCutoff}(N,B)<q<N^{599/1000}.
\]

这填补的是实际载体的物理范围。它没有证明该余项的分布估计，也不单独构造 `MediumAdmissible` 或稿内完整的 (S)/(F) 系数类。应继续消费现有 rank-one U5 源及其 `branches`，不另造一个与实际 U5 源无关的 rank-two 条件包装。

## 1. 已有的同一 ρ 性质，不应重复证明

`P5OriginalU5PlateauPrimeBV.modulus_data` 是既有私有引理，其实际结论为：对 `q ∈ moduli N e P`，在 `smallCutoff N e ≤ cutoff N` 下，

\[
  0<q,\quad \operatorname{Squarefree}(q),\quad (N,q)=1,
  \quad |\operatorname{integerRho}(N,e,P,q)|\leq 1.
\]

它使用同一 `integerRho_at_original` 和 `actualEvenLowerIntegerRho_cast`，没有更换系数。其可见性是模块组织问题，不是缺少这段数学证明。

另一个已存在且公开的供应者是 `P5OriginalU5AllMarkCosts.full_modulus_data`。其**返回类型**更具体地给出：

1. `q ∈ (sieveProduct N N).divisors`；
2. `|(integerRho N e P q : ℝ)| ≤ 1`；
3. `∀ p ∈ q.primeFactors, (p : ℝ) < N^(19/125)`。

第一项经既有 `Nat.pos_of_mem_divisors`、`sieveProduct_squarefree`、`coprime_of_dvd_sieveProduct` 即提供正性、平方自由性及与 N 互素。`P5OriginalU5ClassicalComplement.exists_full_classical_payment` 已经这样消费这些字段，并接到实际的经典 BV 支付。无需再写另一套模数性质证明。

| 所需事实 | 已有供应者 | 本轮上界的作用 |
|---|---|---|
| 使用真实整数系数、原标签和原小粗素数符号 | `rowInteger`、`integerRho`、`integerRho_at_original`、`actualEvenLowerIntegerRho_cast` | 保持这些定义不变 |
| `q > 0`、平方自由、`N.Coprime q` | 私有 `modulus_data`；或公开 `full_modulus_data` 的整除结论加既有素数积性质 | 不需要新证明 |
| `|ρ(q)| ≤ 1` | `full_modulus_data` | 可取固定除数阶 `J = 0`、常数 `Cρ = 1` |
| 所有素因子低于 `N^(19/125)` | `full_modulus_data` | 不能代替对完整乘积的上界 |
| 非零实际系数处 `q < N^(599/1000)` | 本轮 `selected_integerRho_nonzero_modulus_lt_theta` | 新补充的物理范围 |
| 未支付载体上 `panModulusCutoff N B < q` 且 `ρ(q) ≠ 0` | 既有 `beyond` 的定义 | 可直接满足新上界的非零前提 |

这里不能把“非零系数处的上界”改称整个原始 `moduli` 的上界。原始载体包括零系数项；现有 `beyond` 已经处理了这一差别。

## 2. 实际消费位置及建议的精度选择

既有定义是：

```lean
def beyond (B : ℝ) (N : ℕ) (e : ℝ) (P : Policy) :=
  (moduli N e P).filter
    (fun q => panModulusCutoff N B < q ∧ integerRho N e P q ≠ 0)
```

`actual_classical_partition` 已把原 `remainingPrimitive` 精确分成经典部分和该非零余项；零系数通过原系数为零消去。`exists_original_count_beyond_classical` 的结论保留

```lean
(branches t tau zeta 6 N K e P (beyond B N e P)).re
```

并没有声称这个 `branches` 已得到小误差界。因此无需重做分区或重新发明一个 active carrier。

建议在后续实际调用中代入

```lean
P := selectedPolicy R bank buffer false N
```

对 `q ∈ beyond B N e P`，`Finset.mem_filter.mp` 已提供新上界需要的 `integerRho ≠ 0`。既有定理的门槛先于 `N` 和任意 `P`，所以按每个 N 代入这一个实际 policy，不会把统一门槛降为逐成员门槛。

### 精确代数核对（已写具体候选，尚未编译验收）

可选择

\[
 \mathrm{buffer}=\frac1{1000},\qquad e_{\max}=\frac1{272}.
\]

既有 `exists_original_count_beyond_classical` 接受任意正的 `eMax`，并返回 `0 < e`、`e < 1/8`、`e < eMax`。当前原定义 `attachmentNu = 34/125` 给出精确恒等式

\[
 \frac{34}{125}\cdot\frac1{272}=\frac1{1000}.
\]

因此返回的 e 满足 `attachmentNu * e < buffer`，从而满足新候选所需的 `≤ buffer`。同时 `0 ≤ buffer ≤ 1/1000`、`0 < eMax < 1/8` 都是有理数不等式。

此处 e 是小因子附着精度；它不自动等于 `PairRange.epsilon`，后者仍由原来的 R 和 bank 接口给出。不能在接线时把这两个不同参数偷偷识别。

这项精度选择现已写入 `docs/source-only/20261125-p36-selected-classical/ImbalancedChen/P3OriginalU5SelectedClassicalComplement.lean`。候选直接实例化原 count 定理，并在内部推得上述 allocation；同一计数余项、同一整数 rho 和统一量词均保留。它仍未编译，其旧依赖闭包正在按精确 blob 恢复；没有据此增加任何节点验收信用，也没有支付保留的 `branches`。

## 3. 与现有 P3 接口的准确关系

### `Part3DistributionTargets`

`primeProductSignedError` 把相同的 ρ 放在 AP 项与原始互素均值之外。`UniformPrimeProductTarget` 记录目标结论及正确的统一量词顺序；它不是一个只要填入正性、平方自由和模数上界就自动得到 PP 的 record。

`MediumAdmissible` 的对象是实际 `MediumAtom`，还含有 U、V、三个模数因子尺度、移动余数、同一个区间、alpha/beta/gamma 系数。其条件包括四个具体尺度不等式、alpha 的粗素数条件、beta 的除数界以及三个 gamma 的一界和互素性。完整物理乘积 `q < N^.599` 没有提供这些因子、它们的分解恒等式或四个尺度不等式。

因此，本次核对没有发现一个可以仅靠本轮 cap 加 `modulus_data` 就构造实际 `MediumAdmissible` 的现成 adapter。不能把全局 N 的上界直接当成每个实际卷积尺度 `X = U*V` 上的所有准入条件；稿内的尺度换算与余量仍须按原参数供应。

### `Part3ProperPowerActualPairFamily`

该已存在定理族有两个明确的模数输入：

```lean
∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ)^θ
∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ)^J
```

从纯接口角度，实际非零 U5 载体可用 `K = 1`、`θ = 599/1000`、`Cρ = 1`、`J = 0` 填这两个字段。但该定理的 W 是 `smoothPhysicalPairOuterRamp`，即 **rank-two 原始素数源**。

实际 U5 的两个外标已经在 `fullModulus t k = (t.1*t.2)*k` 和 ρ 中。既有 `P5OriginalU5AllMarkSmoothing.smoothDiscrepancy` 使用的是

```lean
Part3.primeProductSignedError 1 (2*N) N Q
  (fun q => (integerRho N e P q : ℝ)) (fullSmoothWeight t B N)
```

即 rank-one 源。把 U5 的 ρ 传给一个 rank-two 通用结论可以在逻辑上有意义，却没有完成这个实际 U5 源的 PP 接线。不能据此重复制作“同一ρ proper-power 支付”并把它记到 U5 余项关闭。

### 已有实际 rank-one 工作

应复用以下已写出的候选链，按各自编译状态验收：

- `P5OriginalU5AllMarkSmoothing.exists_all_mark_smoothing`：真实 singleton 与光滑源的差；
- `smooth_original_atlas`：相同整数 ρ 上的原 HB medium/no-medium 分解；
- `P5OriginalU5AllMarkHBReserves.eventually_smooth_to_branches`：trim、proper-power、rough 等非谱修正的支付；
- `exists_original_complement_to_branches` 及 `P5OriginalU5ClassicalComplement.exists_original_count_beyond_classical`：把实际计数剩余项接到未支付分支。

这些候选已经处理了本轮 cap 之前可以完成的修正项；cap 的加入不意味着应重做它们。

## 4. 最小剩余义务及依赖边界

| 剩余义务 | 为何当前 cap 不足 | 应接到的已有工作或后续供应 |
|---|---|---|
| 实际同一ρ进入稿内 (S)/(F) 系数类 | 总乘积上界只是一项范围条件；没有完整小/粗字上的全部满前缀与选中补前缀 square tests、固定分解及其权重重建 | 复用 P2 的原 mask、`IntegerSquareGates`、实际 selected policy/trace，再补实际 rho 到完整类的供应；不改成新的自由系数 |
| 实际 HB atom 的 `MediumAdmissible` 与统一 SW 输入 | 还需实际 U/V/Q1/Q2/Q3、同区间/相位、分解一致性及各尺度和系数条件 | 原 HB/三组分解与实际 retained 模式的接线；一维 q cap 不是它的替代品 |
| `branches ... (beyond ...)` 的算术小误差界 | 现有定理把分支保留下来；分解恒等式和修正项支付不估计其主体 | 必须消费 P3.5 的实际 medium/no-medium 分布供应及其统一常数；不能把一个假设为结论的 adapter 当作完成 |
| 稿内固定共同 Q 的有限查询覆盖 | `P5OriginalU5NativeRootCover.levels N` 是 `pairSupport N` 的 rootLevel 像；它只证明每个 N 的有限分组 | 仍需 N 之前确定的查询族、原 policy 覆盖及相应误差组织；本次 N^.599 上界没有给出这些 |
| 整体投影主项与各必需族的正谐和质量 | q 的上界不给出任何正质量下界，也不支付所有筛后补集 | 复用既有 unit mark、marked mass、固定稀疏矩形候选；剩余全族/共同 Q 义务仍单独验收 |

局部 root 的两项 square gates 也不等于任意延长后完整实际字的全部 (S)/(F) 条件；`NativeRootCover.actual_root_gates` 的列表明确只有原来的两个外标。

本审查将问题区分为：精度选择和零项删除属于可补齐的代数/形式化接线；已写出的 rank-one 修正链应直接复用；完整 (S)/(F)、共同 Q 和实际算术分布仍需要其各自供应证据。这里没有据源码未接通就判定手稿存在实质性数学缺口。

### 已核对的 P3.5 证据：已验收 Cauchy 核心，实际源总装仍未关闭

已读取 `codex/p3-5-full-kernel-20261125` 在 `1847d4c446be7ea2e8a83046f2561dda7a537ab5` 的 continuation、正式 `RECEIPT.json` 和实际 adapter 的 `REUSE.json`。回执状态是 `ACCEPTED_CORE_ONLY_P35_OPEN`，不能继续用“P3.5 的 Cauchy 步骤尚未写出”来描述当前上游。

- 已验收模块为 `ImbalancedChen.Part3ContinuousTraceCauchy`，数学源码提交 `de24ecddb6f5bdb0c8173c788ace734207c457a0`，源码 SHA256 为 `4c6a664915885c31f2d0f8960b2650daa5b7ae44bc31f697a08bbf9a52974c3c`。
- [GitHub run 45571177099](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45571177099) 的回执记录：4 条公开定理、包含 1 个生成 helper 的完整 5 声明清单，严格编译、bundled kernel replay 与传递公理核验全部通过；只使用 `propext`、`Classical.choice`、`Quot.sound`。验收完成时间为 2026-11-25 07:55:39 UTC。
- 该工作已经处理真实连续谱配对中 Cauchy 的规范化、共轭、同一能量测度及开方后的一次除数价格。**本轮 P3.6 不重复这段工作。**
- 接到实际 Y04 行的 `Part3OriginalGeometricWindowEnergy.lean` adapter 仍为 `SOURCE_ONLY_DEPENDENCY_CLOSURE_UNAVAILABLE`：其增补声明是 `original_tested_continuous_window`，源码已写出，但还没有 Lean/kernel/axiom 验收。`REUSE.json` 记录了 6 个已登记 SHA256 而字节尚未恢复的原供应文件；这属于已有源码恢复阻塞，不能说这些证明从未存在，也不能靠重写同名接口绕过。
- 完整 P3.5 仍缺经过兼容核验的实际 trace/Fourier/continuous-spectrum 闭包，以及实际家族上的原外部输入和全部频率、level、height、sign、six-scale 费用的统一支付。独立 Cauchy 核心通过不自动验收实际 adapter，更不能自动估计本节保留的 U5 `branches`。

因此本轮 cap 后续应等待或消费实际 P3.5 供应的完成状态；“等待”的对象是实际谱/算术总装，不是重做已通过的有限或积分 Cauchy 不等式。

### 09:24 UTC 上游刷新：完整高度桥接已有源码，不应重写

再次核对分支后，最新提交为 `fa96aa2a5990ff998868d59d10e359c9e2e14bb8`。已读取其 `P35-FULL-HEIGHT-20261125.md` 与 `continuous-height/SOURCE_REUSE.json`：上游已复用七个历史验收供应模块（378 个声明），恢复 `Part3RegularCumulativeShellPayment`、`Part3RegularPositiveMeasureExhaustion`，并新增 `Part3ContinuousTraceExhaustion`，把同一两行能量与已验收 Cauchy 接到全实线高度穷尽。该快照的两个历史目标和新增桥接仍等待实际云端验收；不能把源码提交当成通过。

这项新进展不重写外部 ABL、Kim–Sarnak 或 Pascadi 定理。六个登记但未恢复字节的实际 Y04 供应仍是旧 actual-row adapter 的阻塞；固定测试函数的衰减常数与实际 Fourier／level／six-scale 家族的统一费用也仍有区别。因此本轮继续复用上游的新工作，不再把“高度穷尽尚未实现”列成待从零编写的任务，也不据此将完整 P3.5 或 P3.6 标为完成。

## 5. 精确来源

以下路径均相对于 `UyNewNas/goldbach-formalization`。审查时已用 Git tree/blob 核对相应档案，未以工作目录的未经固定改动冒充发布源码。

| 原定义/定理 | 源提交及路径 | Git blob |
|---|---|---|
| 新 U5 cap 六条候选 | `aa0f93b87cfd976ca5185e1293c1930562577d8a` — `ImbalancedChen/P3OriginalU5PhysicalModulusCap.lean` | `2b4ecdbec201a63658216c87fb8248ec53afff02` |
| `attachmentNu` | 同一集成提交 — `ImbalancedChen/CurrentChenP5OriginalU5CausalFinite.lean`；原文件来源见 `SOURCE_SELECTION.json` | 见来源清单 |
| `MediumAdmissible`、`UniformPrimeProductTarget` | `ef1479c272bdd6b24800fa10409d793f0a2fe95c` — `ImbalancedChen/Part3DistributionTargets.lean` | `178e0fa5acc4f1c5b77b1ff0a3d6b933c9ef3fe6` |
| 两个模数输入和 rank-two W | `ef1479c272bdd6b24800fa10409d793f0a2fe95c` — `ImbalancedChen/Part3ProperPowerActualPairFamily.lean` | `f8ac55f6d11314cd1af335a47384c699e14856c1` |
| 私有 `modulus_data` 及原 physical rho 定义 | `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b` — `docs/source-only/20261123-resume/ten-task-continuation/ImbalancedChen/P5OriginalU5PlateauPrimeBV.lean` | `c58f36332084fc07e57d1ff3eeaafd478de5f44e` |
| 公开 `full_modulus_data` | 同一 `2dbe821e…` — `docs/source-only/20261123-yellow-node-owners/y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkCosts.lean` | `a2af61aa4f37b0e180c438db49dbed4905706b96` |
| 实际 rank-one 光滑源及 atlas | 同一 `2dbe821e…` — `docs/source-only/20261123-yellow-node-owners/y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkSmoothing.lean` | `db0a39c79124fb95a061abdceb4066c4a4b9b9e0` |
| 实际修正支付及未支付 `branches` | 同一 `2dbe821e…` — `docs/source-only/20261123-yellow-node-owners/y06_same_rho_pp/ImbalancedChen/P5OriginalU5AllMarkHBReserves.lean` | `8e11063b5ec1b6684cb3aed4cd71b3c639e1f1e8` |
| `beyond`、精确分区和实际未支付计数结论 | 同一 `2dbe821e…` — `docs/source-only/20261123-yellow-node-owners/y05_causal_q_mass/ImbalancedChen/P5OriginalU5ClassicalComplement.lean` | `af7f2905aedf6ff2a6ab367d5976e991ddcb04b0` |
| 每个 N 的 rootLevel 分组及原两个外标 gates | 同一 `2dbe821e…` — `docs/source-only/20261123-yellow-node-owners/y05_causal_q_mass/ImbalancedChen/P5OriginalU5NativeRootCover.lean` | `2234c3504e6f13201b2d060eec3b332b793ce745` |
| 最新 P3.5 范围与未关闭义务 | `1847d4c446be7ea2e8a83046f2561dda7a537ab5` — `docs/part3-distribution/P35-CONTINUATION-20261125.md` | `f8ac6182a905bb540cfa1c5f91aaf8bde356cd00` |
| P3.5 独立 Cauchy 核心验收回执 | 同一 `1847d4c4…` — `docs/part3-distribution/continuation-20261125/continuous-trace/RECEIPT.json` | `ed98856e07733a132b58c39bc4a1dc7ba8c218bb` |
| P3.5 实际 adapter 保留及未恢复供应清单 | 同一 `1847d4c4…` — `docs/source-only/20261125-p35-continuous-trace/REUSE.json` | `93a33c1f2c93e283be6501a6d7542cd070960dba` |

本轮仅把已有源码的纯供应接口拆到轻模块；保持 namespace、声明含义和原系数的证据见 `proof-preservation.json`、`native-lower-data-preservation.json`、`root-q-preservation.json` 与 `tagged-pushforward-preservation.json`。


### 2026-11-25：上游全高度验收刷新

已重新读取 `5285d4f5d8c40eddf92c108b492c909de8b43cef` 的正式 height receipt、独立审查和稿件边界。精确数学源码 `94cff537f2e60173aaf936c2345d5af0ee5e6585` 的三个目标已在 P3 任务 `cbcebb66105f4036a00789cc806ce176` 完成 strict compilation、bundled kernel replay、完整声明类型与传递公理审计，共 81 个 owned 声明。上述 09:24 快照的“等待验收”是历史记录，不再是当前状态。

这三模块为 `Part3RegularCumulativeShellPayment`、`Part3RegularPositiveMeasureExhaustion`、`Part3ContinuousTraceExhaustion`。root 本次读取了上游回执和完整独立验收记录，并未重新编译或重复计数。原 Cauchy 核心及七个历史供应继续直接复用。实际 original-row adapter、完整物理家族上的 uniform Fourier/level/six-scale 费用及其实际外部输入仍未关闭。

本轮 all-source 与 signed 两模块另行提供了所有短词／继承／fresh 历史的平方候选；参见 `ALL_SOURCE_SQUARES_REVIEW.md`。这使本审查较早的“没有全来源平方候选”成为已推进的历史缺项，不能继续按未写出描述。新候选尚未编译，并未解决 full (F)、W adoption、共同 Q、正质量或未付 signed branches 的分布估计。
