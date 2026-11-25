# 原 U5 coarse policy：目标量词与同一系数的范围核对

日期：2026-11-25。独立只读源码／稿件审查的保存记录。本报告补充 [COARSE_ROOT_V_TRANSPORT_ANALYSIS.md](COARSE_ROOT_V_TRANSPORT_ANALYSIS.md)，不替换或改写该历史审查，不重复其 common-Q／admission 审计。

固定核对基点为 main `072863fe9c8cbef6c4dc1f5ce42cc5b7c18c6c8c`、count `086aad2886b91e0a39378af77b741a5622a88406` 和只读 donor `d6a9d76c56621992a8445c9628d4a2058db72eb6`。稿件为 `chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` 的 1106 英文版。精确文件、Git blob、原字节 SHA-256 及作用见 [COARSE_POLICY_TARGET_ALIGNMENT_SOURCES.json](COARSE_POLICY_TARGET_ALIGNMENT_SOURCES.json)。

**本报告不提供新的 Lean、编译、kernel replay、公理审计或 PP 验收；不改变现有 targets、manifest、看板状态及已有验收范围。**

## 1. 结论

先选取稿件规定的有限 coarse policy，再让 count、密度和 PP 始终使用由它产生的同一个 rho，是合法且更贴近 1106 稿件的实例化路线。看板 P3.6 的“同 rho”没有写成必须使用本轮 pointwise `selectedPolicy` 的量词。

这不允许把新 coarse rho 当作当前 literal rho，也不自动保留所需的 U5 数值密度下界。现有 selected-policy 导出命题仍保持原实例；新 coarse rho 的 PP 不能计为旧实例的 PP，不能用于关闭仍写着旧 `P` 的 signed `branches`。

在本次固定源码范围内，已有可复用的 count 入口、常量 seed policy 内核、实际有限格舍入及密度误差记账。但未找到完整的、针对原增强 U5 的 coarse policy 实现，以及其已付清误差的密度供应者。这是一条正确的候选路线，不是一个已可替换进去的完成证明。

## 2. 通用 count 的量词及其准确含义

`P5OriginalU5ClassicalComplement.exists_original_count_beyond_classical` 的量词顺序是

\[
\exists B,C,e,M,\quad
\forall N\ge M,\ \mathrm{Even}(N)\Longrightarrow
\forall P:\mathrm{Policy},\ \forall\zeta,\quad \cdots .
\]

其中 `B,C,e,M` 先于 `N` 和 `P`。核心结论为

\[
\begin{aligned}
&\operatorname{fullProjectedMainSum}(N,P)
-\operatorname{projectionReserve}(N,\eta)\\
&\quad+\operatorname{Re}\bigl(
\operatorname{branches}(\ldots,e,P,\operatorname{beyond}(B,N,e,P))\bigr)
-C\frac{N}{(\log N)^3}
\le \operatorname{currentChenUpsilon5}(N).
\end{aligned}
\]

该入口不要求 `P = selectedPolicy ...`。source-only selected consumer `P3OriginalU5SelectedClassicalComplement.exists_selected_original_count_beyond_classical` 才在内部令

```lean
P := selectedPolicy R bank (1 / 1000 : ℚ) false N
```

并应用上述通用定理。故从一开始用实际构造的 `Pcoarse N` 实例化 count 入口，在逻辑上没有障碍。可以先固定 coarse 数据和正余量，再通过 `eMax` 限制后续的小参数；不能由 `∀ P` 反推某个未构造的策略已具备这些余量。

如果整个新证明始终处理新策略产生的 rho，这一步不要求证明 `rho_selected = rho_coarse`，也不要求先估计二者的 discrepancy 差。它没有把两项系数识别成相等。

### 同一个算术 count 不等于同一个数值主项

右侧 `currentChenUpsilon5 N` 是原算术计数。左侧 `fullProjectedMainSum N P`、`beyond ... P`、整数 rho 以及保留的 `branches ... P` 都随 `P` 改变。

`CurrentChenP5OriginalU5CausalFinite` 中，`fullDensity N policy` 是该 policy 的完整 even-retained density，`fullProjectedMainSum` 对这些密度作原 pair 加权求和。实际附着 beta 的 physical density 则是 `density N epsilon policy`。`exists_originalU5_full_density_causal_lower` 给的是同一 policy 下由 full density 到 physical density 的带 reserve 比较，并非二者无误差相等，更不是跨 policy 的密度不变性。

所以通用 count 定理没有供应

\[
\operatorname{fullProjectedMainSum}(N,P_{\rm coarse})
\ge (L_5-o(1))\operatorname{singularNormalization}(N).
\]

选出的实际 coarse U5 策略必须取得所需增强密度及误差预算。不能只保留右侧同一个 count，就沿用旧的数值下界。

## 3. 稿件中的选择顺序与“同 rho”

固定 `coefficient-appendix.tex` 的 `Finite policies and residual square conditions` 先规定有限前缀上的 physical level，并要求 ancestor 决策在 children 细分前固定。coarse box 的例子以

\[
\Gamma_{\mathscr B}=\inf_{\mathscr B}\max(A,W),\qquad
\lambda_{\mathscr B}=\Gamma_{\mathscr B}-2e
\]

定义 physical cap，并未声称它等于逐点 `max(A,W)-2e`。`Finite approximation and strict margins` 要求 count 与 density 使用共同的有限策略。随后 auxiliary covering level 可以较大，但取得 cover 时不改动已选定的 physical lambda。

`coef:prime-product-insertion` 对本 appendix 构造的有限系数族给 PP，且 count 与 exact coprime mean 使用同一系数。`sieve-appendix.tex` 的 `sv:finite-realization`、`sv:physical-lower` 同样先固定实际有限策略，再组织舍入、beta 附着、密度误差和该实际输出的分布。

因此“physical lambda 不因 auxiliary cover 改动”约束的是已经选定的 physical 实现，不能解释成禁止最初选择稿件规定的 coarse physical 实现。这一允许也仅限于原稿实际策略的合法有限实现；它不是“任选一个较弱 Policy，只要通用 count 不等式成立就算完成原增强 U5”。

### 看板目标与本轮具体函数的区别

P3.6 要求原实际源族的同 rho count／mean／PP；child-28 要求原 causal 的共同 Q、过滤补集和实际正质量供应；child-30 保留未覆盖实际 U5 等源族的 smooth 准入、原保留模式、完整 (S)/(F) 及 PP。其职责文字没有指定 `selectedPolicy` 函数。

相比之下，当前 `P2OriginalSelectedPairNativeData.selectedPolicy` 确实把

\[
\operatorname{rootSeed}(N,t)=\operatorname{rootLevel}(N,t)-2b
\]

同时送入 `pairPlan` 与 `pairPolicy`。新有限标签上的常量 physical cap 通常产生另一项 `P` 和另一项 rho。它可以是原 U5 算术计数的另一项稿内实现，但不能把其证明记到当前 literal 实例。

现有 `P3OriginalU5CoarseRootV` 只构造 auxiliary cover，保留原 seed、policy 和 rho。其名称里的 coarse 不表示已经定义了本报告讨论的新 physical coarse policy。AllSigned、RootV 等具体导出命题也不能直接改读成新 P 的命题；可复用的通用 plan／seed 底层接口须准确实例化。

## 4. 已有六项资产及其边界

| 资产 | 已有的实际内容 | 尚未供应的 U5 连接 |
|---|---|---|
| 通用 count 入口 `exists_original_count_beyond_classical` | 对任意 P 的原计数下界、相同 P 的 signed complement 和 classical payment | 没有指定 coarse P 达到所需增强 U5 数值密度的结论 |
| `P5OriginalU5NativeRootCover.policyAt` 与 `P2OriginalPairSourceReceiver.pairPlan` | 给定常量 v 的真实 pairPolicy 内核；继续使用原 rank 3/4/5 checked decisions | 现有 `levels N`／`marks N v` 是 per-N 覆盖；没有 N 前固定的完整 U5 coarse physical level 族及其密度保证 |
| `P5LowerPolicyDensityStability` | 由实际 first-disagreement recursion 得到两项 full-policy densities 之差的显式预算 | 未将某个具体 U5 coarse 选择的预算证明为所需小误差 |
| `P2LowerFiniteCellRounding` | 对整个实际 label fibre 作正系数 inner／负系数 outer 舍入，测试完整 retained history | 未证明舍入损失趋小；输出不保证还是某个 prefix-closed policy coefficient |
| `P2LowerFiniteCellBetaCompiler` | 实际 beta 附着、唯一 small/rough 分解、one-bound 和证明出的 physical minorant | 未将 rounded rho 等同于某项 `actualLowerSmallRoughRho P`，也未完成原 U5 总 count 接线 |
| `P2LowerFiniteCellRawDensityReserve` | rounded physical rho 的真实 density reserve，包括明确 rounding loss 与 absolute rough-density 项 | 未对原 U5 coarse 实例付清这些误差 |

这些是既有源码资产；本报告没有重新运行编译或授予其形式信用。相关 donor 文件的说明也明确保留源代码／未验收边界。

两个容易误认成完成供应者的接口另作定位：

- `CurrentChenP5OriginalU5EnhancedHarmonicTransport.tendsto_nativeEnhancedHarmonic_adoptedH248` 给原 enhanced kernel／literal adopted h248 floor 的 prime-harmonic 极限。其源码明确不据此识别实际 causal density，不提供 physical support licence。
- `P5OriginalFixedDensitySupplierAssembly.eventual_mean_of_fixed_original_grouped_suppliers` 的 U5 `h5` 仍作为输入。总装没有反向供应所需 coarse U5 密度，也不能用来代替这一义务。

已有 ordinary U5 mean 与局部 constant-level plateau 也不等于完整增强 U5 的 finite coarse 实现。本报告不重做这些已存在路线。

## 5. Raw-policy rho 与 rounded output 必须分开

通用 `∀ P` count 定理直接覆盖的是其定义中的 raw-policy-attached rho。如果采用稿件式 finite-cell rounded output，`P2LowerFiniteCellRounding` 明确保留 raw support、rounded coefficient 的区别，`P2LowerFiniteCellBetaCompiler` 也明确保留两项 physical rho。

其中 `raw_attachment_eq_actual` 证明的是 raw coefficient 扩展到共同 carrier 后的附着恒等式，不能拿它证明 rounded coefficient 等于 raw coefficient。`rho_minorant` 则确实从 rounded output 的系数比较和实际 lower tree 推出点态 minorant；它不是把最终 count 结论作为输入。

因此若采用 rounded output，有两种身份要求必须辨明：要直接使用现有任意 P 的 count 接口，必须确实识别该输出属于接口所定义的 rho 类；若不具有这项识别，则应准确接到它自己的已证明 minorant 和物理 count／mean 字典。当前已读代码未完成其原 U5 专用总接线。不得以一个自由 P 名称、未经证明的 rho 等式，或新的 admission／PP 结论假设跨过这一步。

## 6. 对工作选择的判断

合法的新路线是：从一开始选择稿内实际有限 coarse 实现；证明其同一个实际输出具有所需 count、密度与分布性质。它不要求把旧 pointwise rho 的全 discrepancy transport 当作原 count 目标必需的一步。

剩余工作应分层描述：

1. **量词和表达接线：** 已构造 P 对通用 count 的实例化，统一该 P 的 physical rho、exact mean 和 branches 参数。这属于直接逻辑接线，不能给它附加不必要的旧新 rho 等式。
2. **可复用组件：** 常量 seed 内核、first-disagreement density budget、整格舍入、beta 附着、minorant 与 raw-density reserve。无需重写其旧证明。
3. **实质供应缺项：** 实际 coarse U5 的有限选择及所需数值密度；具体误差的小量支付；若使用 rounded output，它自己的 U5 count／mean 接线；之后在该同一输出上的 whole-atom 和分布结论。

这不是已发现稿件路线矛盾，也不是只需改一个 binder 的表达错误。当前没有完成的具体 U5 供应者；`∀ P` 本身无法判断新路线比旧 literal 路线容易多少，但足以排除“任何合法替代实例都必须先证明与旧 rho 相等”这一额外要求。

## 7. 本次附存的看板只读快照

[P36_BOARD_READONLY_SNAPSHOT_20261125.json](P36_BOARD_READONLY_SNAPSHOT_20261125.json) 按 `/tmp/p36-dedup-board-nodes.json` 原字节复制，SHA-256 为 `146a269ad6720faab6b603f7601a413d7908eaa5458d3caba09618bb132fdcc9`。

读取完成时间按分钟记录为 **2026-11-25 13:20 UTC**。来源是用户看板实时页面内的 P3.6 节点树，而非总计数；站点版本 10，站点源码 `c4c1685adfdc804fac670e25ee5d26dd4f79a74c`。46 个 P3.6 子树节点均记 `sourceDate=2026-11-23`、`latestCommit=7f5330cace31383f5626da526b476dd4b0f43376`、`currentVerified=false`；其中 3 黄、43 蓝。

这一快照没有新增 acceptance，也不撤销或重审本轮其他独立已接受的证据。看板页面的 `asOf=2026-11-25` 不能改读成这 46 项源码已在当日重新验收。
