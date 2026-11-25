# 实际 U5 count 消费者的精确轻接口

**状态：源码已逐字核对，项目源码依赖已可读闭合；未进行 Lean elaboration、编译、内核或传递公理验收。** 本目录不修改标准 `ImbalancedChen/` 源码或主 `SOURCE_SELECTION.json`。它是供后续独立编译选择的 source-only overlay，不能增加 P3.6 完成信用。

## 目标与结果

目标仍是父目录的 `P3OriginalU5SelectedClassicalComplement.exists_selected_original_count_beyond_classical`：原始 `integerRho`、literal `selectedPolicy`、同一 `beyond` 载体和实际 count / medium-no-medium `branches` 均不改变。此处只搬运其既有供应者的声明与证明，不重新证明缺失模块，不改旧定理的假设或结论，也不补充 PP、共同 Q 或 (S)/(F) 输入。

原 imports 的有界读取在 594 个已发现项目节点处停止，尚有 26 个 frontier；其中四个精确登记的 GitHub blob 请求实际返回 404。完成下列纯源码抽取后，用实际输出文件重新解析 imports，获得 **444 个项目模块、444 个可读源、零 frontier**。该次快照复用了主 manifest 的 257 个源，其余包括 6 个抽取核心、5 个目标可达 compatibility patches、原有 source-only 供应者与目标候选。完整 manifest 身份和每个模块的来源、SHA256、imports 见本目录 `DEPENDENCY_PREFLIGHT.json`。

全部 6 个核心合计 **58 个原声明**，保留原 namespace、statement 和 proof body。15 个 compatibility 文件在逆转 import 调整并插回原声明后，均与其精确原件逐字节相等。独立复核结果记录于 `PRESERVATION_CHECK.json`；这是源码保真检查，不是 Lean 验收。

## 抽取清单

| 新文件 | 原声明数 | 搬运内容及实际消费者 |
|---|---:|---|
| `P5OriginalU5ScalarSmoothCutoffs` | 12 | `ActualEtaPsiOccurrenceBudget` 的 eta/chi 六个基本声明，以及 `ActualSingletonPrimeTestFamily` 的 chi/chiLog 六个基本声明。供真实 smooth singleton 和原 HB chart 使用；不包含 occurrence/Euler budget。 |
| `P5OriginalU5LogCollarBasic` | 17 | 原 narrow log-collar 的 profile、smoothness、值域、精确支撑、logWidth 和 `singletonLicence`。保留原函数定义及全部被调用证明。 |
| `P5OriginalU5NarrowSingletonBasic` | 11 | `smoothNatural`、`fullSmoothWeight`、`actualLicence`、上下端 reserve 及 `original_source_exact_reserves`。供 `P5OriginalU5AllMarkSmoothing` 使用。 |
| `P5WordKernelSignedRow` | 1 | `P4BActualUpperTrimPayment.wordKernel_eq_signedRow` 的原 statement/body。它是 U5 HB reserve 对 broad upper-trim 模块的实际直接调用。 |
| `P1SharpPrimeEndpointDefinitions` | 4 | 原 `cut`、`primeMass`、`densityTest`、`sharpPrimeError`，仍处于各自原 namespace。原 Pan-BV payment 证明保持不动，只改 import。 |
| `P2OriginalU5PlateauRectangle` | 13 | 原 `Pair` 别名及 plateau rectangle 的十二个定义/几何声明，止于 `rectangle_rootQ`；全部源自现有原件。供原 `P5OriginalU5PlateauPrimeBV` 使用。 |

每一条声明的原始字节区间、声明名、源 SHA256、目标核心及正文 SHA256 均在 `PRESERVATION.json`。该清单是完整清单，不以这里的概要代替精确记录。

`cores/ImbalancedChen/` 含新核心；`compatibility/ImbalancedChen/` 含原模块的可逆替换副本。目标可达的五个 patch 是：

- `P5OriginalU5AllMarkSmoothing`：导入 narrow singleton 核心。
- `P5OriginalPrimeAllGroupHBDiscrepancy`：导入标量 eta/chi 核心。
- `P5OriginalU5AllMarkHBReserves`：导入 kernel dictionary 核心，并显式补齐既有 signed-modulus / polynomial-divisor 依赖。
- `P1Full87SharpClassicalCut`：导入四个 endpoint 定义及现有 BV / log 基础模块；两条原证明不变。
- `P5OriginalU5PlateauPrimeBV`：导入 plateau rectangle 核心。

其余十个 compatibility 副本保留完整旧模块的剩余声明，用于维持原导入入口；它们没有被强行加入本目标的编译闭包，也没有获得编译信用。

## 四个 404 为什么可以离开本次闭包

前三个模块——`P5ActualFourNativeBoxFullNorm`、`P5OriginalFourSelectedSmoothWBindingGap`、`P5PositiveFourProfileLocalZeroSmooth`——都由 `P5NativeSelectedFourIntegerProfile` 导入。原 singleton 模块经过 `P5NativeSelectedFourOrderedEuler` 间接引入这一整条 rank-four 链。原 singleton 的 Euler budget 确实使用其中的通用 chart dictionary，不能只删 import 后声称等价。

第四个 `P5AllWordAmbientOccurrenceBound` 供应真正使用的 occurrence calculus。原 `singleton_mixedEuler` / `collar_mixedEuler` 使用 `occWord_four_bound`；`orderedEuler_occurrence_dictionary` 和 `logWidth_occurrence_budget` 使用 `occWord_ambient`。因此它不能因为名字含有 four-profile 就被视作无用。仅搬出 `NativeSelectedFourOrderedEuler` 的通用块仍绕不开它。

本次 count→branches 路径需要的接口较小。对 `P5OriginalU5AllMarkSmoothing`、`P5OriginalU5AllMarkHBReserves`、`P5OriginalU5ShortComplement` 和 `P5OriginalU5ClassicalComplement` 的正文核对显示，它们使用 narrow profile 的值域、支撑、smooth licence 及原有限 HB 恒等式；没有调用 `mixedEuler` 或 `actual_family_fields`。本次只把这些已存在的基本声明搬到轻模块；原 Euler/occurrence 证明仍完整留在 compatibility 原入口。

另外，HB discrepancy 模块原本通过 `P5ActualEtaPsiOccurrenceBudget` 的宽 import 再次进入 occurrence 链。它实际使用的是原 eta/chi 及 `eta_zero`/`eta_one`；改为同 namespace 的标量核心后，这条第二入口也被关闭。没有新造 `occWord` 定义，没有替代遗失证明。

## 两项明确的接口检查

`P5LicensedOriginalIntegerProfile.Licence` 在固定原件中只有三个字段：

```lean
ambient : (Fin k → ℝ) → ℝ
smooth : ContDiff ℝ ∞ ambient
agrees_on_primes : ∀ u : Fin k → ℕ, (∀ i, (u i).Prime) →
  ambient (fun i => (u i : ℝ)) = Wprime u
```

这里没有隐藏的 `mixedEuler`、budget 或 factorization 字段。新核心的 `singletonLicence` 是原来的三字段构造；其 `profile_smooth` 原证明仅用 eta/chiLog 的基本光滑性及局部恒等，不使用导数预算。

`wordKernel_eq_signedRow` 原证明只展开原 `wordKernel`、`signedRow`、`signedKernel`，并调用公开的 `IndependentPrimeSourceWordDictionary.residueKernel_real`。该公开供应者在原文件中紧随 `wordKernel`；不是被删除的 private helper。该定理的两个精确 imports 已直接保留。

## P1 与 plateau 两处额外宽 import

原 `P1Full87SharpClassicalCut.exists_pan_sharp_payment` 通过 `P1OriginalSharpFiniteReceiver` 导入大量 full87 账本，包括存在版本歧义的 `CentreFrozenHN`。正文只需要原四个 endpoint 定义以及既有 Pan-BV 和 reciprocal-totient/log 供应者。两个 endpoint 原件的唯一 blob 已由多份固定 registry 交叉定位并精确取回，四定义逐字搬运后，原 Pan payment 的 statement/body 完全未动。`CentreFrozenHN` 的版本没有被猜选。

同样，原 `P2GammaU5PlateauGeometry` 的 `rectangle_rootQ` 之前的矩形几何只需要原 `Pair`、原 rootQ、原 U5 coordinates 和 prime-box 库。相对误差 `P2GammaSelectedRelativeLogSaving` 由该文件的其他 root-fibre 定理导入。实际 U5 receiver 不消费那些定理，所以只搬运实际矩形声明；保留 Pair 别名的精确来源，未用新定义替换它。

## 关键源 pin

这里 `archive` 指 `2dbe821e7f6eabc4fd7ec4de793d4e243c1df02b`；全部路径与 blob 的完整逐模块记录在 `PRESERVATION.json`。

| 原模块或接口 | 原始路径 / 精确来源 |
|---|---|
| eta/chi 基础 | archive 的 `docs/source-only/20261028-resume-30c/pp_derivatives/P5ActualEtaPsiOccurrenceBudget.lean`，blob `ce098bfa1466350290d4a4c82b4ca78c7ec20de3`。 |
| chiLog 基础 | archive 的 `docs/source-only/20261028-resume-30f/pp_derivatives/P5ActualSingletonPrimeTestFamily.lean`，blob `f5124e445fcda247a98d67573f0a8840cda6fd16`。 |
| log-collar 基础 | archive 的 `docs/source-only/20261028-resume-30f/pp_derivatives/P5ActualSingletonLogCollarFamily.lean`，blob `b095c7130b921cf51b42d619467cb70ff01b8191`。 |
| narrow singleton reserves | archive 的 `docs/source-only/20261028-resume-30f/transfer_lambda/P5CanonicalTentNarrowSingletonTransfer.lean`，blob `ceed27efe214cf794464fd7466aea18fa810bd37`。 |
| kernel dictionary | archive 的 `docs/source-only/20261102-resume-30s/S/s19_actual_upper_pp/P4BActualUpperTrimPayment.lean`，blob `c02493f52e5fdf3eb31a6fe20f9f185f7364773a`。 |
| `cut` | archive 的 `docs/source-only/20261112-resume/t03/physical-reserve-next/P1OriginalSharpFiniteReceiver.lean`，blob `909b794ad58dd9bd016c8dc2faa2d91852f99158`。 |
| `primeMass` / `densityTest` | `a023ae055d3d90738f6965a2848266aa13089faf:docs/source-only/20261105-full87-eighth-arithmetic/P4AOriginalFull87EighthPrimeMeanLedger.lean`，blob `7ebef5ea7baf3a79180f4d086a6f05530c0eb827`。 |
| `sharpPrimeError` | `a023ae055d3d90738f6965a2848266aa13089faf:docs/source-only/20261111-full87-signed-sharp-recenter/P4AOriginalFull87SignedSharpReceiver.lean`，blob `74949535b1ae9e5a46e6f9e12432f412fead4b03`。 |
| `Pair` | `f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784:docs/source-only/20261103-p3-selected-theta/P2GammaSelectedPhysicalTheta.lean`，blob `ba93f8ca52acce8988b845308c2b99740720325f`。 |
| plateau rectangle | 既有精确 blob `e97d2fb24f191694a39cb23ccea3417a1f541d98`，SHA256 `55663a73ad99fa71c82eeeccab2a2ebed507b436330a549cd2acdd18b034d6ab`；原路径 locator 尚未升级为已核对 commit/path，故以已验证 blob 为 pin。 |
| `Licence` | `298670f119d24874b719facb3ef756f1e01223a1:ImbalancedChen/P5LicensedOriginalIntegerProfile.lean`，blob `58286fe03462dc395da0ecf96ba42a89c7f87751`。 |
| `residueKernel_real` | archive 的 `docs/source-only/20261028-resume-30f/pp_fourier/P5IndependentPrimeSourceWordDictionary.lean`，blob `b16405e7466f4e190b694944b01fe6a8594d5cd2`。 |

## 可复核文件与界限

- `PRESERVATION.json`：58 个原声明和 15 个可逆 patch 的完整来源及字节区间。
- `verify_preservation.py`：只读检查，接受原 blob 缓存或 Git 对象库；禁止隐式网络拉取，不调用 Lean。
- `PRESERVATION_CHECK.json`：本次独立字节检查输出。
- `DEPENDENCY_PREFLIGHT.json`：基于实际 overlay imports 的完整可读项目源闭包、当前主 manifest 快照和每个源的 SHA256。
- `CLOSURE_GUARD.json`：闭包、循环、源哈希和禁止命令检查；仍不是形式化验收。

外部 `Mathlib` / `MathlibNt` 编译缓存和工具链相容性未由本目录预检认证。后续应在这些真实源码上编译及做 kernel / transitive-axiom 检查；不能以本次 hash/graph 检查代替。此 overlay 的存在也不表示完整 P3.6、P3.5、PP 或实际未付分支已获证明。
