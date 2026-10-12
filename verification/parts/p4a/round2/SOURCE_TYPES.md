# SOURCE_EXTRACTED_NOT_COMPILER_INVENTORY

## 源码提取的完整类型；本文件本身不声称编译成功，编译器确认见最终 inventory

提取时间：2026-10-12T17:57:24.689668+00:00。

本文件逐字提取当前五个 Part 4 工作树源码中的全部 **53 个公开 theorem** 的完整 signature。保留所有显式和隐式参数、量词、前提、let 绑定与结论；去掉 `:= by` 和证明体。本次没有运行 Lean、原版 replay、axiom audit 或 CI。

root 通知五个源码的证明修复完成、内容稳定后，本文件计算并记录了实际源码 SHA256 与 Git blob SHA1。源码指纹不代表编译成功；真实 strict compile、原版 replay、axiom audit 及其固定提交由最终 inventory 确认。`SOURCE_TYPES.json` 同时保存原始 signature 和完整限定声明名的 qualified_signature。

所有声明均来自 `namespace ImbalancedChen`。下方标题和代码块中的定理名均加上完整 `ImbalancedChen.` 限定；参数、量词、前提及结论逐字保留。JSON 的 signature 字段另外保留原始源码声明名。其余短标识符按原 ImbalancedChen 命名空间解释；阅读完整限定代码块时可采用 `open ImbalancedChen`、`open scoped BigOperators`、`open Filter Topology` 的上下文。各模块列出原 imports。这只是源码接口摘录，不是编译器全名展开、新的 Lean 声明或独立可编译文件。

| 模块 | 公开 theorem 数 |
|---|---:|
| `ImbalancedChen/ActualUpperPolicyDensity.lean` | 13 |
| `ImbalancedChen/UpperCoefficientPerturbation.lean` | 6 |
| `ImbalancedChen/ActualUpperDensityAssembly.lean` | 7 |
| `ImbalancedChen/RealPhysicalUpperWeightBridge.lean` | 26 |
| `ImbalancedChen/RealUpperCountingAssembly.lean` | 1 |


## 源码内容身份（不是编译验证）

源码哈希计算时间：2026-10-12T18:00:00.880460+00:00。

本次提取不宣称源码属于某个已验证 commit；根代理负责 Git 恢复与最终提交绑定。以下哈希标识本次实际读取的五个源码内容。

| 源文件 | SHA256 | Git blob SHA1 |
|---|---|---|
| `ImbalancedChen/ActualUpperPolicyDensity.lean` | `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6` | `487f13707ee13159cd7f161879b5a2e44ffb8c19` |
| `ImbalancedChen/UpperCoefficientPerturbation.lean` | `e4d1d84fa128f7f84fb4f7d4f0b03acf8401312de1ceaed045de3aaf3b5d6e86` | `7b024033e58e19c0dcf94de322d6cb7d6815d987` |
| `ImbalancedChen/ActualUpperDensityAssembly.lean` | `659aa3d8cfa50345f912ba070e30cd57a6caa1738e4146d1c051a7506f944cec` | `e363dee459e99b2be6f83f2c70b15f8968fd4817` |
| `ImbalancedChen/RealPhysicalUpperWeightBridge.lean` | `8a86c2e7fd2383fcae243b5958f3447675a4f5b7a4c9078ba1ba832ea067878f` | `c774859dab0bdcfc1266200d7437a62d0c69e5ea` |
| `ImbalancedChen/RealUpperCountingAssembly.lean` | `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96` | `6e6843444cafa0e1d51a903981da0092983d2ac0` |

## 必需接口覆盖

| 接口 | 完整限定声明名 |
|---|---|
| policy／同一实际权等式 | `ImbalancedChen.actualSmallRoughRho_eq_firstExitAttachment` |
| 同一 raw density | `ImbalancedChen.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained` |
| absolute physical density perturbation | `ImbalancedChen.abs_physicalDensitySum_smallRoughRho_sub_le` |
| raw reserve 存在式 | `ImbalancedChen.exists_actualSmallRoughRho_density_le_of_full_policy_limits` |
| compiler budget | `ImbalancedChen.compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget` |
| real finite 分解 | `ImbalancedChen.sum_rho_mul_realHalfProductCongruenceMass_eq` |
| 编译后 actual majorant | `ImbalancedChen.actualAttachedRho_majorant_of_rough_domination` |
| actual rho 的 ceil majorant | `ImbalancedChen.actualSmallRoughRho_sieveProduct_majorant` |
| coprime-zero gate | `ImbalancedChen.realPhysicalCoprimeCorrection_eq_zero_of_gate` |
| outer source 有限式 | `ImbalancedChen.RealB_cast_le_same_rho_outer_main_add_errors` |
| 最终 same-rho 条件式 hUpper | `ImbalancedChen.eventually_RealB_le_currentK_log_of_same_rho_inputs` |

## ImbalancedChen.ActualUpperPolicyDensity

来源：`ImbalancedChen/ActualUpperPolicyDensity.lean`。

```lean
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.ActualSelectedPrefixOwnCubeIntegral
import ImbalancedChen.FirstExitHistoricalLevels
```

### ImbalancedChen.oddFirstExitPolicy_eq_of_even_retained

```lean
theorem ImbalancedChen.oddFirstExitPolicy_eq_of_even_retained {α : Type*}
    (retained : Bool → List α → Bool)
    (heven : ∀ pre, retained true pre = true) :
    oddFirstExitPolicy (retained false) = retained
```

### ImbalancedChen.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained

```lean
theorem ImbalancedChen.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport (retained false) N cap w z =
      firstExitRetainedModuli retained (roughPrimeUniverse N cap w z)
```

### ImbalancedChen.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained

```lean
theorem ImbalancedChen.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retained false) N cap w z d =
      (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ)
```

### ImbalancedChen.actualSmallRoughModuli_eq_firstExitAttachment

```lean
theorem ImbalancedChen.actualSmallRoughModuli_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    actualSmallRoughModuli (retained false) N cap w z =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
```

### ImbalancedChen.actualSmallRoughRho_eq_firstExitAttachment

```lean
theorem ImbalancedChen.actualSmallRoughRho_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (retained false) N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient retained
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
```

### ImbalancedChen.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained

```lean
theorem ImbalancedChen.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial retained
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z)
```

### ImbalancedChen.fixedRoughDensity_nonneg

```lean
theorem ImbalancedChen.fixedRoughDensity_nonneg
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    0 ≤ reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
      (fixedRoughCoefficient retainOdd N cap w z)
```

### ImbalancedChen.firstExitDepthSplicePolicy_even_retained

```lean
theorem ImbalancedChen.firstExitDepthSplicePolicy_even_retained {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hreplacement : ∀ pre, replacement true pre = true) (pre : List α) :
    firstExitDepthSplicePolicy k parent replacement true pre = true
```

### ImbalancedChen.actualSelectedPrefixSplicePolicy_upper_even

```lean
@[simp] theorem ImbalancedChen.actualSelectedPrefixSplicePolicy_upper_even {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (pre : List ℕ) :
    actualSelectedPrefixSplicePolicy false N I old nu a b m J true pre = true
```

### ImbalancedChen.thirdCappedUpperPolicy_even_retained

```lean
theorem ImbalancedChen.thirdCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    thirdCappedUpperPolicy base Q3 true pre = true
```

### ImbalancedChen.fourthCappedUpperPolicy_even_retained

```lean
theorem ImbalancedChen.fourthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fourthCappedUpperPolicy base Q3 Q4 true pre = true
```

### ImbalancedChen.fifthCappedUpperPolicy_even_retained

```lean
theorem ImbalancedChen.fifthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fifthCappedUpperPolicy base Q3 Q5 true pre = true
```

### ImbalancedChen.actualSelectedPrefixUpperDensity_eq_fixedRoughDensity

```lean
theorem ImbalancedChen.actualSelectedPrefixUpperDensity_eq_fixedRoughDensity
    (N cap : ℕ) (I : Finset (Fin 5)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) :
    actualSelectedPrefixUpperDensity N cap I old nu a b m J =
      reciprocalTotientDensity
        (fixedRoughSupport
          (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J false)
          N cap 0 ((N : ℝ) ^ (b : ℝ)))
        (fixedRoughCoefficient
          (actualSelectedPrefixSplicePolicy false (N : ℝ) I old nu a b m J false)
          N cap 0 ((N : ℝ) ^ (b : ℝ)))
```

## ImbalancedChen.UpperCoefficientPerturbation

来源：`ImbalancedChen/UpperCoefficientPerturbation.lean`。

```lean
import ImbalancedChen.ActualSmallRoughAttachment
```

### ImbalancedChen.abs_signAttachedValue_sub_le

```lean
theorem ImbalancedChen.abs_signAttachedValue_sub_le
    {c d lo hi M : ℝ} (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signAttachedValue c lo hi - signAttachedValue d lo hi| ≤ M * |c - d|
```

### ImbalancedChen.signSensitiveReciprocalTotientDensity_eq_sum_attached

```lean
theorem ImbalancedChen.signSensitiveReciprocalTotientDensity_eq_sum_attached
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity rough c lo hi =
      ∑ d ∈ rough, signAttachedValue (c d) lo hi / (Nat.totient d : ℝ)
```

### ImbalancedChen.abs_signSensitiveReciprocalTotientDensity_sub_le

```lean
theorem ImbalancedChen.abs_signSensitiveReciprocalTotientDensity_sub_le
    (rough : Finset ℕ) (compiled raw : ℕ → ℝ) {lo hi M : ℝ}
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signSensitiveReciprocalTotientDensity rough compiled lo hi -
        signSensitiveReciprocalTotientDensity rough raw lo hi| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)
```

### ImbalancedChen.abs_physicalDensitySum_smallRoughRho_sub_le

```lean
theorem ImbalancedChen.abs_physicalDensitySum_smallRoughRho_sub_le
    {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) {M : ℝ}
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M) :
    |physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough compiled betaMinus betaPlus) -
        physicalDensitySum (smallRoughModuli small rough)
          (smallRoughRho small rough raw betaMinus betaPlus)| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)
```

### ImbalancedChen.supportedDivisorSum_le_of_coefficient_le

```lean
theorem ImbalancedChen.supportedDivisorSum_le_of_coefficient_le
    (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d) (n : ℕ) :
    supportedDivisorSum rough raw n ≤ supportedDivisorSum rough compiled n
```

### ImbalancedChen.actualAttachedRho_majorant_of_rough_domination

```lean
theorem ImbalancedChen.actualAttachedRho_majorant_of_rough_domination
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (hraw : ∀ n : ℤ, actualIntervalRoughIndicator N w z n ≤
      supportedDivisorSum rough raw n.natAbs)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough compiled
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) n.natAbs
```

## ImbalancedChen.ActualUpperDensityAssembly

来源：`ImbalancedChen/ActualUpperDensityAssembly.lean`。

```lean
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.UpperCoefficientPerturbation
import ImbalancedChen.CurrentNumericalTransfer
```

### ImbalancedChen.sourceMassScale_mul_densityScale

```lean
theorem ImbalancedChen.sourceMassScale_mul_densityScale (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)) = singularNormalization N
```

### ImbalancedChen.densityScale_pos

```lean
theorem ImbalancedChen.densityScale_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < singularSeries N / Real.log (N : ℝ)
```

### ImbalancedChen.density_le_manuscriptScale_iff_normalized

```lean
theorem ImbalancedChen.density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient
```

### ImbalancedChen.same_rho_normalized_mainTerm

```lean
theorem ImbalancedChen.same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

### ImbalancedChen.exists_actualSmallRoughRho_density_le_of_full_policy_limits

```lean
theorem ImbalancedChen.exists_actualSmallRoughRho_density_le_of_full_policy_limits
    (nu sieveR epsilonMax rawBound densityCap : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < densityCap) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          densityCap * (singularSeries N / Real.log (N : ℝ))
```

### ImbalancedChen.exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits

```lean
theorem ImbalancedChen.exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
    (nu sieveR epsilonMax rawBound : ℝ)
    (hnu : 0 < nu) (hr : 0 < sieveR) (hepsilonMax : 0 < epsilonMax)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (integral : ℝ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * sieveR) ≤ (cap N : ℝ))
    (hIntegral : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR)))
          (fixedRoughCoefficient (retainOdd epsilon N) N (cap N) 0
            ((N : ℝ) ^ (nu * sieveR))) *
          Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
        (𝓝 (integral epsilon)))
    (hCertificate : ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilonMax →
      integral epsilon ≤ rawBound)
    (hgap : rawBound < currentK) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ sieveR ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (nu * sieveR)
        let L := (N : ℝ) ^ (nu * epsilon)
        physicalDensitySum (actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
            (actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L) ≤
          currentK * (singularSeries N / Real.log (N : ℝ))
```

### ImbalancedChen.compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget

```lean
theorem ImbalancedChen.compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
    {N : ℕ} (hN : 2 ≤ N) {w : ℝ} {small rough : Finset ℕ}
    (hsmall : ∀ d ∈ small, SmallPrimeSupportedAt w d)
    (hrough : ∀ d ∈ rough, RoughPrimeSupportedAt w d)
    (compiled raw betaMinus betaPlus : ℕ → ℝ) (M rawBound compilerReserve : ℝ)
    (hminus : |reciprocalTotientDensity small betaMinus| ≤ M)
    (hplus : |reciprocalTotientDensity small betaPlus| ≤ M)
    (hraw : physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough raw betaMinus betaPlus) ≤
      rawBound * (singularSeries N / Real.log (N : ℝ)))
    (hcompiler : M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
      compilerReserve * (singularSeries N / Real.log (N : ℝ)))
    (hbudget : rawBound + compilerReserve ≤ currentK) :
    physicalDensitySum (smallRoughModuli small rough)
        (smallRoughRho small rough compiled betaMinus betaPlus) *
        Real.log (N : ℝ) / singularSeries N ≤ currentK
```

## ImbalancedChen.RealPhysicalUpperWeightBridge

来源：`ImbalancedChen/RealPhysicalUpperWeightBridge.lean`。

```lean
import ImbalancedChen.PhysicalUpperWeightBridge
import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.CurvedRegionDiscrepancy
import ImbalancedChen.ActualSmallRoughAttachment
```

### ImbalancedChen.realHalfProductSource_filter_dvd_eq_filter_modEq

```lean
theorem ImbalancedChen.realHalfProductSource_filter_dvd_eq_filter_modEq
    (b : ℝ) (N d : ℕ) (T : ℝ) :
    (realHalfProductSource b N T).filter (fun m : ℕ => d ∣ N - m) =
      (realHalfProductSource b N T).filter (fun m : ℕ => Nat.ModEq d m N)
```

### ImbalancedChen.sum_physicalDivisorSum_realHalfProductSource

```lean
theorem ImbalancedChen.sum_physicalDivisorSum_realHalfProductSource
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d
```

### ImbalancedChen.sum_rho_mul_realHalfProductCongruenceMass_eq

```lean
theorem ImbalancedChen.sum_rho_mul_realHalfProductCongruenceMass_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) =
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

### ImbalancedChen.mem_realSiftedHalfProductSource

```lean
@[simp] theorem ImbalancedChen.mem_realSiftedHalfProductSource {b T : ℝ} {N m z : ℕ} :
    m ∈ realSiftedHalfProductSource b N T z ↔
      m ∈ realHalfProductSource b N T ∧
        Nat.Coprime (N - m) (sieveProduct N z)
```

### ImbalancedChen.realSiftedHalfProductSource_card_le_sum_physicalDivisorSum

```lean
theorem ImbalancedChen.realSiftedHalfProductSource_card_le_sum_physicalDivisorSum
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m)
```

### ImbalancedChen.realSiftedHalfProductSource_card_le_same_rho_main_add_errors

```lean
theorem ImbalancedChen.realSiftedHalfProductSource_card_le_same_rho_main_add_errors
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

### ImbalancedChen.realHalfProductSource_primePartner_card_le_realSifted_add_cap

```lean
theorem ImbalancedChen.realHalfProductSource_primePartner_card_le_realSifted_add_cap
    (b : ℝ) (N z : ℕ) (T : ℝ) :
    ((realHalfProductSource b N T).filter
      (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
      (realSiftedHalfProductSource b N T z).card + z
```

### ImbalancedChen.RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff

```lean
theorem ImbalancedChen.RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (hb : b < 1) (hT : 0 ≤ T) :
    (RealB b N : ℝ) ≤
      ((realSiftedHalfProductSource b N T z).card : ℝ) + (z : ℝ) + (T + 1)
```

### ImbalancedChen.RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff

```lean
theorem ImbalancedChen.RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      (∑ m ∈ realHalfProductSource b N T,
        physicalDivisorSum Q rho (N - m)) + (z : ℝ) + (T + 1)
```

### ImbalancedChen.RealB_cast_le_same_rho_main_add_errors

```lean
theorem ImbalancedChen.RealB_cast_le_same_rho_main_add_errors
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho + (z : ℝ) + (T + 1)
```

### ImbalancedChen.realHalfProductSource_prime_divisor_rough

```lean
theorem ImbalancedChen.realHalfProductSource_prime_divisor_rough
    {b T : ℝ} {N m ell : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hm : m ∈ realHalfProductSource b N T)
    (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    T ^ (b / (1 + b)) < (ell : ℝ)
```

### ImbalancedChen.realHalfProductSource_coprime_of_dvd_sieveProduct

```lean
theorem ImbalancedChen.realHalfProductSource_coprime_of_dvd_sieveProduct
    {b T : ℝ} {N m z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime m d
```

### ImbalancedChen.realHalfProductCoprimeMass_eq_card_of_gate

```lean
theorem ImbalancedChen.realHalfProductCoprimeMass_eq_card_of_gate
    {b T : ℝ} {N z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b))) (hd : d ∣ sieveProduct N z) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ)
```

### ImbalancedChen.realPhysicalCoprimeCorrection_eq_zero_of_gate

```lean
theorem ImbalancedChen.realPhysicalCoprimeCorrection_eq_zero_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realPhysicalCoprimeCorrection b N T Q rho = 0
```

### ImbalancedChen.RealB_cast_le_same_rho_main_add_distribution_of_gate

```lean
theorem ImbalancedChen.RealB_cast_le_same_rho_main_add_distribution_of_gate
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalDistributionError b N T Q rho + (z : ℝ) + (T + 1)
```

### ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass

```lean
theorem ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d
```

### ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors

```lean
theorem ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d
```

### ImbalancedChen.RealB_cast_le_same_rho_outer_main_add_errors

```lean
theorem ImbalancedChen.RealB_cast_le_same_rho_outer_main_add_errors
    {b T : ℝ} (N z : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hSN : ∀ m ∈ S, m ≤ N)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) +
        (z : ℝ) + (T + 1)
```

### ImbalancedChen.actualSmallPrimeFinset_eq_sievePrimes_ceil

```lean
theorem ImbalancedChen.actualSmallPrimeFinset_eq_sievePrimes_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z)
```

### ImbalancedChen.actualSmallPrimeProduct_eq_sieveProduct_ceil

```lean
theorem ImbalancedChen.actualSmallPrimeProduct_eq_sieveProduct_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z)
```

### ImbalancedChen.actualSmallRoughIndicator_eq_sieveProduct_natAbs

```lean
theorem ImbalancedChen.actualSmallRoughIndicator_eq_sieveProduct_natAbs
    (N : ℕ) (z : ℝ) (n : ℤ) :
    actualSmallRoughIndicator N z n =
      if Nat.Coprime n.natAbs (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0
```

### ImbalancedChen.actualSmallRoughRho_sieveProduct_majorant

```lean
theorem ImbalancedChen.actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

### ImbalancedChen.actualSmallRosserSupport_dvd_sieveProduct_ceil

```lean
theorem ImbalancedChen.actualSmallRosserSupport_dvd_sieveProduct_ceil
    (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### ImbalancedChen.fixedRoughSupport_dvd_sieveProduct_ceil

```lean
theorem ImbalancedChen.fixedRoughSupport_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### ImbalancedChen.actualSmallRoughModuli_dvd_sieveProduct_ceil

```lean
theorem ImbalancedChen.actualSmallRoughModuli_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### ImbalancedChen.RealB_cast_le_actualSmallRoughRho_main_add_errors

```lean
theorem ImbalancedChen.RealB_cast_le_actualSmallRoughRho_main_add_errors
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalCoprimeCorrection b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalDistributionError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) + (Nat.ceil z : ℝ) + (T + 1)
```

## ImbalancedChen.RealUpperCountingAssembly

来源：`ImbalancedChen/RealUpperCountingAssembly.lean`。

```lean
import ImbalancedChen.ActualUpperDensityAssembly
import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.PowerErrorBudget
```

### ImbalancedChen.eventually_RealB_le_currentK_log_of_same_rho_inputs

```lean
theorem ImbalancedChen.eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N
```

## 接收 Part 与最小未闭合输入

- **P1 → P4：**完整 adopted policy／compiler 的实例、合法性及支持许可；实际零延拓必须保持同一 raw coefficient、相同 small weights 与相同参数。
- **P2 → P4：**对应完整实际 policy 的 `hIntegral`／`hCertificate`、留有 compiler reserve 的全量数值上界，以及同一 carrier 上的实际 compiler budget。若主项以 `log D` 表示且 `D=N^nu`，到 `log N` 的系数为 `U/nu`。
- **P3 → P4：**相同精度下相同 `Q delta N`／`rho delta N` 的 distribution 与合法平滑外逼近转换，覆盖这里指定的真实有序源和截断。
- **P4 → P5：**这里提供准确接口；实际 K 密度结论和无条件 hUpper 须在解析输入闭合且真实验证后另行交付。条件式本身不宣称交付 A／B 已完成。
- **P0／验证整合：**最终 inventory 负责精确源码身份、真实 strict compile、原版 replay 和 axiom audit；本文不替代这些证据。

互素修正归零仍保留 cutoff gate 与所有非零系数的除尽支持。最终 hUpper 允许权依精度 delta 变化，但同一 delta 的 majorant、density、coprime correction 与 distribution 全部使用同一权。有限式保留 ceil 截断及端点项，全部签名没有 hLower 依赖。

已有 small Rosser density sandwich 可用于取得 M 的有限上界；不应把这个可复用有限推论重复列为 P2 新解析缺口。共同 carrier 的有限适配候选单列于 `COMMON_CARRIER_CANDIDATE.lean.txt`，尚未编译、尚非生产代码，不属于本次 53 个现有声明。
