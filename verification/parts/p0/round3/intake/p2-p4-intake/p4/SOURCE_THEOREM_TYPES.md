# P4 固定候选完整源码签名

这些是固定源码提取，不是编译器确认类型。固定提交 `3d5dd058cf6bef5fe90719ee277580baf8b5bf41`；生产源码仍同 `262f69822a386a9d44efc059bceba11049668d68`。

## ActualUpperPolicyDensity

Source SHA256: `16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`

### oddFirstExitPolicy_eq_of_even_retained

```lean
theorem oddFirstExitPolicy_eq_of_even_retained {α : Type*}
    (retained : Bool → List α → Bool)
    (heven : ∀ pre, retained true pre = true) :
    oddFirstExitPolicy (retained false) = retained
```

### fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained

```lean
theorem fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport (retained false) N cap w z =
      firstExitRetainedModuli retained (roughPrimeUniverse N cap w z)
```

### fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained

```lean
theorem fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retained false) N cap w z d =
      (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ)
```

### actualSmallRoughModuli_eq_firstExitAttachment

```lean
theorem actualSmallRoughModuli_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    actualSmallRoughModuli (retained false) N cap w z =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
```

### actualSmallRoughRho_eq_firstExitAttachment

```lean
theorem actualSmallRoughRho_eq_firstExitAttachment
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

### firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained

```lean
theorem firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial retained
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z)
```

### fixedRoughDensity_nonneg

```lean
theorem fixedRoughDensity_nonneg
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    0 ≤ reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
      (fixedRoughCoefficient retainOdd N cap w z)
```

### firstExitDepthSplicePolicy_even_retained

```lean
theorem firstExitDepthSplicePolicy_even_retained {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hreplacement : ∀ pre, replacement true pre = true) (pre : List α) :
    firstExitDepthSplicePolicy k parent replacement true pre = true
```

### actualSelectedPrefixSplicePolicy_upper_even

```lean
@[simp] theorem actualSelectedPrefixSplicePolicy_upper_even {d : ℕ} (N : ℝ)
    (I : Finset (Fin d)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1))) (pre : List ℕ) :
    actualSelectedPrefixSplicePolicy false N I old nu a b m J true pre = true
```

### thirdCappedUpperPolicy_even_retained

```lean
theorem thirdCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    thirdCappedUpperPolicy base Q3 true pre = true
```

### fourthCappedUpperPolicy_even_retained

```lean
theorem fourthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fourthCappedUpperPolicy base Q3 Q4 true pre = true
```

### fifthCappedUpperPolicy_even_retained

```lean
theorem fifthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fifthCappedUpperPolicy base Q3 Q5 true pre = true
```

### actualSelectedPrefixUpperDensity_eq_fixedRoughDensity

```lean
theorem actualSelectedPrefixUpperDensity_eq_fixedRoughDensity
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

## UpperCoefficientPerturbation

Source SHA256: `59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`

### abs_signAttachedValue_sub_le

```lean
theorem abs_signAttachedValue_sub_le
    {c d lo hi M : ℝ} (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signAttachedValue c lo hi - signAttachedValue d lo hi| ≤ M * |c - d|
```

### signSensitiveReciprocalTotientDensity_eq_sum_attached

```lean
theorem signSensitiveReciprocalTotientDensity_eq_sum_attached
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity rough c lo hi =
      ∑ d ∈ rough, signAttachedValue (c d) lo hi / (Nat.totient d : ℝ)
```

### abs_signSensitiveReciprocalTotientDensity_sub_le

```lean
theorem abs_signSensitiveReciprocalTotientDensity_sub_le
    (rough : Finset ℕ) (compiled raw : ℕ → ℝ) {lo hi M : ℝ}
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signSensitiveReciprocalTotientDensity rough compiled lo hi -
        signSensitiveReciprocalTotientDensity rough raw lo hi| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)
```

### abs_physicalDensitySum_smallRoughRho_sub_le

```lean
theorem abs_physicalDensitySum_smallRoughRho_sub_le
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

### supportedDivisorSum_le_of_coefficient_le

```lean
theorem supportedDivisorSum_le_of_coefficient_le
    (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d) (n : ℕ) :
    supportedDivisorSum rough raw n ≤ supportedDivisorSum rough compiled n
```

### actualAttachedRho_majorant_of_rough_domination

```lean
theorem actualAttachedRho_majorant_of_rough_domination
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

## ActualUpperDensityAssembly

Source SHA256: `241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`

### sourceMassScale_mul_densityScale

```lean
theorem sourceMassScale_mul_densityScale (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)) = singularNormalization N
```

### densityScale_pos

```lean
theorem densityScale_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < singularSeries N / Real.log (N : ℝ)
```

### density_le_manuscriptScale_iff_normalized

```lean
theorem density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient
```

### same_rho_normalized_mainTerm

```lean
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

### exists_actualSmallRoughRho_density_le_of_full_policy_limits

```lean
theorem exists_actualSmallRoughRho_density_le_of_full_policy_limits
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

### exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits

```lean
theorem exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits
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

### compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget

```lean
theorem compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget
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

## RealPhysicalUpperWeightBridge

Source SHA256: `f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`

### realHalfProductSource_filter_dvd_eq_filter_modEq

```lean
theorem realHalfProductSource_filter_dvd_eq_filter_modEq
    (b : ℝ) (N d : ℕ) (T : ℝ) :
    (realHalfProductSource b N T).filter (fun m : ℕ => d ∣ N - m) =
      (realHalfProductSource b N T).filter (fun m : ℕ => Nat.ModEq d m N)
```

### sum_physicalDivisorSum_realHalfProductSource

```lean
theorem sum_physicalDivisorSum_realHalfProductSource
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d
```

### sum_rho_mul_realHalfProductCongruenceMass_eq

```lean
theorem sum_rho_mul_realHalfProductCongruenceMass_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) =
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

### mem_realSiftedHalfProductSource

```lean
@[simp] theorem mem_realSiftedHalfProductSource {b T : ℝ} {N m z : ℕ} :
    m ∈ realSiftedHalfProductSource b N T z ↔
      m ∈ realHalfProductSource b N T ∧
        Nat.Coprime (N - m) (sieveProduct N z)
```

### realSiftedHalfProductSource_card_le_sum_physicalDivisorSum

```lean
theorem realSiftedHalfProductSource_card_le_sum_physicalDivisorSum
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m)
```

### realSiftedHalfProductSource_card_le_same_rho_main_add_errors

```lean
theorem realSiftedHalfProductSource_card_le_same_rho_main_add_errors
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

### realHalfProductSource_primePartner_card_le_realSifted_add_cap

```lean
theorem realHalfProductSource_primePartner_card_le_realSifted_add_cap
    (b : ℝ) (N z : ℕ) (T : ℝ) :
    ((realHalfProductSource b N T).filter
      (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
      (realSiftedHalfProductSource b N T z).card + z
```

### RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff

```lean
theorem RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (hb : b < 1) (hT : 0 ≤ T) :
    (RealB b N : ℝ) ≤
      ((realSiftedHalfProductSource b N T z).card : ℝ) + (z : ℝ) + (T + 1)
```

### RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff

```lean
theorem RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      (∑ m ∈ realHalfProductSource b N T,
        physicalDivisorSum Q rho (N - m)) + (z : ℝ) + (T + 1)
```

### RealB_cast_le_same_rho_main_add_errors

```lean
theorem RealB_cast_le_same_rho_main_add_errors
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

### realHalfProductSource_prime_divisor_rough

```lean
theorem realHalfProductSource_prime_divisor_rough
    {b T : ℝ} {N m ell : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hm : m ∈ realHalfProductSource b N T)
    (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    T ^ (b / (1 + b)) < (ell : ℝ)
```

### realHalfProductSource_coprime_of_dvd_sieveProduct

```lean
theorem realHalfProductSource_coprime_of_dvd_sieveProduct
    {b T : ℝ} {N m z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime m d
```

### realHalfProductCoprimeMass_eq_card_of_gate

```lean
theorem realHalfProductCoprimeMass_eq_card_of_gate
    {b T : ℝ} {N z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b))) (hd : d ∣ sieveProduct N z) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ)
```

### realPhysicalCoprimeCorrection_eq_zero_of_gate

```lean
theorem realPhysicalCoprimeCorrection_eq_zero_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realPhysicalCoprimeCorrection b N T Q rho = 0
```

### RealB_cast_le_same_rho_main_add_distribution_of_gate

```lean
theorem RealB_cast_le_same_rho_main_add_distribution_of_gate
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

### sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass

```lean
theorem sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d
```

### sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors

```lean
theorem sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d
```

### RealB_cast_le_same_rho_outer_main_add_errors

```lean
theorem RealB_cast_le_same_rho_outer_main_add_errors
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

### actualSmallPrimeFinset_eq_sievePrimes_ceil

```lean
theorem actualSmallPrimeFinset_eq_sievePrimes_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z)
```

### actualSmallPrimeProduct_eq_sieveProduct_ceil

```lean
theorem actualSmallPrimeProduct_eq_sieveProduct_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z)
```

### actualSmallRoughIndicator_eq_sieveProduct_natAbs

```lean
theorem actualSmallRoughIndicator_eq_sieveProduct_natAbs
    (N : ℕ) (z : ℝ) (n : ℤ) :
    actualSmallRoughIndicator N z n =
      if Nat.Coprime n.natAbs (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0
```

### actualSmallRoughRho_sieveProduct_majorant

```lean
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

### actualSmallRosserSupport_dvd_sieveProduct_ceil

```lean
theorem actualSmallRosserSupport_dvd_sieveProduct_ceil
    (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### fixedRoughSupport_dvd_sieveProduct_ceil

```lean
theorem fixedRoughSupport_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### actualSmallRoughModuli_dvd_sieveProduct_ceil

```lean
theorem actualSmallRoughModuli_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

### RealB_cast_le_actualSmallRoughRho_main_add_errors

```lean
theorem RealB_cast_le_actualSmallRoughRho_main_add_errors
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

## RealUpperCountingAssembly

Source SHA256: `56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96`

### eventually_RealB_le_currentK_log_of_same_rho_inputs

```lean
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
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
