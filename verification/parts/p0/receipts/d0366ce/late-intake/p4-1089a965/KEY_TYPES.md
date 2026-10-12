# P4 late intake: key complete source theorem signatures

Fixed source: `1089a965e20664e63ffd51e0105c11befa406a1f`; parent: `3d5dd058cf6bef5fe90719ee277580baf8b5bf41`.

**SOURCE_EXTRACTED_NOT_COMPILER_CONFIRMED.** All signatures below preserve the full written source header in its original `ImbalancedChen` namespace and imports. No implicit-argument elaboration or axiom inventory is claimed. The five production files retain all 53 public source headers byte for byte from the parent. Full original inventory is retained in `fixed-source/verification/parts/p4a/round2/SOURCE_TYPES.md` and `.json`.

## `actualSmallRoughRho_eq_firstExitAttachment`

Fixed path: `ImbalancedChen/ActualUpperPolicyDensity.lean`.

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

## `same_rho_normalized_mainTerm`

Fixed path: `ImbalancedChen/ActualUpperDensityAssembly.lean`.

```lean
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

## `exists_actualSmallRoughRho_density_le_of_full_policy_limits`

Fixed path: `ImbalancedChen/ActualUpperDensityAssembly.lean`.

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

## `exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits`

Fixed path: `ImbalancedChen/ActualUpperDensityAssembly.lean`.

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

## `compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget`

Fixed path: `ImbalancedChen/ActualUpperDensityAssembly.lean`.

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

## `actualSmallRoughRho_sieveProduct_majorant`

Fixed path: `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`.

```lean
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

## `RealB_cast_le_actualSmallRoughRho_main_add_errors`

Fixed path: `ImbalancedChen/RealPhysicalUpperWeightBridge.lean`.

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

## `eventually_RealB_le_currentK_log_of_same_rho_inputs`

Fixed path: `ImbalancedChen/RealUpperCountingAssembly.lean`.

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

## Four uncompiled common-carrier candidate signatures

Fixed path: `verification/parts/p4a/round2/COMMON_CARRIER_CANDIDATE.lean.txt`. These four are outside the five production modules, outside their 53-source-theorem inventory, and outside the dedicated P4 audit.

```lean
theorem smallRoughRho_eq_of_rough_subset
    (small Rraw R : Finset ℕ)
    (raw betaMinus betaPlus : ℕ → ℝ)
    (hsub : Rraw ⊆ R)
    (hzero : ∀ d ∈ R, d ∉ Rraw → raw d = 0) :
    smallRoughRho small R raw betaMinus betaPlus =
      smallRoughRho small Rraw raw betaMinus betaPlus
```

```lean
theorem sum_smallRoughRho_mul_eq_of_rough_subset
    (small Rraw R : Finset ℕ)
    (raw betaMinus betaPlus F : ℕ → ℝ)
    (hsub : Rraw ⊆ R)
    (hzero : ∀ d ∈ R, d ∉ Rraw → raw d = 0) :
    (∑ q ∈ smallRoughModuli small R,
      smallRoughRho small R raw betaMinus betaPlus q * F q) =
    ∑ q ∈ smallRoughModuli small Rraw,
      smallRoughRho small Rraw raw betaMinus betaPlus q * F q
```

```lean
theorem actualSmallRoughRho_eq_rough_union
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (extra : Finset ℕ) :
    smallRoughRho (actualSmallRosserSupport N cap w)
      (fixedRoughSupport retainOdd N cap w z ∪ extra)
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) =
    actualSmallRoughRho retainOdd N cap w z L
```

```lean
theorem supportedDivisorSum_eq_of_subset
    (Rraw R : Finset ℕ) (raw : ℕ → ℝ) (n : ℕ)
    (hsub : Rraw ⊆ R)
    (hzero : ∀ d ∈ R, d ∉ Rraw → raw d = 0) :
    supportedDivisorSum R raw n = supportedDivisorSum Rraw raw n
```

## Unchanged final conditional entrance

Fixed path: `ImbalancedChen/CurrentMainTheorem.lean`; byte-identical to the common baseline and d036. This transcription remains source text. The existing earlier compiler confirmation belongs to its own fixed receipt, not to this late P4 evidence.

```lean
theorem current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop
```
