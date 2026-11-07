# P1 provisional source-extracted theorem types

These signatures are extracted from uncommitted local candidate source, not compiler-confirmed types. See p1-intake.json for exact file hashes and status.

## selectedPrefixLowerRestorationIntegral_eq_integrals

Source: ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean

```lean
theorem selectedPrefixLowerRestorationIntegral_eq_integrals
    (I : Finset (Fin 4)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    selectedPrefixLowerRestorationIntegral I old nu a b m J =
      ∑ j ∈ J, ∫ t in logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old),
        (primeOwnCubeGatedProfile (selectedPrefixCellCap I old nu a b m j : ℝ) t -
          primeOwnCubeGatedProfile (old : ℝ) t) * ∏ i, 1 / t i
```

## tendsto_actualSelectedPrefixLowerOwnCubeSum

Source: ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean

```lean
theorem tendsto_actualSelectedPrefixLowerOwnCubeSum
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixOwnCubeSum true N (cap N) ((N : ℝ) ^ (b : ℝ))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## tendsto_actualSelectedPrefixLowerDensity_ceil_normalized

Source: ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_ceil_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixLowerDensity N (Nat.ceil ((N : ℝ) ^ (b : ℝ)))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## levelCheck_sound

Source: ImbalancedChen/HistoricalPrefixCertificate.lean

```lean
theorem levelCheck_sound (D : HistoricalPrefixCapData) (h : D.levelCheck = true) :
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
      (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
      (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j)
```

## levelCheck_of_selectedBoxCapChecks

Source: ImbalancedChen/HistoricalPrefixCertificate.lean

```lean
theorem levelCheck_of_selectedBoxCapChecks (D : HistoricalPrefixCapData)
    (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
    (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4))
    (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
    (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ)
    (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ)
    (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ)
    (h3 : ∀ j ∈ D.cells3,
      D.cap3 j = selectedBoxCap (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I3 j) D.old (nu3 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h4 : ∀ j ∈ D.cells4,
      D.cap4 j = selectedBoxCap (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I4 j) (D.old4 j) (nu4 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true)
    (h5 : ∀ j ∈ D.cells5,
      D.cap5 j = selectedBoxCap (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) ∧
      selectedBoxCapCheck (I5 j) (D.old5 j) (nu5 j)
        (qLogPrimeMeshLo D.a D.b D.m j) (qLogPrimeMeshHi D.a D.b D.m j) = true) :
    D.levelCheck = true
```

## exponent5_apply_sub

Source: ImbalancedChen/HistoricalPrefixCertificate.lean

```lean
theorem exponent5_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0
```

## upperFifthPolicy_eq_oddFirstExitPolicy

Source: ImbalancedChen/HistoricalPrefixCertificate.lean

```lean
theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre)
```

## upperThirdToFifthSaving_eq

Source: ImbalancedChen/HistoricalPrefixCertificate.lean

```lean
theorem upperThirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z
```
