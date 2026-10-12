# 当前源码 theorem/lemma 声明头

源码提取与编译器输出分别标明。

## `ImbalancedChen.ActualSelectedPrefixLowerCellSum` / `ordinaryLowerFourFrontierTuples_cube_filter`

源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFourFrontierTuples_cube_filter
    (N cap : ℕ) (a b old : ℝ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) :
    (firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old))
```

## `ImbalancedChen.ActualSelectedPrefixLowerCellSum` / `ordinaryLowerFourFrontierTuples_cell_filter`

源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFourFrontierTuples_cell_filter
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1)) :
    (firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old))
```

## `ImbalancedChen.ActualSelectedPrefixLowerCellSum` / `ordinaryLowerFourFrontier_cell_weighted_sum`

源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFourFrontier_cell_weighted_sum
    (N cap : ℕ) (a b old : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1))
    (f : (Fin 4 → ℕ) → ℝ) :
    (∑ p ∈ firstExitFrontierTuples 3
      (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a) (fun _ => b),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)
          then f p else 0)
```

## `ImbalancedChen.ActualSelectedPrefixLowerCellSum` / `ordinaryLowerFourFrontier_cell_ownCube_difference`

源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFourFrontier_cell_ownCube_difference
    (N cap : ℕ) (a b old lambda : ℝ) (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ b ≤ (cap : ℝ)) (m : ℕ) (j : Fin 4 → Fin (m + 1)) :
    (∑ p ∈ firstExitFrontierTuples 3
      (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b)),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j then
          actualPrimeTupleOwnCubeMinus N cap lambda p - actualPrimeTupleOwnCubeMinus N cap old p
        else 0)) =
      actualPrimeBoxOwnCubeMinusSum 3 N cap a b lambda
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) -
      actualPrimeBoxOwnCubeMinusSum 3 N cap a b old
        (logPrimeMeshCell a b m j ∩
          primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old))
```

## `ImbalancedChen.ActualSelectedPrefixLowerCellSum` / `actualSelectedPrefixLowerOwnCubeSum_eq_cells`

源码 SHA256：`48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714`；命名空间：`ImbalancedChen`。

```lean
theorem actualSelectedPrefixLowerOwnCubeSum_eq_cells
    (N cap : ℕ) (I : Finset (Fin 4)) (old nu a b : ℚ)
    (hab : a < b) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (b : ℝ) ≤ (cap : ℝ))
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum true N cap ((N : ℝ) ^ (b : ℝ)) I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ J,
        (actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ)
          (selectedPrefixCellCap I old nu a b m j : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)) -
        actualPrimeBoxOwnCubeMinusSum 3 N cap (a : ℝ) (b : ℝ) (old : ℝ)
          (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
            primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old)))
```

## `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` / `selectedPrefixLowerRestorationIntegral_eq_integrals`

源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` / `tendsto_actualSelectedPrefixLowerOwnCubeSum`

源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` / `tendsto_actualSelectedPrefixLowerDensity_restoration`

源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；命名空间：`ImbalancedChen`。

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_restoration
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      (actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J -
        actualSmallRosserMinusDensity N (cap N) ((N : ℝ) ^ (b : ℝ))
          ((N : ℝ) ^ (old : ℝ))) * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` / `tendsto_actualSelectedPrefixLowerDensity_normalized`

源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；命名空间：`ImbalancedChen`。

```lean
theorem tendsto_actualSelectedPrefixLowerDensity_normalized
    (I : Finset (Fin 4)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hbo : 2 * b ≤ old)
    (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1)))
    (hchecks : ∀ j ∈ J, selectedBoxCapCheck I old nu
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J *
      Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 ((2 * Real.exp (-Real.eulerMascheroniConstant) / (b : ℝ)) *
        suzukiContinuousLowerFactor ((old : ℝ) / (b : ℝ)) +
        selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` / `tendsto_actualSelectedPrefixLowerDensity_ceil_normalized`

源码 SHA256：`c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixProject_comp`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixProject_comp {α : Type*} {r d e : ℕ}
    (hrd : r ≤ d) (hde : d ≤ e) (t : Fin e → α) :
    historicalPrefixProject hrd (historicalPrefixProject hde t) =
      historicalPrefixProject (hrd.trans hde) t
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `mem_logPrimeMeshCell_historicalPrefixProject`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem mem_logPrimeMeshCell_historicalPrefixProject {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} {j : Fin d → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j) :
    historicalPrefixProject hrd t ∈
      logPrimeMeshCell a b m (historicalPrefixProject hrd j)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixAncestorCell_unique`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixAncestorCell_unique {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j)
    (hq : historicalPrefixProject hrd t ∈ logPrimeMeshCell a b m q) :
    q = historicalPrefixProject hrd j
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `primeHistoryLogCoordinates_eq_historicalPrefixProject`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
    {r d : ℕ} (hrd : r ≤ d) {history : List ℕ} (hlen : history.length = d) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) =
      historicalPrefixProject hrd (primeHistoryLogCoordinates N d history)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixLookup_on_cell`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixLookup_on_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = cap j
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixLookup_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixLookup_outside {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (ht : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = fallback
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixLookup_on_any_cell`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixLookup_on_any_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1))
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t =
      if j ∈ J then cap j else fallback
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixLookup_ge_fallback`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixLookup_ge_fallback {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (old cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (hlevel : ∀ j ∈ J, old j ≤ cap j)
    (hinherit : ∀ j ∈ J,
      t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j → fallback = old j) :
    fallback ≤ historicalPrefixLookup a b m J cap fallback t
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `historicalPrefixLookup_apply_sub`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen`。

```lean
theorem historicalPrefixLookup_apply_sub {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (f : ℚ → ℝ) :
    f (historicalPrefixLookup a b m J cap fallback t) - f fallback =
      ∑ j ∈ J, if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
        f (cap j) - f fallback else 0
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `levelCheck_sound`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem levelCheck_sound (D : HistoricalPrefixCapData) (h : D.levelCheck = true) :
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
      (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
      (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `levelCheck_of_selectedBoxCapChecks`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

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

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent3_on_cell`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent3_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ) (j : Fin 3 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.cell3 j
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent4_on_cell`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent4_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (j : Fin 4 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.cell4 j
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent5_on_cell`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent5_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.cell5 j
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent3_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent3_outside (D : HistoricalPrefixCapData) (t : Fin 3 → ℝ)
    (ht : ∀ j ∈ D.cells3,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.old
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent4_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent4_outside (D : HistoricalPrefixCapData) (t : Fin 4 → ℝ)
    (ht : ∀ j ∈ D.cells4,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent5_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent5_outside (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ)
    (ht : ∀ j ∈ D.cells5,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent4_apply_sub`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent4_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent4 t) -
        f (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) =
      ∑ j ∈ D.cells4,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap4 j) - f (D.old4 j) else 0
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent5_apply_sub`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent5_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `old_le_exponent3`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem old_le_exponent3 (D : HistoricalPrefixCapData) (hcheck : D.levelCheck = true)
    (t : Fin 3 → ℝ) : D.old ≤ D.exponent3 t
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent3_le_exponent4`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent3_le_exponent4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 4 → ℝ) :
    D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t) ≤ D.exponent4 t
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `exponent4_le_exponent5`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem exponent4_le_exponent5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 5 → ℝ) :
    D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤ D.exponent5 t
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `level3_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem level3_outside (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ D.cells3, primeHistoryLogCoordinates N 3 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N history = N ^ (D.old : ℝ)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `level4_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem level4_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 4)
    (hout : ∀ j ∈ D.cells4, primeHistoryLogCoordinates N 4 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N history = D.level3 N (rosserAncestor 3 history)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `level5_outside`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem level5_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = D.level4 N (rosserAncestor 4 history)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `level3_ancestor_le_level4`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem level3_ancestor_le_level4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 4) :
    D.level3 N (rosserAncestor 3 history) ≤ D.level4 N history
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `level4_ancestor_le_level5`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem level4_ancestor_le_level5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 5) :
    D.level4 N (rosserAncestor 4 history) ≤ D.level5 N history
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `upperThirdPolicy_even`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem upperThirdPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperThirdPolicy N true pre = true
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `upperFourthPolicy_even`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem upperFourthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFourthPolicy N true pre = true
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `upperFifthPolicy_even`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem upperFifthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFifthPolicy N true pre = true
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `upperFifthPolicy_eq_oddFirstExitPolicy`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre)
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `actual_thirdToFifthSaving_eq`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

```lean
theorem actual_thirdToFifthSaving_eq (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (base : Bool → List ℕ → Bool)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base (D.level3 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (fifthCappedUpperPolicy base (D.level3 (N : ℝ)) (D.level5 (N : ℝ)))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving base (D.level3 (N : ℝ))
          (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z
```

## `ImbalancedChen.HistoricalPrefixCertificate` / `upperThirdToFifthSaving_eq`

源码 SHA256：`347e367e743f8224424ab89b554404b41d78a3be716259586a281feb03f88fd1`；命名空间：`ImbalancedChen.HistoricalPrefixCapData`。

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

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `lowerRosserAdmissibleSet_two_iff`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
private theorem lowerRosserAdmissibleSet_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h21 : p2 < p1) :
    LowerAdmissibleSet Q [p2, p1].toFinset ↔
      (p1 : ℝ) * p2 ^ 3 < Q
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `ordinaryRosserPrefixAdmissible_lower_two_iff`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryRosserPrefixAdmissible_lower_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h2 : 0 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible true Q [p2, p1] ↔
      (p1 : ℝ) * p2 ^ 3 < Q
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `ordinaryLowerFour_parent_valid_iff`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFour_parent_valid_iff
    (Q : ℝ) (p : Fin 4 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection (ordinaryParityRosserPolicy true Q) [] true
      (List.ofFn p).dropLast ↔
      (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `mem_ordinaryLowerFourFrontierTuples_iff`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem mem_ordinaryLowerFourFrontierTuples_iff
    (Q : ℝ) (N cap : ℕ) (w z : ℝ) (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap
    (Q : ℝ) (N cap : ℕ) (w z : ℝ) (hzcap : z ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true Q)
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `ordinaryLowerFour_cube_test_iff_log`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFour_cube_test_iff_log {N : ℕ} (hN : 1 < N)
    (old : ℝ) (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) :
    (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < (N : ℝ) ^ old ↔
      actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `mem_ordinaryLowerFourFrontierTuples_iff_log`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem mem_ordinaryLowerFourFrontierTuples_iff_log
    (N cap : ℕ) (old w z : ℝ) (hN : 1 < N)
    (hzcap : z ≤ (cap : ℝ)) (p : Fin 4 → ℕ) :
    p ∈ firstExitFrontierTuples 3 (ordinaryParityRosserPolicy true ((N : ℝ) ^ old))
      (roughPrimeUniverse N cap w z) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          w ≤ (p i : ℝ) ∧ (p i : ℝ) < z) ∧
        actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `ordinaryLowerFourGateForms_ne_zero`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem ordinaryLowerFourGateForms_ne_zero : ∀ j, ordinaryLowerFourGateForms j ≠ 0
```

## `ImbalancedChen.OrdinaryLowerFourFrontier` / `mem_ordinaryLowerFourGateRegion`

源码 SHA256：`97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8`；命名空间：`ImbalancedChen`。

```lean
theorem mem_ordinaryLowerFourGateRegion (old : ℝ) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old) ↔
      StrictAnti t ∧ t 0 + 3 * t 1 < old
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartIntegral_eq_literal`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartIntegral_eq_literal (k : ℝ) :
    chartIntegral k = (6 * |k| * step ^ 3) *
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        u ^ 2 * (1 - v) /
          (chartX u * chartY k u v * oldResidual k u v * newResidual k u v)
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_eq_literal`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (k : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 6 (abs.{0} k))
        (HPow.hPow.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.step 3))
      (∫ (u : ℝ) (v : ℝ) in 0..1,
        HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} u 2) (HSub.hSub.{0, 0, 0} 1 v))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (k : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 6)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
          (@abs.{0} Real Real.lattice Real.instAddGroup k))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (u : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (v : Real) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `step_eq`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem step_eq : step = rho - mu
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.step_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.step
  (HSub.hSub.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
    ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.step
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartX_eq`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartX_eq (u : ℝ) : chartX u = mu + step * u
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (u : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (HMul.hMul.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.step u))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (u : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.step u))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartY_eq`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartY_eq (k u v : ℝ) : chartY k u v = mu + k * step * u * v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (k u v : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} k ImbalancedChen.Certificates.AboveMuSecondCoarse.step) u) v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
          u)
        v))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chart_bounds`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chart_bounds {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    mu ≤ chartX u ∧ chartX u ≤ rho ∧
      (3 / 16 : ℝ) ≤ chartY k u v ∧ chartY k u v ≤ rho ∧
      rho ≤ oldResidual k u v ∧ rho ≤ newResidual k u v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        LE.le.{0} ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u) ∧
          LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
              ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ∧
            LE.le.{0} (3 / 16) (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v) ∧
              LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
                  ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ∧
                LE.le.{0} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v) ∧
                  LE.le.{0} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (And
      (@LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho)
      (And
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (And
          (@LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
            ImbalancedChen.Certificates.AboveMuSecondCoarse.rho)
          (And
            (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
            (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chart_factors_pos`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chart_factors_pos {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < chartX u ∧ 0 < chartY k u v ∧
      0 < oldResidual k u v ∧ 0 < newResidual k u v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_factors_pos`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        LT.lt.{0} 0 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u) ∧
          LT.lt.{0} 0 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v) ∧
            LT.lt.{0} 0 (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v) ∧
              LT.lt.{0} 0 (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartDenominator_pos`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartDenominator_pos {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < chartDenominator k u v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator_pos`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        LT.lt.{0} 0 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `negative_chart_upper_bounds`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem negative_chart_upper_bounds {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartY (-3) u v ≤ mu ∧ oldResidual (-3) u v ≤ 5 / 24 ∧
      newResidual (-3) u v ≤ 5 / 24
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_upper_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {u v : ℝ},
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
      LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY (-3) u v)
          ImbalancedChen.Certificates.AboveMuSecondCoarse.mu ∧
        LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual (-3) u v) (5 / 24) ∧
          LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual (-3) u v) (5 / 24)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
        u v)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
    (And
      (@LE.le.{0} Real Real.instLE
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual
          (@Neg.neg.{0} Real Real.instNeg
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          u v)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 24)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))))
      (@LE.le.{0} Real Real.instLE
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual
          (@Neg.neg.{0} Real Real.instNeg
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          u v)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 24)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `positive_chart_upper_bounds`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem positive_chart_upper_bounds {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    oldResidual 1 u v ≤ 53 / 256 ∧ newResidual 1 u v ≤ 53 / 256
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_upper_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {u v : ℝ},
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
      LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual 1 u v) (53 / 256) ∧
        LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual 1 u v) (53 / 256)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254)))))))))
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254)))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartInterior_mem_physicalDomain`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartInterior_mem_physicalDomain {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    (chartX u, chartY k u v) ∈ physicalDomain
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_mem_physicalDomain`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Ioo.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Ioo.{0} 0 1) v →
        Membership.mem.{0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain
          (Prod.mk.{0, 0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Membership.mem.{0, 0} (Prod.{0, 0} Real Real) (Set.{0} (Prod.{0, 0} Real Real))
    (@Set.instMembership.{0} (Prod.{0, 0} Real Real)) ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain
    (@Prod.mk.{0, 0} Real Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `envelope_of_ge_mu`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
private theorem envelope_of_ge_mu {t : ℝ} (ht : mu ≤ t) :
    endpointEnvelope t = 57 / 64 - 3 * t / 2
```

编译器声明：`_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_ge_mu`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {t : ℝ},
  LE.le.{0} ImbalancedChen.Certificates.AboveMuSecondCoarse.mu t →
    Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
      (HSub.hSub.{0, 0, 0} (57 / 64) (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 t) 2))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {t : Real} (ht : @LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.mu t),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 57)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 57) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 55) (instOfNatNat (nat_lit 55)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 64)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62))))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          t)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `envelope_of_le_mu`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
private theorem envelope_of_le_mu {t : ℝ} (ht : t ≤ mu) :
    endpointEnvelope t = (1 + t) / 2
```

编译器声明：`_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_le_mu`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {t : ℝ},
  LE.le.{0} t ImbalancedChen.Certificates.AboveMuSecondCoarse.mu →
    Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
      (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 t) 2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {t : Real} (ht : @LE.le.{0} Real Real.instLE t ImbalancedChen.Certificates.AboveMuSecondCoarse.mu),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `endpointEnvelope_chartX`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem endpointEnvelope_chartX {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    endpointEnvelope (chartX u) = 153 / 256 - (3 / 2 : ℝ) * step * u
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartX`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {u : ℝ},
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Eq.{1}
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (HSub.hSub.{0, 0, 0} (153 / 256)
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 / 2) ImbalancedChen.Certificates.AboveMuSecondCoarse.step) u))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {u : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 153)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 153) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
        u))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `endpointEnvelope_chartY`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem endpointEnvelope_chartY {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    endpointEnvelope (chartY k u v) =
      153 / 256 - (3 / 2 : ℝ) * step * u * v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartY`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        Eq.{1}
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
          (HSub.hSub.{0, 0, 0} (153 / 256)
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (3 / 2) ImbalancedChen.Certificates.AboveMuSecondCoarse.step) u)
              v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 153)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 153) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
          u)
        v))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartInterior_gates`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartInterior_gates {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    2 * chartX u < endpointEnvelope (chartX u) ∧
      chartX u + 2 * chartY k u v < endpointEnvelope (chartX u) ∧
      2 * chartX u + chartY k u v < endpointEnvelope (chartX u) ∧
      endpointEnvelope (chartX u) < endpointEnvelope (chartY k u v)
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_gates`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Ioo.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Ioo.{0} 0 1) v →
        LT.lt.{0} (HMul.hMul.{0, 0, 0} 2 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)) ∧
          LT.lt.{0}
              (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
                (HMul.hMul.{0, 0, 0} 2 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)) ∧
            LT.lt.{0}
                (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)) ∧
              LT.lt.{0}
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
    (And
      (@LT.lt.{0} Real Real.instLT
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
        (@LT.lt.{0} Real Real.instLT
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `oldResidual_semantics`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem oldResidual_semantics {k u : ℝ} (v : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    oldResidual k u v = endpointEnvelope (chartX u) - chartX u - chartY k u v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual_semantics`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u : ℝ} (v : ℝ),
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v)
      (HSub.hSub.{0, 0, 0}
        (HSub.hSub.{0, 0, 0}
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u : Real} (v : Real)
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `newResidual_semantics`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem newResidual_semantics {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    newResidual k u v =
      endpointEnvelope (chartY k u v) - chartX u - chartY k u v
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual_semantics`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)
          (HSub.hSub.{0, 0, 0}
            (HSub.hSub.{0, 0, 0}
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartKernel_eq_physical_pullback`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartKernel_eq_physical_pullback {k u v : ℝ} (hk : k = -3 ∨ k = 1)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartKernel k u v =
      (4 * (endpointEnvelope (chartY k u v) - endpointEnvelope (chartX u)) /
        (chartX u * chartY k u v *
          (endpointEnvelope (chartX u) - chartX u - chartY k u v) *
          (endpointEnvelope (chartY k u v) - chartX u - chartY k u v))) *
        (|k| * step ^ 2 * u)
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel_eq_physical_pullback`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k u v : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
      Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
        Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
          (HMul.hMul.{0, 0, 0}
            (HDiv.hDiv.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} 4
                (HSub.hSub.{0, 0, 0}
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))))
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                  (HSub.hSub.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0}
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
                (HSub.hSub.{0, 0, 0}
                  (HSub.hSub.{0, 0, 0}
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))))
            (HMul.hMul.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (abs.{0} k)
                (HPow.hPow.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.step 2))
              u))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@abs.{0} Real Real.lattice Real.instAddGroup k)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        u))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `continuousOn_chartKernel`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem continuousOn_chartKernel {k : ℝ} (hk : k = -3 ∨ k = 1) :
    ContinuousOn (fun p : ℝ × ℝ => chartKernel k p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.continuousOn_chartKernel`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    ContinuousOn.{0, 0} (fun p => ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k p.1 p.2)
      (SProd.sprod.{0, 0, 0} (Set.Icc.{0} 0 1) (Set.Icc.{0} 0 1))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
    (@instTopologicalSpaceProd.{0, 0} Real Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (fun (p : Prod.{0, 0} Real Real) =>
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k (@Prod.fst.{0, 0} Real Real p)
        (@Prod.snd.{0, 0} Real Real p))
    (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
      (@Set.instSProd.{0, 0} Real Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `squareIntegral_eq_setIntegral`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
private theorem squareIntegral_eq_setIntegral (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    squareIntegral f = ∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1,
      f p.1 p.2 ∂(volume.prod volume)
```

编译器声明：`_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_eq_setIntegral`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (f : ℝ → ℝ → ℝ),
  ContinuousOn.{0, 0} (fun p => f p.1 p.2) (SProd.sprod.{0, 0, 0} (Set.Icc.{0} 0 1) (Set.Icc.{0} 0 1)) →
    Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
      (∫ (p : Prod.{0, 0} ℝ ℝ) in SProd.sprod.{0, 0, 0} (Set.Ioc.{0} 0 1) (Set.Ioc.{0} 0 1),
        f p.1
          p.2 ∂MeasureTheory.Measure.prod.{0, 0} MeasureTheory.MeasureSpace.volume.{0}
          MeasureTheory.MeasureSpace.volume.{0})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (f : Real → Real → Real)
  (hf :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (@MeasureTheory.integral.{0, 0} (Prod.{0, 0} Real Real) Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@Prod.instMeasurableSpace.{0, 0} Real Real
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
      (@MeasureTheory.Measure.restrict.{0} (Prod.{0, 0} Real Real)
        (@Prod.instMeasurableSpace.{0, 0} Real Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (@MeasureTheory.Measure.prod.{0, 0} Real Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
          (@Set.instSProd.{0, 0} Real Real)
          (@Set.Ioc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Set.Ioc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `squareIntegral_mono`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
private theorem squareIntegral_mono {f g : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hfg : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, f u v ≤ g u v) :
    squareIntegral f ≤ squareIntegral g
```

编译器声明：`_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_mono`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {f g : ℝ → ℝ → ℝ},
  ContinuousOn.{0, 0} (fun p => f p.1 p.2) (SProd.sprod.{0, 0, 0} (Set.Icc.{0} 0 1) (Set.Icc.{0} 0 1)) →
    ContinuousOn.{0, 0} (fun p => g p.1 p.2) (SProd.sprod.{0, 0, 0} (Set.Icc.{0} 0 1) (Set.Icc.{0} 0 1)) →
      (∀ (u : ℝ),
          Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
            ∀ (v : ℝ), Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v → LE.le.{0} (f u v) (g u v)) →
        LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral g)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {f g : Real → Real → Real}
  (hf :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (hg :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => g (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (hfg :
    ∀ (u : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          u →
        ∀ (v : Real),
          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
              (@Set.Icc.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              v →
            @LE.le.{0} Real Real.instLE (f u v) (g u v)),
  @LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral g)
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `squareIntegral_weightedMass`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem squareIntegral_weightedMass (C : ℝ) :
    squareIntegral (fun u v => C * u ^ 2 * (1 - v)) = C / 6
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_weightedMass`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (C : ℝ),
  Eq.{1}
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral fun u v =>
      HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (HPow.hPow.{0, 0, 0} u 2)) (HSub.hSub.{0, 0, 0} 1 v))
    (HDiv.hDiv.{0, 0, 0} C 6)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (C : Real),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral fun (u v : Real) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
      (@OfNat.ofNat.{0} Real (nat_lit 6)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `chartIntegral_lower_of_denominatorCap`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem chartIntegral_lower_of_denominatorCap {k D : ℝ} (hk : k = -3 ∨ k = 1)
    (hD : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      chartDenominator k u v ≤ D) :
    |k| * step ^ 3 / D ≤ chartIntegral k
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_lower_of_denominatorCap`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {k D : ℝ},
  Eq.{1} k (-3) ∨ Eq.{1} k 1 →
    (∀ (u : ℝ),
        Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
          ∀ (v : ℝ),
            Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
              LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v) D) →
      LE.le.{0}
        (HDiv.hDiv.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (abs.{0} k) (HPow.hPow.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.step 3))
          D)
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {k D : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hD :
    ∀ (u : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          u →
        ∀ (v : Real),
          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
              (@Set.Icc.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              v →
            @LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v) D),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@abs.{0} Real Real.lattice Real.instAddGroup k)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      D)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `negative_denominator_le`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem negative_denominator_le {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartDenominator (-3) u v ≤ negativeDenominatorCap
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_denominator_le`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {u v : ℝ},
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
      LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator (-3) u v)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator
      (@Neg.neg.{0} Real Real.instNeg
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
      u v)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `positive_denominator_le`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem positive_denominator_le {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    chartDenominator 1 u v ≤ positiveDenominatorCap
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_denominator_le`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {u v : ℝ},
  Membership.mem.{0, 0} (Set.Icc.{0} 0 1) u →
    Membership.mem.{0, 0} (Set.Icc.{0} 0 1) v →
      LE.le.{0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator 1 u v)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `negative_chart_lower`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem negative_chart_lower : (3 / 95000 : ℝ) ≤ chartIntegral (-3)
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LE.le.{0} (3 / 95000) (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral (-3))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 95000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 95000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 94999) (instOfNatNat (nat_lit 94999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 94998) (instOfNatNat (nat_lit 94998))))))))
  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral
    (@Neg.neg.{0} Real Real.instNeg
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `positive_chart_lower`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem positive_chart_lower : (32 / 3042147 : ℝ) ≤ chartIntegral 1
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LE.le.{0} (32 / 3042147) (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral 1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 3042147)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3042147) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3042146) (instOfNatNat (nat_lit 3042146)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3042145) (instOfNatNat (nat_lit 3042145))))))))
  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
```

## `ImbalancedChen.Certificates.AboveMuSecondCoarse` / `adopted_coarse_lower`

源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`；命名空间：`ImbalancedChen.Certificates.AboveMuSecondCoarse`。

```lean
theorem adopted_coarse_lower :
    (640339 / 15210735000 : ℝ) ≤ totalChartIntegral
```

编译器声明：`ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LE.le.{0} (640339 / 15210735000) ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 640339)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 640339) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 640338) (instOfNatNat (nat_lit 640338)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 640337) (instOfNatNat (nat_lit 640337)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 15210735000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 15210735000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15210734999) (instOfNatNat (nat_lit 15210734999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 15210734998) (instOfNatNat (nat_lit 15210734998))))))))
  ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

## `ImbalancedChen.Certificates.PairedCertificateChecker` / `PairedIntegralCertificate.check_sound`

源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem PairedIntegralCertificate.check_sound (c : PairedIntegralCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ∧
      pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ≤ (c.upper : ℝ)
```

编译器声明：`ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.check Bool.true →
    LE.le.{0} (↑c.lower) (ImbalancedChen.Certificates.pairedLocalIntegral ↑c.K ↑c.a ↑c.tl ↑c.tr ↑c.ul ↑c.ur ↑c.Z) ∧
      LE.le.{0} (ImbalancedChen.Certificates.pairedLocalIntegral ↑c.K ↑c.a ↑c.tl ↑c.tr ↑c.ul ↑c.ur ↑c.Z) ↑c.upper
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate)
  (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check c) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.lower c))
      (ImbalancedChen.Certificates.pairedLocalIntegral
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c))))
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.pairedLocalIntegral
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.upper c)))
```

## `ImbalancedChen.Certificates.PairedCertificateChecker` / `PairedIntegralCertificate.sum_check_sound`

源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem PairedIntegralCertificate.sum_check_sound {ι : Type*}
    (s : Finset ι) (c : ι → PairedIntegralCertificate)
    (hchecks : ∀ i ∈ s, (c i).check = true) :
    ((∑ i ∈ s, (c i).lower : ℚ) : ℝ) ≤
        ∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z ∧
      (∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z) ≤
        ((∑ i ∈ s, (c i).upper : ℚ) : ℝ)
```

编译器声明：`ImbalancedChen.Certificates.PairedIntegralCertificate.sum_check_sound`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (c : ι → ImbalancedChen.Certificates.PairedIntegralCertificate),
  (∀ (i : ι), Membership.mem.{u_1, u_1} s i → Eq.{1} (c i).check Bool.true) →
    LE.le.{0} (↑(∑ i ∈ s, (c i).lower))
        (∑ i ∈ s,
          ImbalancedChen.Certificates.pairedLocalIntegral ↑(c i).K ↑(c i).a ↑(c i).tl ↑(c i).tr ↑(c i).ul ↑(c i).ur
            ↑(c i).Z) ∧
      LE.le.{0}
        (∑ i ∈ s,
          ImbalancedChen.Certificates.pairedLocalIntegral ↑(c i).K ↑(c i).a ↑(c i).tl ↑(c i).tr ↑(c i).ul ↑(c i).ur
            ↑(c i).Z)
        ↑(∑ i ∈ s, (c i).upper)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (c : ι → ImbalancedChen.Certificates.PairedIntegralCertificate)
  (hchecks :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) s i →
        @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check (c i)) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast
        (@Finset.sum.{u_1, 0} ι Rat Rat.addCommMonoid s fun (i : ι) =>
          ImbalancedChen.Certificates.PairedIntegralCertificate.lower (c i)))
      (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid s fun (i : ι) =>
        ImbalancedChen.Certificates.pairedLocalIntegral
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z (c i)))))
    (@LE.le.{0} Real Real.instLE
      (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid s fun (i : ι) =>
        ImbalancedChen.Certificates.pairedLocalIntegral
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z (c i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (@Finset.sum.{u_1, 0} ι Rat Rat.addCommMonoid s fun (i : ι) =>
          ImbalancedChen.Certificates.PairedIntegralCertificate.upper (c i))))
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `hasDerivAt_pairedFibrePrimitive`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
private theorem hasDerivAt_pairedFibrePrimitive {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => -((1 + Real.log x - Real.log a) / x))
      (Real.log (z / a) / z ^ 2) z
```

编译器声明：`_private.ImbalancedChen.Certificates.PairedFibreIntegral.0.ImbalancedChen.Certificates.hasDerivAt_pairedFibrePrimitive`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a z : ℝ},
  LT.lt.{0} 0 a →
    LT.lt.{0} 0 z →
      HasDerivAt.{0, 0}
        (fun x =>
          Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Real.log x)) (Real.log a)) x))
        (HDiv.hDiv.{0, 0, 0} (Real.log (HDiv.hDiv.{0, 0, 0} z a)) (HPow.hPow.{0, 0, 0} z 2)) z
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z),
  @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.instAddCommGroup
    (@Semiring.toModule.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@NontriviallyNormedField.toNormedField.{0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@IsModuleTopology.toContinuousSMul.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real
        (@PseudoMetricSpace.toUniformSpace.{0} Real
          (@SeminormedRing.toPseudoMetricSpace.{0} Real
            (@SeminormedCommRing.toSeminormedRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real
                (@NormedField.toNormedCommRing.{0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
      Real Real.instAdd
      (@SMulZeroClass.toSMul.{0, 0} Real Real
        (@AddZero.toZero.{0} Real
          (@AddZeroClass.toAddZero.{0} Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
          (@AddMonoid.toAddZeroClass.{0} Real
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
          (@DistribMulAction.toDistribSMul.{0, 0} Real Real
            (@Semiring.toMonoid.{0} Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
            (@Module.toDistribMulAction.{0, 0} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
              (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
              (@Semiring.toModule.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))))))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real
            (@SeminormedRing.toPseudoMetricSpace.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
        (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))
          instIsTopologicalRingReal)))
    (fun (x : Real) =>
      @Neg.neg.{0} Real Real.instNeg
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (Real.log x))
            (Real.log a))
          x))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) z
          a))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    z
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `intervalIntegrable_pairedFibreKernel`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem intervalIntegrable_pairedFibreKernel {a Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    IntervalIntegrable (fun z : ℝ => Real.log (z / a) / z ^ 2)
      volume a Z
```

编译器声明：`ImbalancedChen.Certificates.intervalIntegrable_pairedFibreKernel`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a Z : ℝ},
  LT.lt.{0} 0 a →
    LE.le.{0} a Z →
      IntervalIntegrable.{0}
        (fun z => HDiv.hDiv.{0, 0, 0} (Real.log (HDiv.hDiv.{0, 0, 0} z a)) (HPow.hPow.{0, 0, 0} z 2))
        MeasureTheory.MeasureSpace.volume.{0} a Z
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @IntervalIntegrable.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@NormedAddGroup.toENormedAddMonoid.{0} Real
      (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
    (fun (z : Real) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            z a))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) a Z
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `pairedFibreIntegral_eq`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem pairedFibreIntegral_eq {a Z : ℝ} (ha : 0 < a) (hAZ : a ≤ Z) :
    pairedFibreIntegral a Z =
      1 / a - (1 + Real.log (Z / a)) / Z
```

编译器声明：`ImbalancedChen.Certificates.pairedFibreIntegral_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a Z : ℝ},
  LT.lt.{0} 0 a →
    LE.le.{0} a Z →
      Eq.{1} (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
        (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 a)
          (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Real.log (HDiv.hDiv.{0, 0, 0} Z a))) Z))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Z a)))
        Z))
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `pairedFibreKernel_eq`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem pairedFibreKernel_eq (t u z w : ℝ) :
    pairedFibreKernel t u z w = 1 / (t * u * z ^ 2 * w)
```

编译器声明：`ImbalancedChen.Certificates.pairedFibreKernel_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (t u z w : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (HDiv.hDiv.{0, 0, 0} 1
      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (t u z w : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        w))
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `pairedLocalIntegral_eq_literal`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem pairedLocalIntegral_eq_literal (K a tl tr ul ur Z : ℝ) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
        ∫ z in a..Z, ∫ w in a..z, 1 / (t * u * z ^ 2 * w)
```

编译器声明：`ImbalancedChen.Certificates.pairedLocalIntegral_eq_literal`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (K a tl tr ul ur Z : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} K 80)
      (∫ (t : ℝ) in tl..tr,
        ∫ (u : ℝ) in ul..ur,
          ∫ (z : ℝ) in a..Z,
            ∫ (w : ℝ) in a..z,
              HDiv.hDiv.{0, 0, 0} 1
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (K a tl tr ul ur Z : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
        (@OfNat.ofNat.{0} Real (nat_lit 80)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
      (@intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (t : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (u : Real) =>
              @intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (z : Real) =>
                  @intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (w : Real) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          w))
                    a z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            ul ur (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        tl tr (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `pairedFibreIntegral_eq_iterated`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem pairedFibreIntegral_eq_iterated {a Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    (∫ z in a..Z, (1 / z ^ 2) * (∫ w in a..z, 1 / w)) =
      pairedFibreIntegral a Z
```

编译器声明：`ImbalancedChen.Certificates.pairedFibreIntegral_eq_iterated`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a Z : ℝ},
  LT.lt.{0} 0 a →
    LE.le.{0} a Z →
      Eq.{1}
        (∫ (z : ℝ) in a..Z,
          HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} z 2))
            (∫ (w : ℝ) in a..z, HDiv.hDiv.{0, 0, 0} 1 w))
        (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @Eq.{1} Real
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (z : Real) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (w : Real) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) w)
            a z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
      a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
```

## `ImbalancedChen.Certificates.PairedFibreIntegral` / `pairedLocalIntegral_eq`

源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem pairedLocalIntegral_eq (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * Real.log (tr / tl) * Real.log (ur / ul) *
        (1 / a - (1 + Real.log (Z / a)) / Z)
```

编译器声明：`ImbalancedChen.Certificates.pairedLocalIntegral_eq`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (K : ℝ) {a tl tr ul ur Z : ℝ},
  LT.lt.{0} 0 a →
    LE.le.{0} a Z →
      LT.lt.{0} 0 tl →
        LT.lt.{0} 0 tr →
          LT.lt.{0} 0 ul →
            LT.lt.{0} 0 ur →
              Eq.{1} (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
                (HMul.hMul.{0, 0, 0}
                  (HMul.hMul.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} K 80) (Real.log (HDiv.hDiv.{0, 0, 0} tr tl)))
                    (Real.log (HDiv.hDiv.{0, 0, 0} ur ul)))
                  (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 a)
                    (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Real.log (HDiv.hDiv.{0, 0, 0} Z a))) Z)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (K : Real) {a tl tr ul ur Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z)
  (htl : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tl)
  (htr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tr)
  (hul : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ul)
  (hur : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ur),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            K
            (@OfNat.ofNat.{0} Real (nat_lit 80)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) tr tl)))
        (Real.log
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            ur ul)))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (Real.log
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Z a)))
          Z)))
```

## `ImbalancedChen.Certificates.PairedV2` / `first_coordinates`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_coordinates :
    tLower firstTIndex = (937361 / 4096000 : ℚ) ∧
    tUpper firstTIndex = (1875373 / 8192000 : ℚ) ∧
    uLower firstUIndex = (194217 / 1280000 : ℚ) ∧
    uUpper firstUIndex = (388777 / 2560000 : ℚ)
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_coordinates`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (937361 / 4096000) ∧
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
      (1875373 / 8192000) ∧
    Eq.{1} (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (194217 / 1280000) ∧
      Eq.{1} (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (388777 / 2560000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
And
  (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 937361) (@Rat.instOfNat (nat_lit 937361)))
      (@OfNat.ofNat.{0} Rat (nat_lit 4096000) (@Rat.instOfNat (nat_lit 4096000)))))
  (And
    (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000)))))
    (And
      (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 194217) (@Rat.instOfNat (nat_lit 194217)))
          (@OfNat.ofNat.{0} Rat (nat_lit 1280000) (@Rat.instOfNat (nat_lit 1280000)))))
      (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
          (@OfNat.ofNat.{0} Rat (nat_lit 2560000) (@Rat.instOfNat (nat_lit 2560000)))))))
```

## `ImbalancedChen.Certificates.PairedV2` / `first_cutoff_definition`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_cutoff_definition :
    firstZ = min (uLower firstUIndex)
      (3 * (1 - tUpper firstTIndex - uUpper firstUIndex) / 13)
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_cutoff_definition`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstZ
  (Min.min.{0} (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
    (HDiv.hDiv.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} 3
        (HSub.hSub.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} 1
            (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)))
      13))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.firstZ
  (@Min.min.{0} Rat Rat.instInf
    (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)))
      (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))))
```

## `ImbalancedChen.Certificates.PairedV2` / `first_geometry_checked`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_geometry_checked :
    0 < a ∧ a < firstZ ∧ firstZ ≤ uLower firstUIndex ∧
    uLower firstUIndex < uUpper firstUIndex ∧ uUpper firstUIndex < h ∧
    h < tLower firstTIndex ∧ tLower firstTIndex < tUpper firstTIndex ∧
    tUpper firstTIndex < d ∧
    (13 / 3 : ℚ) * firstZ ≤ 1 - tUpper firstTIndex - uUpper firstUIndex ∧
    (57 / 64 : ℚ) - (5 / 2) * tLower firstTIndex - uLower firstUIndex ≤ 2 * a ∧
    firstDiscardedQ80 = 0
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_geometry_checked`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LT.lt.{0} 0 ImbalancedChen.Certificates.PairedV2.a ∧
  LT.lt.{0} ImbalancedChen.Certificates.PairedV2.a ImbalancedChen.Certificates.PairedV2.firstZ ∧
    LE.le.{0} ImbalancedChen.Certificates.PairedV2.firstZ
        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex) ∧
      LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex) ∧
        LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
            ImbalancedChen.Certificates.PairedV2.h ∧
          LT.lt.{0} ImbalancedChen.Certificates.PairedV2.h
              (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex) ∧
            LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
                (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex) ∧
              LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
                  ImbalancedChen.Certificates.PairedV2.d ∧
                LE.le.{0} (HMul.hMul.{0, 0, 0} (13 / 3) ImbalancedChen.Certificates.PairedV2.firstZ)
                    (HSub.hSub.{0, 0, 0}
                      (HSub.hSub.{0, 0, 0} 1
                        (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
                      (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)) ∧
                  LE.le.{0}
                      (HSub.hSub.{0, 0, 0}
                        (HSub.hSub.{0, 0, 0} (57 / 64)
                          (HMul.hMul.{0, 0, 0} (5 / 2)
                            (ImbalancedChen.Certificates.PairedV2.tLower
                              ImbalancedChen.Certificates.PairedV2.firstTIndex)))
                        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex))
                      (HMul.hMul.{0, 0, 0} 2 ImbalancedChen.Certificates.PairedV2.a) ∧
                    Eq.{1} ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80 0
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
And
  (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    ImbalancedChen.Certificates.PairedV2.a)
  (And (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.a ImbalancedChen.Certificates.PairedV2.firstZ)
    (And
      (@LE.le.{0} Rat Rat.instLE ImbalancedChen.Certificates.PairedV2.firstZ
        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex))
      (And
        (@LT.lt.{0} Rat Rat.instLT
          (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex))
        (And
          (@LT.lt.{0} Rat Rat.instLT
            (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
            ImbalancedChen.Certificates.PairedV2.h)
          (And
            (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.h
              (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex))
            (And
              (@LT.lt.{0} Rat Rat.instLT
                (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
                (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
              (And
                (@LT.lt.{0} Rat Rat.instLT
                  (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
                  ImbalancedChen.Certificates.PairedV2.d)
                (And
                  (@LE.le.{0} Rat Rat.instLE
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                        (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))
                        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
                      ImbalancedChen.Certificates.PairedV2.firstZ)
                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                        (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
                      (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)))
                  (And
                    (@LE.le.{0} Rat Rat.instLE
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@OfNat.ofNat.{0} Rat (nat_lit 57) (@Rat.instOfNat (nat_lit 57)))
                            (@OfNat.ofNat.{0} Rat (nat_lit 64) (@Rat.instOfNat (nat_lit 64))))
                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                              (@OfNat.ofNat.{0} Rat (nat_lit 5) (@Rat.instOfNat (nat_lit 5)))
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                            (ImbalancedChen.Certificates.PairedV2.tLower
                              ImbalancedChen.Certificates.PairedV2.firstTIndex)))
                        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex))
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                        ImbalancedChen.Certificates.PairedV2.a))
                    (@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))))
```

## `ImbalancedChen.Certificates.PairedV2` / `first_fibre_argument`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_fibre_argument {t u z w : ℝ} (hs : firstFibreSupport t u z w) :
    (417 / 5000 : ℝ) < w ∧ w < z ∧ z < u ∧ u < 19 / 125 ∧
      (19 / 125 : ℝ) < t ∧ t < 59 / 250 ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_fibre_argument`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {t u z w : ℝ},
  ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w →
    LT.lt.{0} (417 / 5000) w ∧
      LT.lt.{0} w z ∧
        LT.lt.{0} z u ∧
          LT.lt.{0} u (19 / 125) ∧
            LT.lt.{0} (19 / 125) t ∧
              LT.lt.{0} t (59 / 250) ∧
                LE.le.{0} (7 / 3)
                  (HDiv.hDiv.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z) w) z)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  And
    (@LT.lt.{0} Real Real.instLT
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 417)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 5000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
      w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (And
            (@LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 19)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 125)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))
              t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 59)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 250)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                        u)
                      z)
                    w)
                  z)))))))
```

## `ImbalancedChen.Certificates.PairedV2` / `first_fibre_nonempty`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_fibre_nonempty : ∃ t u z w : ℝ, firstFibreSupport t u z w
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_fibre_nonempty`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∃ t u z w, ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Exists.{1} Real fun (t : Real) =>
  @Exists.{1} Real fun (u : Real) =>
    @Exists.{1} Real fun (z : Real) =>
      @Exists.{1} Real fun (w : Real) => ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w
```

## `ImbalancedChen.Certificates.PairedV2` / `first_certificate_checked`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_certificate_checked : firstCertificate.check = true
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_certificate_checked`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstCertificate.check Bool.true
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check ImbalancedChen.Certificates.PairedV2.firstCertificate)
  Bool.true
```

## `ImbalancedChen.Certificates.PairedV2` / `firstIntegral_semantics`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem firstIntegral_semantics :
    firstIntegral = ((8452171 / 1250000 : ℝ) / 80) *
      ∫ t in (937361 / 4096000 : ℝ)..(1875373 / 8192000),
      ∫ u in (194217 / 1280000 : ℝ)..(388777 / 2560000),
      ∫ z in (417 / 5000 : ℝ)..(76088109 / 532480000),
      ∫ w in (417 / 5000 : ℝ)..z, 1 / (t * u * z ^ 2 * w)
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstIntegral
  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (8452171 / 1250000) 80)
    (∫ (t : ℝ) in 937361 / 4096000..1875373 / 8192000,
      ∫ (u : ℝ) in 194217 / 1280000..388777 / 2560000,
        ∫ (z : ℝ) in 417 / 5000..76088109 / 532480000,
          ∫ (w : ℝ) in 417 / 5000..z,
            HDiv.hDiv.{0, 0, 0} 1
              (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.firstIntegral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 8452171)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8452171) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8452170) (instOfNatNat (nat_lit 8452170)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8452169) (instOfNatNat (nat_lit 8452169)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1250000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 1250000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1249999) (instOfNatNat (nat_lit 1249999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1249998) (instOfNatNat (nat_lit 1249998))))))))
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (t : Real) =>
        @intervalIntegral.{0} Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (fun (u : Real) =>
            @intervalIntegral.{0} Real Real.normedAddCommGroup
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
              (fun (z : Real) =>
                @intervalIntegral.{0} Real Real.normedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  (fun (w : Real) =>
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        w))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 417)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 5000)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
                  z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 76088109)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 76088108) (instOfNatNat (nat_lit 76088108)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 76088107) (instOfNatNat (nat_lit 76088107)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 532480000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 532479999) (instOfNatNat (nat_lit 532479999)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 532479998) (instOfNatNat (nat_lit 532479998))))))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 194217)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 194216) (instOfNatNat (nat_lit 194216)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 194215) (instOfNatNat (nat_lit 194215)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 1280000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1279999) (instOfNatNat (nat_lit 1279999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1279998) (instOfNatNat (nat_lit 1279998))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 388777)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 388776) (instOfNatNat (nat_lit 388776)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 388775) (instOfNatNat (nat_lit 388775)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2560000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2559999) (instOfNatNat (nat_lit 2559999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2559998) (instOfNatNat (nat_lit 2559998))))))))
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 937361)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 937360) (instOfNatNat (nat_lit 937360)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 937359) (instOfNatNat (nat_lit 937359)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 4096000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4095999) (instOfNatNat (nat_lit 4095999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4095998) (instOfNatNat (nat_lit 4095998))))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1875373)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1875372) (instOfNatNat (nat_lit 1875372)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1875371) (instOfNatNat (nat_lit 1875371)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 8192000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191999) (instOfNatNat (nat_lit 8191999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8191998) (instOfNatNat (nat_lit 8191998))))))))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## `ImbalancedChen.Certificates.PairedV2` / `firstIntegral_bounds`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem firstIntegral_bounds :
    (31703 / 1000000000000 : ℝ) ≤ firstIntegral ∧
      firstIntegral ≤ (31704 / 1000000000000 : ℝ)
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LE.le.{0} (31703 / 1000000000000) ImbalancedChen.Certificates.PairedV2.firstIntegral ∧
  LE.le.{0} ImbalancedChen.Certificates.PairedV2.firstIntegral (31704 / 1000000000000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 31703)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 31703) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31702) (instOfNatNat (nat_lit 31702)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 31701) (instOfNatNat (nat_lit 31701)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 1000000000000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1000000000000) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat
            (@OfNat.ofNat.{0} Nat (nat_lit 999999999999) (instOfNatNat (nat_lit 999999999999)))
            (@Nat.instNeZeroSucc
              (@OfNat.ofNat.{0} Nat (nat_lit 999999999998) (instOfNatNat (nat_lit 999999999998))))))))
    ImbalancedChen.Certificates.PairedV2.firstIntegral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.firstIntegral
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 31704)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 31704) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31703) (instOfNatNat (nat_lit 31703)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 31702) (instOfNatNat (nat_lit 31702)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 1000000000000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1000000000000) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat
            (@OfNat.ofNat.{0} Nat (nat_lit 999999999999) (instOfNatNat (nat_lit 999999999999)))
            (@Nat.instNeZeroSucc
              (@OfNat.ofNat.{0} Nat (nat_lit 999999999998) (instOfNatNat (nat_lit 999999999998)))))))))
```

## `ImbalancedChen.Certificates.PairedV2` / `firstIntegral_pos`

源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem firstIntegral_pos : 0 < firstIntegral
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.firstIntegral_pos`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LT.lt.{0} 0 ImbalancedChen.Certificates.PairedV2.firstIntegral
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ImbalancedChen.Certificates.PairedV2.firstIntegral
```

## `ImbalancedChen.Certificates.RationalLogCertificate` / `logParameter_bounds`

源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`；命名空间：`ImbalancedChen.Certificates`。

```lean
private theorem logParameter_bounds {q : ℚ} (hq : 1 ≤ q) :
    0 ≤ logParameter q ∧ logParameter q < 1
```

编译器声明：`_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {q : ℚ},
  LE.le.{0} 1 q →
    LE.le.{0} 0 (ImbalancedChen.Certificates.logParameter q) ∧ LT.lt.{0} (ImbalancedChen.Certificates.logParameter q) 1
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {q : Rat} (hq : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) q),
  And
    (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (ImbalancedChen.Certificates.logParameter q))
    (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.logParameter q)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
```

## `ImbalancedChen.Certificates.RationalLogCertificate` / `logParameter_identity`

源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`；命名空间：`ImbalancedChen.Certificates`。

```lean
private theorem logParameter_identity {q : ℚ} (hq : 1 ≤ q) :
    (1 + logParameter q) / (1 - logParameter q) = q
```

编译器声明：`_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {q : ℚ},
  LE.le.{0} 1 q →
    Eq.{1}
      (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (ImbalancedChen.Certificates.logParameter q))
        (HSub.hSub.{0, 0, 0} 1 (ImbalancedChen.Certificates.logParameter q)))
      q
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {q : Rat} (hq : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) q),
  @Eq.{1} Rat
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.logParameter q))
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.logParameter q)))
    q
```

## `ImbalancedChen.Certificates.RationalLogCertificate` / `RationalLogCertificate.check_sound`

源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`；命名空间：`ImbalancedChen.Certificates`。

```lean
theorem RationalLogCertificate.check_sound (c : RationalLogCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
      Real.log (c.argument : ℝ) ≤ (c.upper : ℝ)
```

编译器声明：`ImbalancedChen.Certificates.RationalLogCertificate.check_sound`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  Eq.{1} c.check Bool.true → LE.le.{0} (↑c.lower) (Real.log ↑c.argument) ∧ LE.le.{0} (Real.log ↑c.argument) ↑c.upper
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate)
  (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.RationalLogCertificate.check c) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.lower c))
      (Real.log (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.argument c))))
    (@LE.le.{0} Real Real.instLE
      (Real.log (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.argument c)))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.upper c)))
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3CurrentLowerAPError_le_four_pool`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3CurrentLowerAPError_le_four_pool (N Q : ℕ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerAPError N S3 S4 S5 S6 ≤
      4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|)
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3_currentLowerAPError_log_saving`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3_currentLowerAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerAPError N S3 S4 S5 S6 ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3_quotientRemainder_log_saving_add_centre`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3_quotientRemainder_log_saving_add_centre
    {α : Type*} (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ A : ℝ, ∀ T : Finset α, ∀ b : α → ℕ, ∀ S : α → Finset ℕ,
          ∀ hN : Even N,
          ∀ hbpos : ∀ t ∈ T, 0 < b t,
          ∀ hbN : ∀ t ∈ T, Nat.Coprime (b t) N,
          ∀ hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)),
          Set.InjOn b (T : Set α) → ChenQuotientRows N A Q T b S →
          (∑ t ∈ T.attach, ∑ e ∈ S t.val,
            |(chenQuotientBoundingSieve N (b t.val) A hN (hb t.val t.property)).rem e|) ≤
            (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
              (C * (N : ℝ) / Real.log (N : ℝ) ^ accuracy) +
                chenSelectedCentreCost N T b S
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3CurrentLowerRemainderSum_le_primitive_log_add_cost`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3CurrentLowerRemainderSum_le_primitive_log_add_cost
    (N Q : ℕ) (hN : Even N) (M : ℝ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
      4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k|) +
            part3CurrentLowerCentreCost N S3 S4 S5 S6
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3CurrentLowerCentreCost_le_sqrt_log_cube`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3CurrentLowerCentreCost_le_sqrt_log_cube {N Q : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt (N : ℝ))
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerCentreCost N S3 S4 S5 S6 ≤
      (8 / (Real.log 2) ^ 3) * (N : ℝ) ^ (1 / 2 : ℝ) *
        (Real.log (N : ℝ)) ^ 3
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3_panModulusCutoff_le_sqrt`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
private theorem part3_panModulusCutoff_le_sqrt (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (panModulusCutoff N B : ℝ) ≤ Real.sqrt (N : ℝ)
```

## `ImbalancedChen.Part3CurrentLowerDistribution` / `part3_currentLowerRemainder_negligible`

源码 SHA256：`a78bb4051c70e17d2b954d3c043af40754dfb1b37b0e42c60dd117c75a5c107d`；命名空间：`ImbalancedChen`。

```lean
theorem part3_currentLowerRemainder_negligible :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ hN : Even N,
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
            epsilon * singularNormalization N
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3_prefix_count_le_add_one`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
private theorem part3_prefix_count_le_add_one (U q a b : ℕ) (hq : 0 < q) :
    U.count (fun n => n ≡ a [MOD q]) ≤
      U.count (fun n => n ≡ b [MOD q]) + 1
```

编译器声明：`_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (U q a b : ℕ),
  LT.lt.{0} 0 q →
    LE.le.{0} (Nat.count (fun n => n ≡ a [MOD q]) U) (HAdd.hAdd.{0, 0, 0} (Nat.count (fun n => n ≡ b [MOD q]) U) 1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Nat instLENat
    (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3_Ico_filter_card_sub`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
private theorem part3_Ico_filter_card_sub (L U : ℕ) (hLU : L ≤ U)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Ico L U).filter P).card = U.count P - L.count P
```

编译器声明：`_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U : ℕ),
  LE.le.{0} L U →
    ∀ (P : ℕ → Prop) [inst : DecidablePred.{1} P],
      Eq.{1} (Finset.card.{0} (Finset.filter.{0} P (Finset.Ico.{0} L U)))
        (HSub.hSub.{0, 0, 0} (Nat.count P U) (Nat.count P L))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U : Nat) (hLU : @LE.le.{0} Nat instLENat L U) (P : Nat → Prop) [inst : @DecidablePred.{1} Nat P],
  @Eq.{1} Nat
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat P inst (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Nat.count P inst U) (@Nat.count P inst L))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3IntervalAPCount_le_add_two`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3IntervalAPCount_le_add_two (L U q a b : ℕ) (hq : 0 < q) :
    part3IntervalAPCount L U q a ≤ part3IntervalAPCount L U q b + 2
```

编译器声明：`ImbalancedChen.part3IntervalAPCount_le_add_two`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a b : ℕ),
  LT.lt.{0} 0 q →
    LE.le.{0} (ImbalancedChen.part3IntervalAPCount L U q a)
      (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.part3IntervalAPCount L U q b) 2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Nat instLENat (ImbalancedChen.part3IntervalAPCount L U q a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.part3IntervalAPCount L U q b)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3IntervalAPCount_abs_sub_le_two`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3IntervalAPCount_abs_sub_le_two (L U q a b : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) - part3IntervalAPCount L U q b| ≤ 2
```

编译器声明：`ImbalancedChen.part3IntervalAPCount_abs_sub_le_two`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a b : ℕ),
  LT.lt.{0} 0 q →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0} ↑(ImbalancedChen.part3IntervalAPCount L U q a)
          ↑(ImbalancedChen.part3IntervalAPCount L U q b)))
      2
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q a))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q b))))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3IntervalCoprimeCount_eq_sum`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3IntervalCoprimeCount_eq_sum (L U q : ℕ) (hq : 0 < q) :
    part3IntervalCoprimeCount L U q =
      ∑ a ∈ (range q).filter (fun a => q.Coprime a), part3IntervalAPCount L U q a
```

编译器声明：`ImbalancedChen.part3IntervalCoprimeCount_eq_sum`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q : ℕ),
  LT.lt.{0} 0 q →
    Eq.{1} (ImbalancedChen.part3IntervalCoprimeCount L U q)
      (∑ a ∈ Finset.range q with q.Coprime a, ImbalancedChen.part3IntervalAPCount L U q a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalCoprimeCount L U q)
    (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
      (@Finset.filter.{0} Nat (fun (a : Nat) => Nat.Coprime q a) (Nat.instDecidableCoprime q) (Finset.range q))
      fun (a : Nat) => ImbalancedChen.part3IntervalAPCount L U q a)
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3IntervalAPCount_coprimeMean_error`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3IntervalAPCount_coprimeMean_error (L U q a : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) -
      (part3IntervalCoprimeCount L U q : ℝ) / q.totient| ≤ 2
```

编译器声明：`ImbalancedChen.part3IntervalAPCount_coprimeMean_error`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a : ℕ),
  LT.lt.{0} 0 q →
    LE.le.{0}
      (abs.{0}
        (HSub.hSub.{0, 0, 0} (↑(ImbalancedChen.part3IntervalAPCount L U q a))
          (HDiv.hDiv.{0, 0, 0} ↑(ImbalancedChen.part3IntervalCoprimeCount L U q) ↑q.totient)))
      2
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q a))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalCoprimeCount L U q))
          (@Nat.cast.{0} Real Real.instNatCast (Nat.totient q)))))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotRemainder_eq_zero_of_not_coprime`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotRemainder_eq_zero_of_not_coprime (L U q a m : ℕ)
    (ha : a.Coprime q) (hm : ¬m.Coprime q) :
    part3LongSlotRemainder L U q a m = 0
```

编译器声明：`ImbalancedChen.part3LongSlotRemainder_eq_zero_of_not_coprime`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a m : ℕ), a.Coprime q → ¬m.Coprime q → Eq.{1} (ImbalancedChen.part3LongSlotRemainder L U q a m) 0
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a m : Nat) (ha : Nat.Coprime a q) (hm : Not (Nat.Coprime m q)),
  @Eq.{1} Real (ImbalancedChen.part3LongSlotRemainder L U q a m)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotRemainder_abs_le_two`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotRemainder_abs_le_two (L U q a m : ℕ)
    (hq : 0 < q) (ha : a.Coprime q) :
    |part3LongSlotRemainder L U q a m| ≤ 2
```

编译器声明：`ImbalancedChen.part3LongSlotRemainder_abs_le_two`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a m : ℕ), LT.lt.{0} 0 q → a.Coprime q → LE.le.{0} (abs.{0} (ImbalancedChen.part3LongSlotRemainder L U q a m)) 2
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a m : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha : Nat.Coprime a q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.part3LongSlotRemainder L U q a m))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotSignedError_norm_le`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotSignedError_norm_le (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (∑ m ∈ S, ‖α m‖) * (∑ q ∈ Q, ‖ρ q‖)
```

编译器声明：`ImbalancedChen.part3LongSlotSignedError_norm_le`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (S Q : Finset.{0} ℕ) (α ρ : ℕ → ℂ) (L U a : ℕ),
  (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LT.lt.{0} 0 q) →
    (∀ (q : ℕ), Membership.mem.{0, 0} Q q → a.Coprime q) →
      LE.le.{0} (Norm.norm.{0} (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (∑ m ∈ S, Norm.norm.{0} (α m))) (∑ q ∈ Q, Norm.norm.{0} (ρ q)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
          @Norm.norm.{0} Complex Complex.instNorm (α m)))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (q : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (ρ q)))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotSignedError_norm_le_of_mass`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotSignedError_norm_le_of_mass (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (M D : ℝ) (hq : ∀ q ∈ Q, 0 < q)
    (ha : ∀ q ∈ Q, a.Coprime q)
    (hM : (∑ m ∈ S, ‖α m‖) ≤ M) (hD : (∑ q ∈ Q, ‖ρ q‖) ≤ D) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤ 2 * M * D
```

编译器声明：`ImbalancedChen.part3LongSlotSignedError_norm_le_of_mass`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (S Q : Finset.{0} ℕ) (α ρ : ℕ → ℂ) (L U a : ℕ) (M D : ℝ),
  (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LT.lt.{0} 0 q) →
    (∀ (q : ℕ), Membership.mem.{0, 0} Q q → a.Coprime q) →
      LE.le.{0} (∑ m ∈ S, Norm.norm.{0} (α m)) M →
        LE.le.{0} (∑ q ∈ Q, Norm.norm.{0} (ρ q)) D →
          LE.le.{0} (Norm.norm.{0} (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 M) D)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat) (M D : Real)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q)
  (hM :
    @LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (α m))
      M)
  (hD :
    @LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (q : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (ρ q))
      D),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        M)
      D)
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotSignedError_norm_le_card`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotSignedError_norm_le_card (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q)
    (hα : ∀ m ∈ S, ‖α m‖ ≤ 1) (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (S.card : ℝ) * (Q.card : ℝ)
```

编译器声明：`ImbalancedChen.part3LongSlotSignedError_norm_le_card`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (S Q : Finset.{0} ℕ) (α ρ : ℕ → ℂ) (L U a : ℕ),
  (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LT.lt.{0} 0 q) →
    (∀ (q : ℕ), Membership.mem.{0, 0} Q q → a.Coprime q) →
      (∀ (m : ℕ), Membership.mem.{0, 0} S m → LE.le.{0} (Norm.norm.{0} (α m)) 1) →
        (∀ (q : ℕ), Membership.mem.{0, 0} Q q → LE.le.{0} (Norm.norm.{0} (ρ q)) 1) →
          LE.le.{0} (Norm.norm.{0} (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 ↑(Finset.card.{0} S)) ↑(Finset.card.{0} Q))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q)
  (hα :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (α m))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hρ :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (ρ q))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat S)))
      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q)))
```

## `ImbalancedChen.Part3LongSlotDistribution` / `part3LongSlotSignedError_norm_le_box`

源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`；命名空间：`ImbalancedChen`。

```lean
theorem part3LongSlotSignedError_norm_le_box (M D L U a : ℕ) (α ρ : ℕ → ℂ)
    (hα : ∀ m ∈ Icc 1 M, ‖α m‖ ≤ 1)
    (hρ : ∀ q ∈ (Icc 1 D).filter (fun q => a.Coprime q), ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError (Icc 1 M)
      ((Icc 1 D).filter (fun q => a.Coprime q)) α ρ L U a‖ ≤
      2 * (M : ℝ) * (D : ℝ)
```

编译器声明：`ImbalancedChen.part3LongSlotSignedError_norm_le_box`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (M D L U a : ℕ) (α ρ : ℕ → ℂ),
  (∀ (m : ℕ), Membership.mem.{0, 0} (Finset.Icc.{0} 1 M) m → LE.le.{0} (Norm.norm.{0} (α m)) 1) →
    (∀ (q : ℕ), Membership.mem.{0, 0} ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) q → LE.le.{0} (Norm.norm.{0} (ρ q)) 1) →
      LE.le.{0}
        (Norm.norm.{0}
          (ImbalancedChen.part3LongSlotSignedError (Finset.Icc.{0} 1 M) ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) α ρ L U
            a))
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 ↑M) ↑D)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (M D L U a : Nat) (α ρ : Nat → Complex)
  (hα :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
          m →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (α m))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hρ :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
          q →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (ρ q))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm
      (ImbalancedChen.part3LongSlotSignedError
        (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
        (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
        α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Nat.cast.{0} Real Real.instNatCast M))
      (@Nat.cast.{0} Real Real.instNatCast D))
```

## `ImbalancedChen.Part3LongSlotNormalization` / `part3_eventually_longSlot_logAccuracy`

源码 SHA256：`ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_eventually_longSlot_logAccuracy
    (theta : ℝ) (htheta : theta < 1) (K : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K
```

## `ImbalancedChen.Part3LongSlotNormalization` / `part3_eventually_longSlot_singularNormalization`

源码 SHA256：`ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_eventually_longSlot_singularNormalization
    (theta : ℝ) (htheta : theta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * singularNormalization N
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_chenPrimeAPCount_eq_primesInAP`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_chenPrimeAPCount_eq_primesInAP (Y a d : ℕ) :
    chenPrimeAPCount Y a d = (primesInAP Y d a : ℝ)
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3PrimeAPError_eq_standard`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3PrimeAPError_eq_standard (Y a d : ℕ) :
    part3PrimeAPError Y a d = standardPrimeAPError Y d (a % d)
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3PrimeAPError_target_eq_chenQuotientPrimeAPError`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3PrimeAPError_target_eq_chenQuotientPrimeAPError (N d : ℕ) :
    part3PrimeAPError N N d =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_standardPrimeAPMaxError_le_prefix`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_standardPrimeAPMaxError_le_prefix
    {N Y d : ℕ} (hY : Y ≤ N) :
    standardPrimeAPMaxError Y d ≤ standardPrimeAPPrefixMaxError N d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_abs_primeAPError_le_prefix`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_abs_primeAPError_le_prefix
    {N Y a d : ℕ} (hY : Y ≤ N) (hd : 0 < d) (ha : Nat.Coprime a d) :
    |part3PrimeAPError Y a d| ≤ standardPrimeAPPrefixMaxError N d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_abs_chenQuotientPrimeAPError_le_prefix`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_abs_chenQuotientPrimeAPError_le_prefix
    {N d : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d| ≤
      standardPrimeAPPrefixMaxError N d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_sum_abs_primeAPError_le_prefix`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_sum_abs_primeAPError_le_prefix
    (N D : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (Y : ℕ) (hY : Y ≤ N) (a : ℕ → ℕ)
    (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
      ∑ d ∈ Finset.Icc 1 D, standardPrimeAPPrefixMaxError N d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_abs_sum_mul_primeAPError_le_sum_abs`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_abs_sum_mul_primeAPError_le_sum_abs
    (S : Finset ℕ) (Y : ℕ) (a : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
      ∑ d ∈ S, |part3PrimeAPError Y (a d) d|
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_sum_abs_primeAPError_log_saving`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_sum_abs_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_abs_sum_mul_primeAPError_log_saving`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3PrimeAPIntervalError_eq_sub`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3PrimeAPIntervalError_eq_sub (L U a d : ℕ) :
    part3PrimeAPIntervalError L U a d =
      part3PrimeAPError U a d - part3PrimeAPError L a d
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_abs_sum_mul_primeAPIntervalError_log_saving`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_abs_sum_mul_primeAPIntervalError_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ L U : ℕ, L ≤ U → U ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPIntervalError L U (a d) d| ≤
              2 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A)
```

## `ImbalancedChen.Part3PrimeAPDistribution` / `part3_chenQuotientPrimeAPError_pool_log_saving`

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`；命名空间：`ImbalancedChen`。

```lean
theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `MediumAtom.auxSWError_eq_auxiliarySWError`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem MediumAtom.auxSWError_eq_auxiliarySWError (d : MediumAtom) (k q b : ℕ) :
    d.auxSWError k q b = auxiliarySWError d.alphaCarrier d.alpha k q b
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `norm_sum_ite_and_not_coprime_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
private theorem norm_sum_ite_and_not_coprime_le
    (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ‖∑ n ∈ S, if P n ∧ ¬Nat.Coprime n k then α n else 0‖ ≤
      ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_sub_one_norm_le_bad_mass`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_sub_one_norm_le_bad_mass
    (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) (hq : 0 < q) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖)
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `sum_norm_not_coprime_le_rough`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem sum_norm_not_coprime_le_rough
    (S : Finset ℕ) (α : ℕ → ℂ) (H k : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) ≤
      (k.primeFactors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_sub_one_norm_le_primeFactors`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_sub_one_norm_le_primeFactors
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.primeFactors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_sub_one_norm_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_norm_le_one_add`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_norm_le_one_add
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b‖ ≤ ‖auxiliarySWError S α 1 q b‖ +
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughOneSlot_norm_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughOneSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughOneSlot z n‖ ≤ 1
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughOneSlot_support`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughOneSlot_support (z : ℝ) (n : ℕ) (hn : roughOneSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughMoebiusSlot_norm_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughMoebiusSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughMoebiusSlot z n‖ ≤ 1
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughMoebiusSlot_support`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughMoebiusSlot_support (z : ℝ) (n : ℕ) (hn : roughMoebiusSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughOneSlot_auxiliarySWError_sub_one_norm_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughOneSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughOneSlot z) k q b -
      auxiliarySWError S (roughOneSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `roughMoebiusSlot_auxiliarySWError_sub_one_norm_le`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem roughMoebiusSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughMoebiusSlot z) k q b -
      auxiliarySWError S (roughMoebiusSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_sub_one_norm_le_mellin`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_sub_one_norm_le_mellin
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z t : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) k q b -
      auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `card_filter_modEq_le_prefix`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
private theorem card_filter_modEq_le_prefix
    (S : Finset ℕ) (H q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H) (hq : 0 < q) :
    ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) ≤ (H : ℝ) / q + 2
```

## `ImbalancedChen.Part3RoughAuxiliarySW` / `auxiliarySWError_norm_le_large_modulus`

源码 SHA256：`d1ff2dc2e0ce6f9f5e18eb2b01da4ae10dfb42c23d2d49f1bb241f8c7796a9f8`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem auxiliarySWError_norm_le_large_modulus
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 H) (hH : 3 ≤ H) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1) :
    ‖auxiliarySWError S α k q b‖ ≤ (H : ℝ) / q + 2 +
      (H : ℝ) * MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
        Real.log (H : ℝ) / (min q H : ℕ)
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `tendsto_logLog_four_div_log`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem tendsto_logLog_four_div_log :
    Tendsto (fun x : ℝ => (Real.log (Real.log x)) ^ 4 / Real.log x)
      atTop (𝓝 0)
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `eventually_log_rpow_le_roughCutoff`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem eventually_log_rpow_le_roughCutoff (B : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ B ≤ x ^ (1 / (Real.log (Real.log x)) ^ 3)
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `eventually_roughCutoff_inv_logAccuracy`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem eventually_roughCutoff_inv_logAccuracy
    (A c epsilon : ℝ) (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      c / x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤
        epsilon / (Real.log x) ^ A
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `MediumAtom.alphaCarrier_subset_Ioc`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem MediumAtom.alphaCarrier_subset_Ioc (d : MediumAtom) (hU : 0 < d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U))
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `MediumAtom.auxSWError_sub_one_norm_le`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem MediumAtom.auxSWError_sub_one_norm_le
    (d : MediumAtom) (z : ℝ) (hU : 0 < d.U) (hz : 0 < z)
    (hα : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (hrough : ∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n → z < (p : ℝ))
    (k q b : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
      4 * d.U * (k.divisors.card : ℝ) / z
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `exists_medium_auxSWError_sub_one_logAccuracy`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem exists_medium_auxSWError_sub_one_logAccuracy
    (A epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      0 < d.U →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
        Nat.Prime p → p ∣ n →
          d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) →
      ∀ k q b : ℕ, 1 ≤ k → 1 ≤ q →
        ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
          epsilon * d.U * (k.divisors.card : ℝ) / (Real.log d.scale) ^ A
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `uniformAuxiliarySW_of_rough_one`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem uniformAuxiliarySW_of_rough_one
    {ι : Type*} (F : ι → MediumAtom)
    (hU : ∀ i, 0 < (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `eventually_const_mul_log_rpow_le_rpow`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem eventually_const_mul_log_rpow_le_rpow
    (c A xi : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, c * (Real.log x) ^ A ≤ x ^ xi
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `eventually_auxiliarySW_large_modulus_logAccuracy`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `exists_medium_auxSW_large_modulus_logAccuracy`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem exists_medium_auxSW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      d.scale ^ xi ≤ d.U → 1 ≤ d.V →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      ∀ k q b : ℕ, (Real.log d.scale) ^ (A + 2) ≤ (q : ℝ) →
        ‖d.auxSWError k q b‖ ≤ epsilon * d.U / (Real.log d.scale) ^ A
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `uniformAuxiliarySW_of_rough_small_moduli`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem uniformAuxiliarySW_of_rough_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (xi : ℝ) (hxi : 0 < xi)
    (hU : ∀ i, 1 ≤ (F i).U) (hV : ∀ i, 1 ≤ (F i).V)
    (hUlow : ∀ i, (F i).scale ^ xi ≤ (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `MediumAdmissible.alphaScaleLower`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem MediumAdmissible.alphaScaleLower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma < d.U
```

## `ImbalancedChen.Part3RoughAuxiliarySWNormalization` / `uniformAuxiliarySW_of_mediumAdmissible_small_moduli`

源码 SHA256：`1d1a6e5d23449f3733a7532018ea23ae820bab06a8c45d46476cc9f2a6b7f91c`；命名空间：`ImbalancedChen.Part3`。

```lean
theorem uniformAuxiliarySW_of_mediumAdmissible_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `sourceMassScale_mul_densityScale`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

```lean
theorem sourceMassScale_mul_densityScale (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)) = singularNormalization N
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `densityScale_pos`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

```lean
theorem densityScale_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < singularSeries N / Real.log (N : ℝ)
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `density_le_manuscriptScale_iff_normalized`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

```lean
theorem density_le_manuscriptScale_iff_normalized {N : ℕ}
    (hN : 2 ≤ N) (density coefficient : ℝ) :
    density ≤ coefficient * (singularSeries N / Real.log (N : ℝ)) ↔
      density * Real.log (N : ℝ) / singularSeries N ≤ coefficient
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `same_rho_normalized_mainTerm`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

```lean
theorem same_rho_normalized_mainTerm (N : ℕ) (mass : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (mass * physicalDensitySum Q rho) / singularNormalization N =
      (mass * Real.log (N : ℝ) / (N : ℝ)) *
        (physicalDensitySum Q rho * Real.log (N : ℝ) / singularSeries N)
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `exists_actualSmallRoughRho_density_le_of_full_policy_limits`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

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
        let w
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

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
        let w
```

## `ImbalancedChen.ActualUpperDensityAssembly` / `compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget`

源码 SHA256：`241eaf65d39385e9f556a80184b25b0b2c2f67503922ec03f6a55b15c646ef3d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.ActualUpperPolicyDensity` / `oddFirstExitPolicy_eq_of_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem oddFirstExitPolicy_eq_of_even_retained {α : Type*}
    (retained : Bool → List α → Bool)
    (heven : ∀ pre, retained true pre = true) :
    oddFirstExitPolicy (retained false) = retained
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport (retained false) N cap w z =
      firstExitRetainedModuli retained (roughPrimeUniverse N cap w z)
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retained false) N cap w z d =
      (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ)
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `actualSmallRoughModuli_eq_firstExitAttachment`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallRoughModuli_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    actualSmallRoughModuli (retained false) N cap w z =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `actualSmallRoughRho_eq_firstExitAttachment`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.ActualUpperPolicyDensity` / `firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.ActualUpperPolicyDensity` / `fixedRoughDensity_nonneg`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem fixedRoughDensity_nonneg
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    0 ≤ reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
      (fixedRoughCoefficient retainOdd N cap w z)
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `firstExitDepthSplicePolicy_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem firstExitDepthSplicePolicy_even_retained {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hreplacement : ∀ pre, replacement true pre = true) (pre : List α) :
    firstExitDepthSplicePolicy k parent replacement true pre = true
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `thirdCappedUpperPolicy_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem thirdCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    thirdCappedUpperPolicy base Q3 true pre = true
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `fourthCappedUpperPolicy_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem fourthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fourthCappedUpperPolicy base Q3 Q4 true pre = true
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `fifthCappedUpperPolicy_even_retained`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

```lean
theorem fifthCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    fifthCappedUpperPolicy base Q3 Q5 true pre = true
```

## `ImbalancedChen.ActualUpperPolicyDensity` / `actualSelectedPrefixUpperDensity_eq_fixedRoughDensity`

源码 SHA256：`16d81ee162d9ed2a5efad703c9a900b2c5ada622b2613472f70eaef4cbd02ae6`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realHalfProductSource_filter_dvd_eq_filter_modEq`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realHalfProductSource_filter_dvd_eq_filter_modEq
    (b : ℝ) (N d : ℕ) (T : ℝ) :
    (realHalfProductSource b N T).filter (fun m : ℕ => d ∣ N - m) =
      (realHalfProductSource b N T).filter (fun m : ℕ => Nat.ModEq d m N)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `sum_physicalDivisorSum_realHalfProductSource`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem sum_physicalDivisorSum_realHalfProductSource
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `sum_rho_mul_realHalfProductCongruenceMass_eq`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem sum_rho_mul_realHalfProductCongruenceMass_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) =
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realSiftedHalfProductSource_card_le_sum_physicalDivisorSum`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realSiftedHalfProductSource_card_le_sum_physicalDivisorSum
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realSiftedHalfProductSource_card_le_same_rho_main_add_errors`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realHalfProductSource_primePartner_card_le_realSifted_add_cap`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realHalfProductSource_primePartner_card_le_realSifted_add_cap
    (b : ℝ) (N z : ℕ) (T : ℝ) :
    ((realHalfProductSource b N T).filter
      (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
      (realSiftedHalfProductSource b N T z).card + z
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (hb : b < 1) (hT : 0 ≤ T) :
    (RealB b N : ℝ) ≤
      ((realSiftedHalfProductSource b N T z).card : ℝ) + (z : ℝ) + (T + 1)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_same_rho_main_add_errors`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realHalfProductSource_prime_divisor_rough`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realHalfProductSource_prime_divisor_rough
    {b T : ℝ} {N m ell : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hm : m ∈ realHalfProductSource b N T)
    (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    T ^ (b / (1 + b)) < (ell : ℝ)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realHalfProductSource_coprime_of_dvd_sieveProduct`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realHalfProductSource_coprime_of_dvd_sieveProduct
    {b T : ℝ} {N m z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime m d
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realHalfProductCoprimeMass_eq_card_of_gate`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realHalfProductCoprimeMass_eq_card_of_gate
    {b T : ℝ} {N z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b))) (hd : d ∣ sieveProduct N z) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `realPhysicalCoprimeCorrection_eq_zero_of_gate`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem realPhysicalCoprimeCorrection_eq_zero_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realPhysicalCoprimeCorrection b N T Q rho = 0
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_same_rho_main_add_distribution_of_gate`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_same_rho_outer_main_add_errors`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallPrimeFinset_eq_sievePrimes_ceil`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallPrimeFinset_eq_sievePrimes_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallPrimeProduct_eq_sieveProduct_ceil`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallPrimeProduct_eq_sieveProduct_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallRoughIndicator_eq_sieveProduct_natAbs`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallRoughIndicator_eq_sieveProduct_natAbs
    (N : ℕ) (z : ℝ) (n : ℤ) :
    actualSmallRoughIndicator N z n =
      if Nat.Coprime n.natAbs (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallRoughRho_sieveProduct_majorant`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallRosserSupport_dvd_sieveProduct_ceil`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallRosserSupport_dvd_sieveProduct_ceil
    (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) :
    d ∣ sieveProduct N (Nat.ceil z)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `fixedRoughSupport_dvd_sieveProduct_ceil`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem fixedRoughSupport_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `actualSmallRoughModuli_dvd_sieveProduct_ceil`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

```lean
theorem actualSmallRoughModuli_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z)
```

## `ImbalancedChen.RealPhysicalUpperWeightBridge` / `RealB_cast_le_actualSmallRoughRho_main_add_errors`

源码 SHA256：`f82e567435a61125c6972da1f2c1430ff946bbd44bd9b5538bd9a6003382ea9d`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.RealUpperCountingAssembly` / `eventually_RealB_le_currentK_log_of_same_rho_inputs`

源码 SHA256：`56bab762d3f765f5080a441910a8696e297bcd72801e13f4338b0ed7142a9a96`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.UpperCoefficientPerturbation` / `abs_mul_sub_mul_le_of_opposite_signs`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

```lean
private theorem abs_mul_sub_mul_le_of_opposite_signs
    {c d lo hi M : ℝ} (hc : 0 ≤ c) (hd : d ≤ 0)
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |c * hi - d * lo| ≤ M * |c - d|
```

## `ImbalancedChen.UpperCoefficientPerturbation` / `abs_signAttachedValue_sub_le`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

```lean
theorem abs_signAttachedValue_sub_le
    {c d lo hi M : ℝ} (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signAttachedValue c lo hi - signAttachedValue d lo hi| ≤ M * |c - d|
```

## `ImbalancedChen.UpperCoefficientPerturbation` / `signSensitiveReciprocalTotientDensity_eq_sum_attached`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

```lean
theorem signSensitiveReciprocalTotientDensity_eq_sum_attached
    (rough : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity rough c lo hi =
      ∑ d ∈ rough, signAttachedValue (c d) lo hi / (Nat.totient d : ℝ)
```

## `ImbalancedChen.UpperCoefficientPerturbation` / `abs_signSensitiveReciprocalTotientDensity_sub_le`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

```lean
theorem abs_signSensitiveReciprocalTotientDensity_sub_le
    (rough : Finset ℕ) (compiled raw : ℕ → ℝ) {lo hi M : ℝ}
    (hlo : |lo| ≤ M) (hhi : |hi| ≤ M) :
    |signSensitiveReciprocalTotientDensity rough compiled lo hi -
        signSensitiveReciprocalTotientDensity rough raw lo hi| ≤
      M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|)
```

## `ImbalancedChen.UpperCoefficientPerturbation` / `abs_physicalDensitySum_smallRoughRho_sub_le`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.UpperCoefficientPerturbation` / `supportedDivisorSum_le_of_coefficient_le`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

```lean
theorem supportedDivisorSum_le_of_coefficient_le
    (rough : Finset ℕ) (raw compiled : ℕ → ℝ)
    (hdom : ∀ d ∈ rough, raw d ≤ compiled d) (n : ℕ) :
    supportedDivisorSum rough raw n ≤ supportedDivisorSum rough compiled n
```

## `ImbalancedChen.UpperCoefficientPerturbation` / `actualAttachedRho_majorant_of_rough_domination`

源码 SHA256：`59b45cfb13444beee297beec05b6d2153d7207db4f9bd96a8652260eaa57bcef`；命名空间：`ImbalancedChen`。

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

## `ImbalancedChen.CurrentChenBuchstabRefinement` / `currentChen_log_rational_lower`

源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；命名空间：`ImbalancedChen`。

```lean
private theorem currentChen_log_rational_lower {x : ℝ} (hx : 1 ≤ x) :
    2 * ((x - 1) / (x + 1)) ≤ Real.log x
```

编译器声明：`_private.ImbalancedChen.CurrentChenBuchstabRefinement.0.ImbalancedChen.currentChen_log_rational_lower`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {x : ℝ}, 1 ≤ x → 2 * ((x - 1) / (x + 1)) ≤ Real.log x
```

## `ImbalancedChen.CurrentChenBuchstabRefinement` / `currentChen_buchstab_lower_first_segment`

源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_buchstab_lower_first_segment {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) (hs₃ : s ≤ 3) :
    (11 : ℝ) / 20 ≤ buchstab s
```

编译器声明：`ImbalancedChen.currentChen_buchstab_lower_first_segment`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → s ≤ 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## `ImbalancedChen.CurrentChenBuchstabRefinement` / `currentChen_buchstab_lower_transition`

源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_buchstab_lower_transition {s : ℝ}
    (hs : 3 ≤ s) (hs₁₀ : s ≤ (10 : ℝ) / 3) :
    (11 : ℝ) / 20 ≤ buchstab s
```

编译器声明：`ImbalancedChen.currentChen_buchstab_lower_transition`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 3 ≤ s → s ≤ 10 / 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## `ImbalancedChen.CurrentChenBuchstabRefinement` / `currentChen_buchstab_lower_on_tail`

源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_buchstab_lower_on_tail {a L : ℝ} (ha : 2 ≤ a)
    (hbase : ∀ u ∈ Icc a (a + 1), L ≤ buchstab u) :
    ∀ u : ℝ, a ≤ u → L ≤ buchstab u
```

编译器声明：`ImbalancedChen.currentChen_buchstab_lower_on_tail`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a L : ℝ},
  2 ≤ a →
    (∀ u ∈ Set.Icc a (a + 1), L ≤ LiLiuPrereqBuchstab.buchstab u) →
      ∀ (u : ℝ), a ≤ u → L ≤ LiLiuPrereqBuchstab.buchstab u
```

## `ImbalancedChen.CurrentChenBuchstabRefinement` / `currentChen_buchstab_eleven_twentieths`

源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_buchstab_eleven_twentieths {s : ℝ}
    (hs : (7 : ℝ) / 3 ≤ s) :
    (11 : ℝ) / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

编译器声明：`ImbalancedChen.currentChen_buchstab_eleven_twentieths`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## `ImbalancedChen.CurrentChenLowerScale` / `currentChen_four_currentC`

源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_four_currentC :
    4 * currentC = (49044063 : ℝ) / 6250000
```

编译器声明：`ImbalancedChen.currentChen_four_currentC`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} (HMul.hMul.{0, 0, 0} 4 ImbalancedChen.currentC) (49044063 / 6250000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real (nat_lit 4)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    ImbalancedChen.currentC)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 49044063)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 49044063) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 49044062) (instOfNatNat (nat_lit 49044062)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 49044061) (instOfNatNat (nat_lit 49044061)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 6250000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 6250000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6249999) (instOfNatNat (nat_lit 6249999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6249998) (instOfNatNat (nat_lit 6249998))))))))
```

## `ImbalancedChen.CurrentChenLowerScale` / `currentChen_lower_scale_from_finite_weight_bound`

源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_lower_scale_from_finite_weight_bound
    {N : ℕ} (E : ℕ × ℕ → Prop) {etaMean : ℝ}
    (hN : 1 ≤ (N : ℝ))
    (hA : 1 < (N : ℝ) ^ (417 / 5000 : ℝ))
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E) :
    (currentC - etaMean / 4) * singularNormalization N -
      ((123 : ℝ) / 2 *
        ((N : ℝ) / ((N : ℝ) ^ (417 / 5000 : ℝ) - 1)) + 1) ≤
      (D12 N : ℝ)
```

编译器声明：`ImbalancedChen.currentChen_lower_scale_from_finite_weight_bound`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N : ℕ} (E : Prod.{0, 0} ℕ ℕ → Prop) {etaMean : ℝ},
  LE.le.{0} 1 ↑N →
    LT.lt.{0} 1 (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)) →
      LE.le.{0}
          (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 ImbalancedChen.currentC) etaMean)
            (ImbalancedChen.singularNormalization N))
          (ImbalancedChen.currentChenPairedPrimeSum N E) →
        LE.le.{0}
          (HSub.hSub.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} ImbalancedChen.currentC (HDiv.hDiv.{0, 0, 0} etaMean 4))
              (ImbalancedChen.singularNormalization N))
            (HAdd.hAdd.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} (123 / 2)
                (HDiv.hDiv.{0, 0, 0} (↑N) (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)) 1)))
              1))
          ↑(ImbalancedChen.D12 N)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {etaMean : Real}
  (hN :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@Nat.cast.{0} Real Real.instNatCast N))
  (hA :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 417)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 5000)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          etaMean)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E)),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            etaMean
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
        (ImbalancedChen.singularNormalization N))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 123)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 123) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 121) (instOfNatNat (nat_lit 121)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 417)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 5000)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## `ImbalancedChen.CurrentChenLowerScale` / `currentChen_lower_scale_of_finite_budgets`

源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_lower_scale_of_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon etaMean etaCount : ℝ}
    (hbudget : etaMean + etaCount ≤ 4 * epsilon)
    (hweight : (4 * currentC - etaMean) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      etaCount * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

编译器声明：`ImbalancedChen.currentChen_lower_scale_of_finite_budgets`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N : ℕ} (E : Prod.{0, 0} ℕ ℕ → Prop) {epsilon etaMean etaCount : ℝ},
  LE.le.{0} (HAdd.hAdd.{0, 0, 0} etaMean etaCount) (HMul.hMul.{0, 0, 0} 4 epsilon) →
    LE.le.{0}
        (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 ImbalancedChen.currentC) etaMean)
          (ImbalancedChen.singularNormalization N))
        (ImbalancedChen.currentChenPairedPrimeSum N E) →
      LE.le.{0}
          (HSub.hSub.{0, 0, 0} (ImbalancedChen.currentChenPairedPrimeSum N E)
            (HMul.hMul.{0, 0, 0} etaCount (ImbalancedChen.singularNormalization N)))
          (HMul.hMul.{0, 0, 0} 4 ↑(ImbalancedChen.D12 N)) →
        LE.le.{0}
          (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} ImbalancedChen.currentC epsilon)
            (ImbalancedChen.singularNormalization N))
          ↑(ImbalancedChen.D12 N)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {epsilon etaMean etaCount : Real}
  (hbudget :
    @LE.le.{0} Real Real.instLE (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) etaMean etaCount)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        epsilon))
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          etaMean)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E))
  (hcount :
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.currentChenPairedPrimeSum N E)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) etaCount
          (ImbalancedChen.singularNormalization N)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N)))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC epsilon)
      (ImbalancedChen.singularNormalization N))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## `ImbalancedChen.CurrentChenLowerScale` / `currentChen_lower_scale_of_equal_finite_budgets`

源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_lower_scale_of_equal_finite_budgets
    {N : ℕ} (E : ℕ × ℕ → Prop) {epsilon : ℝ}
    (hweight : (4 * currentC - 2 * epsilon) * singularNormalization N ≤
      currentChenPairedPrimeSum N E)
    (hcount : currentChenPairedPrimeSum N E -
      (2 * epsilon) * singularNormalization N ≤ 4 * (D12 N : ℝ)) :
    (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ)
```

编译器声明：`ImbalancedChen.currentChen_lower_scale_of_equal_finite_budgets`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N : ℕ} (E : Prod.{0, 0} ℕ ℕ → Prop) {epsilon : ℝ},
  LE.le.{0}
      (HMul.hMul.{0, 0, 0}
        (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 ImbalancedChen.currentC) (HMul.hMul.{0, 0, 0} 2 epsilon))
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E) →
    LE.le.{0}
        (HSub.hSub.{0, 0, 0} (ImbalancedChen.currentChenPairedPrimeSum N E)
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 epsilon) (ImbalancedChen.singularNormalization N)))
        (HMul.hMul.{0, 0, 0} 4 ↑(ImbalancedChen.D12 N)) →
      LE.le.{0}
        (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} ImbalancedChen.currentC epsilon)
          (ImbalancedChen.singularNormalization N))
        ↑(ImbalancedChen.D12 N)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {epsilon : Real}
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            epsilon))
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E))
  (hcount :
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.currentChenPairedPrimeSum N E)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            epsilon)
          (ImbalancedChen.singularNormalization N)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N)))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC epsilon)
      (ImbalancedChen.singularNormalization N))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY6Selected_add_compl`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY6Selected_add_compl (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenY6Selected n A H D E + chenY6Selected n A H D (fun t => ¬ E t) =
      chenY6 n A H D
```

编译器声明：`ImbalancedChen.chenY6Selected_add_compl`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (n : ℕ) (A H D : ℝ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1}
    (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.chenY6Selected n A H D E)
      (ImbalancedChen.chenY6Selected n A H D fun t => ¬E t))
    (ImbalancedChen.chenY6 n A H D)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (n : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.chenY6Selected n A H D E)
      (ImbalancedChen.chenY6Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
    (ImbalancedChen.chenY6 n A H D)
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY11Selected_add_compl`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY11Selected_add_compl (n : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenY11Selected n A H D E + chenY11Selected n A H D (fun t => ¬ E t) =
      chenY11Full n A H D
```

编译器声明：`ImbalancedChen.chenY11Selected_add_compl`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (n : ℕ) (A H D : ℝ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1}
    (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.chenY11Selected n A H D E)
      (ImbalancedChen.chenY11Selected n A H D fun t => ¬E t))
    (ImbalancedChen.chenY11Full n A H D)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (n : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.chenY11Selected n A H D E)
      (ImbalancedChen.chenY11Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
    (ImbalancedChen.chenY11Full n A H D)
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenPairedElevenWeight_eq_unselected`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenPairedElevenWeight_eq_unselected (n : ℕ) (N A H D C : ℝ)
    (E : ℕ × ℕ → Prop) :
    chenPairedElevenWeight n N A H D C E =
      3 * (chenY1 n A : ℝ) + (chenY2 n H : ℝ) - (chenY3 n A C : ℝ) -
        (chenY4 n A D : ℝ) + (chenY5 n A H : ℝ) +
        (chenY6Selected n A H D (fun t => ¬ E t) : ℝ) -
        2 * (chenY7 n N D : ℝ) - (chenY8 n N A C : ℝ) -
        (chenY9 n N H D : ℝ) - (chenY10 n A H : ℝ) -
        (chenY11Selected n A H D (fun t => ¬ E t) : ℝ)
```

编译器声明：`ImbalancedChen.chenPairedElevenWeight_eq_unselected`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (n : ℕ) (N A H D C : ℝ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.chenPairedElevenWeight n N A H D C E)
    (HSub.hSub.{0, 0, 0}
      (HSub.hSub.{0, 0, 0}
        (HSub.hSub.{0, 0, 0}
          (HSub.hSub.{0, 0, 0}
            (HSub.hSub.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HSub.hSub.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 ↑(ImbalancedChen.chenY1 n A))
                        ↑(ImbalancedChen.chenY2 n H))
                      ↑(ImbalancedChen.chenY3 n A C))
                    ↑(ImbalancedChen.chenY4 n A D))
                  ↑(ImbalancedChen.chenY5 n A H))
                ↑(ImbalancedChen.chenY6Selected n A H D fun t => ¬E t))
              (HMul.hMul.{0, 0, 0} 2 ↑(ImbalancedChen.chenY7 n N D)))
            ↑(ImbalancedChen.chenY8 n N A C))
          ↑(ImbalancedChen.chenY9 n N H D))
        ↑(ImbalancedChen.chenY10 n A H))
      ↑(ImbalancedChen.chenY11Selected n A H D fun t => ¬E t))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (n : Nat) (N A H D C : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.chenPairedElevenWeight n N A H D C E)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY1 n A)))
                        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY2 n H)))
                      (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY3 n A C)))
                    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY4 n A D)))
                  (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY5 n A H)))
                (@Nat.cast.{0} Real Real.instNatCast
                  (ImbalancedChen.chenY6Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY7 n N D))))
            (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY8 n N A C)))
          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY9 n N H D)))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY10 n A H)))
      (@Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chen_sum_quotient_tuple_card_moving_cutoff`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chen_sum_quotient_tuple_card_moving_cutoff {α : Type*} [DecidableEq α]
    (N : ℕ) (T : Finset α) (b : α → ℕ) (z : α → ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      ((T.filter (fun t => ChenQuotient (b t) (z t) (N - P))).card : ℝ)) =
      ∑ t ∈ T, ((chenSiftedQuotientPrimeSource N (b t) (z t)).card : ℝ)
```

编译器声明：`ImbalancedChen.chen_sum_quotient_tuple_card_moving_cutoff`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (N : ℕ) (T : Finset.{u_1} α) (b : α → ℕ) (z : α → ℝ),
  Eq.{1}
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(Finset.card.{u_1} ({t ∈ T | ImbalancedChen.ChenQuotient (b t) (z t) (HSub.hSub.{0, 0, 0} N P)})))
    (∑ t ∈ T, ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (b t) (z t))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (N : Nat) (T : Finset.{u_1} α) (b : α → Nat) (z : α → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{u_1} α
          (@Finset.filter.{u_1} α
            (fun (t : α) =>
              ImbalancedChen.ChenQuotient (b t) (z t)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
            (fun (a : α) =>
              Classical.propDecidable
                (ImbalancedChen.ChenQuotient (b a) (z a)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
            T)))
    (@Finset.sum.{u_1, 0} α Real Real.instAddCommMonoid T fun (t : α) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat (ImbalancedChen.chenSiftedQuotientPrimeSource N (b t) (z t))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chen_prime_dvd_receiver_mem_additiveCarrier`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chen_prime_dvd_receiver_mem_additiveCarrier {N P p : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (hp : Nat.Prime p)
    (hd : p ∣ N - P) : p ∈ chenAdditivePrimeCarrier N
```

编译器声明：`ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P p : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    Nat.Prime p →
      Dvd.dvd.{0} p (HSub.hSub.{0, 0, 0} N P) → Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) p
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P p : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (hp : Nat.Prime p)
  (hd : @Dvd.dvd.{0} Nat Nat.instDvd p (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
    (ImbalancedChen.chenAdditivePrimeCarrier N) p
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY7Tuples_eq_selector_filter`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY7Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (D : ℝ) :
    chenY7Tuples (N - P) (N : ℝ) D =
      (chenY7PrimeSelector N D).filter
        (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P))
```

编译器声明：`ImbalancedChen.chenY7Tuples_eq_selector_filter`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    ∀ (D : ℝ),
      Eq.{1} (ImbalancedChen.chenY7Tuples (HSub.hSub.{0, 0, 0} N P) (↑N) D)
        ({t ∈ ImbalancedChen.chenY7PrimeSelector N D |
          ImbalancedChen.ChenQuotient (HMul.hMul.{0, 0, 0} t.1 t.2) (↑t.2) (HSub.hSub.{0, 0, 0} N P)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY7Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY7PrimeSelector N D))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY8Tuples_eq_selector_filter`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY8Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A C : ℝ) :
    chenY8Tuples (N - P) (N : ℝ) A C =
      (chenY8PrimeSelector N A C).filter
        (fun t => ChenQuotient (t.1 * t.2) (t.2 : ℝ) (N - P))
```

编译器声明：`ImbalancedChen.chenY8Tuples_eq_selector_filter`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    ∀ (A C : ℝ),
      Eq.{1} (ImbalancedChen.chenY8Tuples (HSub.hSub.{0, 0, 0} N P) (↑N) A C)
        ({t ∈ ImbalancedChen.chenY8PrimeSelector N A C |
          ImbalancedChen.ChenQuotient (HMul.hMul.{0, 0, 0} t.1 t.2) (↑t.2) (HSub.hSub.{0, 0, 0} N P)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A C : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY8Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) A C)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY8PrimeSelector N A C))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY9Tuples_eq_selector_filter`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY9Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (H D : ℝ) :
    chenY9Tuples (N - P) (N : ℝ) H D =
      (chenY9PrimeSelector N H D).filter
        (fun t => ChenQuotient (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ)))) (N - P))
```

编译器声明：`ImbalancedChen.chenY9Tuples_eq_selector_filter`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    ∀ (H D : ℝ),
      Eq.{1} (ImbalancedChen.chenY9Tuples (HSub.hSub.{0, 0, 0} N P) (↑N) H D)
        ({t ∈ ImbalancedChen.chenY9PrimeSelector N H D |
          ImbalancedChen.ChenQuotient (HMul.hMul.{0, 0, 0} t.1 t.2)
            (√(HDiv.hDiv.{0, 0, 0} (↑N) (HMul.hMul.{0, 0, 0} ↑t.1 ↑t.2))) (HSub.hSub.{0, 0, 0} N P)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY9Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) H D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (Real.sqrt
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY9PrimeSelector N H D))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY10Tuples_eq_selector_filter`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY10Tuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H : ℝ) :
    chenY10Tuples (N - P) A H =
      (chenY10PrimeSelector N A H).filter
        (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ) (N - P))
```

编译器声明：`ImbalancedChen.chenY10Tuples_eq_selector_filter`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    ∀ (A H : ℝ),
      Eq.{1} (ImbalancedChen.chenY10Tuples (HSub.hSub.{0, 0, 0} N P) A H)
        ({t ∈ ImbalancedChen.chenY10PrimeSelector N A H |
          ImbalancedChen.ChenQuotient
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) (↑t.1.2)
            (HSub.hSub.{0, 0, 0} N P)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A H : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY10Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY10PrimeSelector N A H))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `chenY11FullTuples_eq_selector_filter`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem chenY11FullTuples_eq_selector_filter {N P : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N) (A H D : ℝ) :
    chenY11FullTuples (N - P) A H D =
      (chenY11FullPrimeSelector N A H D).filter
        (fun t => ChenQuotient (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ) (N - P))
```

编译器声明：`ImbalancedChen.chenY11FullTuples_eq_selector_filter`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ},
  Membership.mem.{0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) P →
    ∀ (A H D : ℝ),
      Eq.{1} (ImbalancedChen.chenY11FullTuples (HSub.hSub.{0, 0, 0} N P) A H D)
        ({t ∈ ImbalancedChen.chenY11FullPrimeSelector N A H D |
          ImbalancedChen.ChenQuotient
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) (↑t.1.2)
            (HSub.hSub.{0, 0, 0} N P)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY11FullTuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY11FullPrimeSelector N A H D))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY7_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY7_eq_siftedQuotientPrimeSource (N : ℕ) (D : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY7 (N - P) (N : ℝ) D : ℝ)) =
      ∑ t ∈ chenY7PrimeSelector N D,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY7_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (D : ℝ),
  Eq.{1} (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N, ↑(ImbalancedChen.chenY7 (HSub.hSub.{0, 0, 0} N P) (↑N) D))
    (∑ t ∈ ImbalancedChen.chenY7PrimeSelector N D,
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2) ↑t.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (D : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY7 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) D))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY7PrimeSelector N D)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY8_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY8_eq_siftedQuotientPrimeSource (N : ℕ) (A C : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY8 (N - P) (N : ℝ) A C : ℝ)) =
      ∑ t ∈ chenY8PrimeSelector N A C,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY8_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A C : ℝ),
  Eq.{1} (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N, ↑(ImbalancedChen.chenY8 (HSub.hSub.{0, 0, 0} N P) (↑N) A C))
    (∑ t ∈ ImbalancedChen.chenY8PrimeSelector N A C,
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2) ↑t.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A C : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY8 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) A C))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY8PrimeSelector N A C)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY9_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY9_eq_siftedQuotientPrimeSource (N : ℕ) (H D : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY9 (N - P) (N : ℝ) H D : ℝ)) =
      ∑ t ∈ chenY9PrimeSelector N H D,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY9_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (H D : ℝ),
  Eq.{1} (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N, ↑(ImbalancedChen.chenY9 (HSub.hSub.{0, 0, 0} N P) (↑N) H D))
    (∑ t ∈ ImbalancedChen.chenY9PrimeSelector N H D,
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2)
            √(HDiv.hDiv.{0, 0, 0} (↑N) (HMul.hMul.{0, 0, 0} ↑t.1 ↑t.2)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (H D : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY9 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) H D))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY9PrimeSelector N H D)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY10_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY10_eq_siftedQuotientPrimeSource (N : ℕ) (A H : ℝ) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY10 (N - P) A H : ℝ)) =
      ∑ t ∈ chenY10PrimeSelector N A H,
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY10_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A H : ℝ),
  Eq.{1} (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N, ↑(ImbalancedChen.chenY10 (HSub.hSub.{0, 0, 0} N P) A H))
    (∑ t ∈ ImbalancedChen.chenY10PrimeSelector N A H,
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) ↑t.1.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A H : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY10 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H))
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY10PrimeSelector N A H) fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY11Selected_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY11Selected_eq_siftedQuotientPrimeSource (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    (∑ P ∈ chenAdditivePrimeCarrier N,
      (chenY11Selected (N - P) A H D E : ℝ)) =
      ∑ t ∈ (chenY11FullPrimeSelector N A H D).filter (fun t => E t.2),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY11Selected_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A H D : ℝ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1}
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY11Selected (HSub.hSub.{0, 0, 0} N P) A H D E))
    (∑ t ∈ ImbalancedChen.chenY11FullPrimeSelector N A H D with E t.2,
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) ↑t.1.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D E))
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
        (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          Classical.propDecidable (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
        (ImbalancedChen.chenY11FullPrimeSelector N A H D))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon1_eq_actual_siftedSum`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon1_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    currentChenUpsilon1 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (417 / 5000 : ℝ)) hN).siftedSum
```

编译器声明：`ImbalancedChen.currentChenUpsilon1_eq_actual_siftedSum`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (hN : Even.{0} N), Eq.{1} (ImbalancedChen.currentChenUpsilon1 N) BoundingSieve.siftedSum
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@BoundingSieve.siftedSum
      (ImbalancedChen.chenInitialBoundingSieve N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        hN))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon2_eq_actual_siftedSum`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon2_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    currentChenUpsilon2 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (19 / 125 : ℝ)) hN).siftedSum
```

编译器声明：`ImbalancedChen.currentChenUpsilon2_eq_actual_siftedSum`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (hN : Even.{0} N), Eq.{1} (ImbalancedChen.currentChenUpsilon2 N) BoundingSieve.siftedSum
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@BoundingSieve.siftedSum
      (ImbalancedChen.chenInitialBoundingSieve N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
        hN))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon1_eq_actual_sifted_card`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon1_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    currentChenUpsilon1 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon1_eq_actual_sifted_card`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Even.{0} N →
    Eq.{1} (ImbalancedChen.currentChenUpsilon1 N)
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedPrimeSource N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} Nat
        (ImbalancedChen.chenSiftedPrimeSource N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon2_eq_actual_sifted_card`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon2_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    currentChenUpsilon2 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (19 / 125 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon2_eq_actual_sifted_card`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Even.{0} N →
    Eq.{1} (ImbalancedChen.currentChenUpsilon2 N)
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedPrimeSource N (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} Nat
        (ImbalancedChen.chenSiftedPrimeSource N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon3_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon3_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon3 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon3_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon3 N)
    (∑
      p ∈
        ImbalancedChen.chenSinglePrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (1 / 3)),
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N p (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon3 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (ImbalancedChen.chenSinglePrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
      fun (p : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N p
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon4_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon4_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon4 N =
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon4_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon4 N)
    (∑
      p ∈
        ImbalancedChen.chenSinglePrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)),
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N p (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon4 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (ImbalancedChen.chenSinglePrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (p : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N p
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon5_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon5_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon5 N =
      ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon5_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon5 N)
    (∑
      t ∈
        ImbalancedChen.chenY5PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)),
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2)
            (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon5 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY5PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `sum_chenY6Selected_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem sum_chenY6Selected_eq_siftedQuotientPrimeSource (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY6Selected (N - P) A H D E : ℝ)) =
      ∑ t ∈ (chenY6PrimeSelector N A H D).filter E,
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) A).card : ℝ)
```

编译器声明：`ImbalancedChen.sum_chenY6Selected_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A H D : ℝ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1}
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY6Selected (HSub.hSub.{0, 0, 0} N P) A H D E))
    (∑ t ∈ ImbalancedChen.chenY6PrimeSelector N A H D with E t,
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2) A)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY6Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D E))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} Nat Nat) E (fun (a : Prod.{0, 0} Nat Nat) => Classical.propDecidable (E a))
        (ImbalancedChen.chenY6PrimeSelector N A H D))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            A)))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon6_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon6_eq_siftedQuotientPrimeSource (N : ℕ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon6 N E =
      ∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
          (fun t => ¬ E t),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          ((N : ℝ) ^ (417 / 5000 : ℝ))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon6_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenUpsilon6 N E)
    (∑
      t ∈
        ImbalancedChen.chenY6PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)) (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)) with
      ¬E t,
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2)
            (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon6 N E)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} Nat Nat) (fun (t : Prod.{0, 0} Nat Nat) => Not (E t))
        (fun (a : Prod.{0, 0} Nat Nat) => @instDecidableNot (E a) (Classical.propDecidable (E a)))
        (ImbalancedChen.chenY6PrimeSelector N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon7_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon7_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon7 N =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon7_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon7 N)
    (∑ t ∈ ImbalancedChen.chenY7PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)),
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2) ↑t.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon7 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY7PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon8_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon8_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon8 N =
      ∑ t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (t.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon8_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon8 N)
    (∑
      t ∈
        ImbalancedChen.chenY8PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000)) (HPow.hPow.{0, 0, 0} (↑N) (1 / 3)),
      ↑(Finset.card.{0} (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2) ↑t.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon8 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY8PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon9_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon9_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon9 N =
      ∑ t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2)
          (Real.sqrt ((N : ℝ) / ((t.1 : ℝ) * (t.2 : ℝ))))).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon9_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon9 N)
    (∑
      t ∈
        ImbalancedChen.chenY9PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))
          (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)),
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N (HMul.hMul.{0, 0, 0} t.1 t.2)
            √(HDiv.hDiv.{0, 0, 0} (↑N) (HMul.hMul.{0, 0, 0} ↑t.1 ↑t.2)))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon9 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY9PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon10_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon10_eq_siftedQuotientPrimeSource (N : ℕ) :
    currentChenUpsilon10 N =
      ∑ t ∈ chenY10PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon10_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon10 N)
    (∑
      t ∈
        ImbalancedChen.chenY10PrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)),
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) ↑t.1.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon10 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY10PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenUpsilon11_eq_siftedQuotientPrimeSource`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenUpsilon11_eq_siftedQuotientPrimeSource (N : ℕ)
    (E : ℕ × ℕ → Prop) :
    currentChenUpsilon11 N E =
      ∑ t ∈ (chenY11FullPrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ))).filter
          (fun t => ¬ E t.2),
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ)
```

编译器声明：`ImbalancedChen.currentChenUpsilon11_eq_siftedQuotientPrimeSource`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenUpsilon11 N E)
    (∑
      t ∈
        ImbalancedChen.chenY11FullPrimeSelector N (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)) (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)) with
      ¬E t.2,
      ↑(Finset.card.{0}
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t.1.1 t.1.2) t.2.1) t.2.2) ↑t.1.2)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon11 N E)
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          Not (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
        (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          @instDecidableNot (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
            (Classical.propDecidable (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
        (ImbalancedChen.chenY11FullPrimeSelector N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenPairedPrimeSum_eq_upsilon`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenPairedPrimeSum_eq_upsilon (N : ℕ) (E : ℕ × ℕ → Prop) :
    currentChenPairedPrimeSum N E =
      3 * currentChenUpsilon1 N + currentChenUpsilon2 N - currentChenUpsilon3 N -
        currentChenUpsilon4 N + currentChenUpsilon5 N + currentChenUpsilon6 N E -
        2 * currentChenUpsilon7 N - currentChenUpsilon8 N - currentChenUpsilon9 N -
        currentChenUpsilon10 N - currentChenUpsilon11 N E
```

编译器声明：`ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenPairedPrimeSum N E)
    (HSub.hSub.{0, 0, 0}
      (HSub.hSub.{0, 0, 0}
        (HSub.hSub.{0, 0, 0}
          (HSub.hSub.{0, 0, 0}
            (HSub.hSub.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HSub.hSub.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 (ImbalancedChen.currentChenUpsilon1 N))
                        (ImbalancedChen.currentChenUpsilon2 N))
                      (ImbalancedChen.currentChenUpsilon3 N))
                    (ImbalancedChen.currentChenUpsilon4 N))
                  (ImbalancedChen.currentChenUpsilon5 N))
                (ImbalancedChen.currentChenUpsilon6 N E))
              (HMul.hMul.{0, 0, 0} 2 (ImbalancedChen.currentChenUpsilon7 N)))
            (ImbalancedChen.currentChenUpsilon8 N))
          (ImbalancedChen.currentChenUpsilon9 N))
        (ImbalancedChen.currentChenUpsilon10 N))
      (ImbalancedChen.currentChenUpsilon11 N E))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenPairedPrimeSum N E)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (ImbalancedChen.currentChenUpsilon1 N))
                        (ImbalancedChen.currentChenUpsilon2 N))
                      (ImbalancedChen.currentChenUpsilon3 N))
                    (ImbalancedChen.currentChenUpsilon4 N))
                  (ImbalancedChen.currentChenUpsilon5 N))
                (ImbalancedChen.currentChenUpsilon6 N E))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (ImbalancedChen.currentChenUpsilon7 N)))
            (ImbalancedChen.currentChenUpsilon8 N))
          (ImbalancedChen.currentChenUpsilon9 N))
        (ImbalancedChen.currentChenUpsilon10 N))
      (ImbalancedChen.currentChenUpsilon11 N E))
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenPairedPrimeSum_ge_of_term_bounds`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenPairedPrimeSum_ge_of_term_bounds (N : ℕ) (E : ℕ × ℕ → Prop)
    (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀ u₁₁ : ℝ)
    (h₁ : l₁ ≤ currentChenUpsilon1 N)
    (h₂ : l₂ ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ u₃)
    (h₄ : currentChenUpsilon4 N ≤ u₄)
    (h₅ : l₅ ≤ currentChenUpsilon5 N)
    (h₆ : l₆ ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ u₇)
    (h₈ : currentChenUpsilon8 N ≤ u₈)
    (h₉ : currentChenUpsilon9 N ≤ u₉)
    (h₁₀ : currentChenUpsilon10 N ≤ u₁₀)
    (h₁₁ : currentChenUpsilon11 N E ≤ u₁₁) :
    3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀ - u₁₁ ≤
      currentChenPairedPrimeSum N E
```

编译器声明：`ImbalancedChen.currentChenPairedPrimeSum_ge_of_term_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀ u₁₁ : ℝ),
  LE.le.{0} l₁ (ImbalancedChen.currentChenUpsilon1 N) →
    LE.le.{0} l₂ (ImbalancedChen.currentChenUpsilon2 N) →
      LE.le.{0} (ImbalancedChen.currentChenUpsilon3 N) u₃ →
        LE.le.{0} (ImbalancedChen.currentChenUpsilon4 N) u₄ →
          LE.le.{0} l₅ (ImbalancedChen.currentChenUpsilon5 N) →
            LE.le.{0} l₆ (ImbalancedChen.currentChenUpsilon6 N E) →
              LE.le.{0} (ImbalancedChen.currentChenUpsilon7 N) u₇ →
                LE.le.{0} (ImbalancedChen.currentChenUpsilon8 N) u₈ →
                  LE.le.{0} (ImbalancedChen.currentChenUpsilon9 N) u₉ →
                    LE.le.{0} (ImbalancedChen.currentChenUpsilon10 N) u₁₀ →
                      LE.le.{0} (ImbalancedChen.currentChenUpsilon11 N E) u₁₁ →
                        LE.le.{0}
                          (HSub.hSub.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0}
                                (HSub.hSub.{0, 0, 0}
                                  (HSub.hSub.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HSub.hSub.{0, 0, 0}
                                          (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 l₁) l₂) u₃)
                                          u₄)
                                        l₅)
                                      l₆)
                                    (HMul.hMul.{0, 0, 0} 2 u₇))
                                  u₈)
                                u₉)
                              u₁₀)
                            u₁₁)
                          (ImbalancedChen.currentChenPairedPrimeSum N E)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀ u₁₁ : Real)
  (h₁ : @LE.le.{0} Real Real.instLE l₁ (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ : @LE.le.{0} Real Real.instLE l₂ (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N) u₃)
  (h₄ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N) u₄)
  (h₅ : @LE.le.{0} Real Real.instLE l₅ (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ : @LE.le.{0} Real Real.instLE l₆ (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N) u₇)
  (h₈ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N) u₈)
  (h₉ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N) u₉)
  (h₁₀ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon10 N) u₁₀)
  (h₁₁ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon11 N E) u₁₁),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          l₁)
                        l₂)
                      u₃)
                    u₄)
                  l₅)
                l₆)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                u₇))
            u₈)
          u₉)
        u₁₀)
      u₁₁)
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenPairedPrimeSum_ge_of_normalized_term_bounds`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenPairedPrimeSum_ge_of_normalized_term_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ delta : ℝ)
    (h₁ : (b₁ - delta) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : (b₂ - delta) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ (b₃ + delta) * singularNormalization N)
    (h₄ : currentChenUpsilon4 N ≤ (b₄ + delta) * singularNormalization N)
    (h₅ : (b₅ - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : (b₆ - delta) * singularNormalization N ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ (b₇ + delta) * singularNormalization N)
    (h₈ : currentChenUpsilon8 N ≤ (b₈ + delta) * singularNormalization N)
    (h₉ : currentChenUpsilon9 N ≤ (b₉ + delta) * singularNormalization N)
    (h₁₀ : currentChenUpsilon10 N ≤ (b₁₀ + delta) * singularNormalization N)
    (h₁₁ : currentChenUpsilon11 N E ≤ (b₁₁ + delta) * singularNormalization N) :
    (3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀ - b₁₁ -
      14 * delta) * singularNormalization N ≤ currentChenPairedPrimeSum N E
```

编译器声明：`ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_term_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ delta : ℝ),
  LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₁ delta) (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N) →
    LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₂ delta) (ImbalancedChen.singularNormalization N))
        (ImbalancedChen.currentChenUpsilon2 N) →
      LE.le.{0} (ImbalancedChen.currentChenUpsilon3 N)
          (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₃ delta) (ImbalancedChen.singularNormalization N)) →
        LE.le.{0} (ImbalancedChen.currentChenUpsilon4 N)
            (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₄ delta) (ImbalancedChen.singularNormalization N)) →
          LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₅ delta) (ImbalancedChen.singularNormalization N))
              (ImbalancedChen.currentChenUpsilon5 N) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₆ delta) (ImbalancedChen.singularNormalization N))
                (ImbalancedChen.currentChenUpsilon6 N E) →
              LE.le.{0} (ImbalancedChen.currentChenUpsilon7 N)
                  (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₇ delta) (ImbalancedChen.singularNormalization N)) →
                LE.le.{0} (ImbalancedChen.currentChenUpsilon8 N)
                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₈ delta) (ImbalancedChen.singularNormalization N)) →
                  LE.le.{0} (ImbalancedChen.currentChenUpsilon9 N)
                      (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₉ delta) (ImbalancedChen.singularNormalization N)) →
                    LE.le.{0} (ImbalancedChen.currentChenUpsilon10 N)
                        (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₁₀ delta) (ImbalancedChen.singularNormalization N)) →
                      LE.le.{0} (ImbalancedChen.currentChenUpsilon11 N E)
                          (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₁₁ delta)
                            (ImbalancedChen.singularNormalization N)) →
                        LE.le.{0}
                          (HMul.hMul.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0}
                                (HSub.hSub.{0, 0, 0}
                                  (HSub.hSub.{0, 0, 0}
                                    (HSub.hSub.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0}
                                        (HAdd.hAdd.{0, 0, 0}
                                          (HAdd.hAdd.{0, 0, 0}
                                            (HSub.hSub.{0, 0, 0}
                                              (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 b₁) b₂)
                                                b₃)
                                              b₄)
                                            b₅)
                                          b₆)
                                        (HMul.hMul.{0, 0, 0} 2 b₇))
                                      b₈)
                                    b₉)
                                  b₁₀)
                                b₁₁)
                              (HMul.hMul.{0, 0, 0} 14 delta))
                            (ImbalancedChen.singularNormalization N))
                          (ImbalancedChen.currentChenPairedPrimeSum N E)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ delta : Real)
  (h₁ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₁ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₂ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₃ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₄ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₄ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₅ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₅ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₆ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₇ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₈ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₈ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₉ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₉ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₀ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon10 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₀ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₁ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon11 N E)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₁ delta)
        (ImbalancedChen.singularNormalization N))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 3)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              b₁)
                            b₂)
                          b₃)
                        b₄)
                      b₅)
                    b₆)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    b₇))
                b₈)
              b₉)
            b₁₀)
          b₁₁)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 14)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
          delta))
      (ImbalancedChen.singularNormalization N))
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenPairedPrimeSum_ge_of_joint_last_bounds`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenPairedPrimeSum_ge_of_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : ℝ)
    (h₁ : l₁ ≤ currentChenUpsilon1 N)
    (h₂ : l₂ ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ u₃)
    (h₄ : currentChenUpsilon4 N ≤ u₄)
    (h₅ : l₅ ≤ currentChenUpsilon5 N)
    (h₆ : l₆ ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ u₇)
    (h₈ : currentChenUpsilon8 N ≤ u₈)
    (h₉ : currentChenUpsilon9 N ≤ u₉)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤ u₁₀₁₁) :
    3 * l₁ + l₂ - u₃ - u₄ + l₅ + l₆ - 2 * u₇ - u₈ - u₉ - u₁₀₁₁ ≤
      currentChenPairedPrimeSum N E
```

编译器声明：`ImbalancedChen.currentChenPairedPrimeSum_ge_of_joint_last_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : ℝ),
  LE.le.{0} l₁ (ImbalancedChen.currentChenUpsilon1 N) →
    LE.le.{0} l₂ (ImbalancedChen.currentChenUpsilon2 N) →
      LE.le.{0} (ImbalancedChen.currentChenUpsilon3 N) u₃ →
        LE.le.{0} (ImbalancedChen.currentChenUpsilon4 N) u₄ →
          LE.le.{0} l₅ (ImbalancedChen.currentChenUpsilon5 N) →
            LE.le.{0} l₆ (ImbalancedChen.currentChenUpsilon6 N E) →
              LE.le.{0} (ImbalancedChen.currentChenUpsilon7 N) u₇ →
                LE.le.{0} (ImbalancedChen.currentChenUpsilon8 N) u₈ →
                  LE.le.{0} (ImbalancedChen.currentChenUpsilon9 N) u₉ →
                    LE.le.{0}
                        (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.currentChenUpsilon10 N)
                          (ImbalancedChen.currentChenUpsilon11 N E))
                        u₁₀₁₁ →
                      LE.le.{0}
                        (HSub.hSub.{0, 0, 0}
                          (HSub.hSub.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0}
                                (HAdd.hAdd.{0, 0, 0}
                                  (HAdd.hAdd.{0, 0, 0}
                                    (HSub.hSub.{0, 0, 0}
                                      (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 l₁) l₂) u₃) u₄)
                                    l₅)
                                  l₆)
                                (HMul.hMul.{0, 0, 0} 2 u₇))
                              u₈)
                            u₉)
                          u₁₀₁₁)
                        (ImbalancedChen.currentChenPairedPrimeSum N E)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : Real)
  (h₁ : @LE.le.{0} Real Real.instLE l₁ (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ : @LE.le.{0} Real Real.instLE l₂ (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N) u₃)
  (h₄ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N) u₄)
  (h₅ : @LE.le.{0} Real Real.instLE l₅ (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ : @LE.le.{0} Real Real.instLE l₆ (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N) u₇)
  (h₈ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N) u₈)
  (h₉ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N) u₉)
  (h₁₀₁₁ :
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ImbalancedChen.currentChenUpsilon10 N)
        (ImbalancedChen.currentChenUpsilon11 N E))
      u₁₀₁₁),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        l₁)
                      l₂)
                    u₃)
                  u₄)
                l₅)
              l₆)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              u₇))
          u₈)
        u₉)
      u₁₀₁₁)
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## `ImbalancedChen.CurrentChenMeanLedger` / `currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds`

源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`；命名空间：`ImbalancedChen`。

```lean
theorem currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds
    (N : ℕ) (E : ℕ × ℕ → Prop)
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : ℝ)
    (h₁ : (b₁ - delta) * singularNormalization N ≤ currentChenUpsilon1 N)
    (h₂ : (b₂ - delta) * singularNormalization N ≤ currentChenUpsilon2 N)
    (h₃ : currentChenUpsilon3 N ≤ (b₃ + delta) * singularNormalization N)
    (h₄ : currentChenUpsilon4 N ≤ (b₄ + delta) * singularNormalization N)
    (h₅ : (b₅ - delta) * singularNormalization N ≤ currentChenUpsilon5 N)
    (h₆ : (b₆ - delta) * singularNormalization N ≤ currentChenUpsilon6 N E)
    (h₇ : currentChenUpsilon7 N ≤ (b₇ + delta) * singularNormalization N)
    (h₈ : currentChenUpsilon8 N ≤ (b₈ + delta) * singularNormalization N)
    (h₉ : currentChenUpsilon9 N ≤ (b₉ + delta) * singularNormalization N)
    (h₁₀₁₁ : currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      (b₁₀₁₁ + 2 * delta) * singularNormalization N) :
    (3 * b₁ + b₂ - b₃ - b₄ + b₅ + b₆ - 2 * b₇ - b₈ - b₉ - b₁₀₁₁ -
      14 * delta) * singularNormalization N ≤ currentChenPairedPrimeSum N E
```

编译器声明：`ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : ℝ),
  LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₁ delta) (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N) →
    LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₂ delta) (ImbalancedChen.singularNormalization N))
        (ImbalancedChen.currentChenUpsilon2 N) →
      LE.le.{0} (ImbalancedChen.currentChenUpsilon3 N)
          (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₃ delta) (ImbalancedChen.singularNormalization N)) →
        LE.le.{0} (ImbalancedChen.currentChenUpsilon4 N)
            (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₄ delta) (ImbalancedChen.singularNormalization N)) →
          LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₅ delta) (ImbalancedChen.singularNormalization N))
              (ImbalancedChen.currentChenUpsilon5 N) →
            LE.le.{0} (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} b₆ delta) (ImbalancedChen.singularNormalization N))
                (ImbalancedChen.currentChenUpsilon6 N E) →
              LE.le.{0} (ImbalancedChen.currentChenUpsilon7 N)
                  (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₇ delta) (ImbalancedChen.singularNormalization N)) →
                LE.le.{0} (ImbalancedChen.currentChenUpsilon8 N)
                    (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₈ delta) (ImbalancedChen.singularNormalization N)) →
                  LE.le.{0} (ImbalancedChen.currentChenUpsilon9 N)
                      (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₉ delta) (ImbalancedChen.singularNormalization N)) →
                    LE.le.{0}
                        (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.currentChenUpsilon10 N)
                          (ImbalancedChen.currentChenUpsilon11 N E))
                        (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} b₁₀₁₁ (HMul.hMul.{0, 0, 0} 2 delta))
                          (ImbalancedChen.singularNormalization N)) →
                      LE.le.{0}
                        (HMul.hMul.{0, 0, 0}
                          (HSub.hSub.{0, 0, 0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0}
                                (HSub.hSub.{0, 0, 0}
                                  (HSub.hSub.{0, 0, 0}
                                    (HAdd.hAdd.{0, 0, 0}
                                      (HAdd.hAdd.{0, 0, 0}
                                        (HSub.hSub.{0, 0, 0}
                                          (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 3 b₁) b₂) b₃)
                                          b₄)
                                        b₅)
                                      b₆)
                                    (HMul.hMul.{0, 0, 0} 2 b₇))
                                  b₈)
                                b₉)
                              b₁₀₁₁)
                            (HMul.hMul.{0, 0, 0} 14 delta))
                          (ImbalancedChen.singularNormalization N))
                        (ImbalancedChen.currentChenPairedPrimeSum N E)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : Real)
  (h₁ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₁ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₂ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₃ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₄ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₄ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₅ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₅ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₆ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₇ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₈ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₈ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₉ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₉ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₀₁₁ :
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ImbalancedChen.currentChenUpsilon10 N)
        (ImbalancedChen.currentChenUpsilon11 N E))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₀₁₁
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            delta))
        (ImbalancedChen.singularNormalization N))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 3)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            b₁)
                          b₂)
                        b₃)
                      b₄)
                    b₅)
                  b₆)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  b₇))
              b₈)
            b₉)
          b₁₀₁₁)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 14)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
          delta))
      (ImbalancedChen.singularNormalization N))
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## `ImbalancedChen.CurrentPairedBuchstabBridge` / `first_fibre_buchstab_eleven_twentieths`

源码 SHA256：`280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_fibre_buchstab_eleven_twentieths {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (11 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z)
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_eleven_twentieths`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {t u z w : ℝ},
  ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w →
    LE.le.{0} (11 / 20)
      (LiLiuPrereqBuchstab.buchstab
        (HDiv.hDiv.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z) w) z))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 11)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 20)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
    (LiLiuPrereqBuchstab.buchstab
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
              u)
            z)
          w)
        z))
```

## `ImbalancedChen.CurrentPairedBuchstabBridge` / `first_fibre_buchstab_gain`

源码 SHA256：`280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550`；命名空间：`ImbalancedChen.Certificates.PairedV2`。

```lean
theorem first_fibre_buchstab_gain {t u z w : ℝ}
    (hs : firstFibreSupport t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2
```

编译器声明：`ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_gain`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {t u z w : ℝ},
  ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w →
    LE.le.{0} (1 / 20)
      (HSub.hSub.{0, 0, 0}
        (LiLiuPrereqBuchstab.buchstab
          (HDiv.hDiv.{0, 0, 0}
            (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z) w) z))
        (1 / 2))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 20)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (LiLiuPrereqBuchstab.buchstab
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                u)
              z)
            w)
          z))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## `ImbalancedChen.CurrentChenInitialSource` / `currentChen_twinPrimeConstant_eq_liuUniversalProduct`

源码 SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_twinPrimeConstant_eq_liuUniversalProduct :
    twinPrimeConstant = MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
```

## `ImbalancedChen.CurrentChenInitialSource` / `currentChen_singularSeries_eq_liuSingularSeries`

源码 SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_singularSeries_eq_liuSingularSeries (N : ℕ) :
    singularSeries N = MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N
```

## `ImbalancedChen.CurrentChenInitialSource` / `currentChen_initial_sieve_coefficient`

源码 SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_initial_sieve_coefficient :
    (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
        dimensionOneLowerLinearSieveFactor 4 =
      (33 / 4 : ℝ) * Real.log 3
```

## `ImbalancedChen.CurrentChenInitialSource` / `currentChen_goldbachS1_le_sifted_add_primeFactors`

源码 SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`；命名空间：`ImbalancedChen`。

```lean
theorem currentChen_goldbachS1_le_sifted_add_primeFactors
    (N : ℕ) (tau A z : ℝ) (hN : N ≠ 0) (htau : 0 ≤ tau) (hAz : A ≤ z) :
    (goldbachS1 (goldbachDifferenceCarrier N tau) N z : ℝ) ≤
      ((chenSiftedPrimeSource N A).card : ℝ) + (N.primeFactors.card : ℝ)
```

## `ImbalancedChen.CurrentChenInitialSource` / `eventually_currentChen_primeFactors_negligible`

源码 SHA256：`2573e544e605652b00f767e0e03eb2cd73bfe7fdb8d7f3dd48cfd1c550fc6767`；命名空间：`ImbalancedChen`。

```lean
theorem eventually_currentChen_primeFactors_negligible
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      (N.primeFactors.card : ℝ) ≤ epsilon * singularNormalization N
```

## `ImbalancedChen.CurrentChenInitialMean` / `eventually_currentChenUpsilon1_ge_initial_mean`

源码 SHA256：`adad5c2c0a98b49fed4ef832726e2fa20881b4fd8e31a270f93c32902e13e6c5`；命名空间：`ImbalancedChen`。

```lean
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N
```
