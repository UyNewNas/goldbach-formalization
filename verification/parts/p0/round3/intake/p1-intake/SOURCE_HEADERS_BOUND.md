# P1 生产源码定理头与实际审计类型对应

固定源码：`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`。以下第一栏为完整源码声明头，第二栏为原始审计实际 pretty 类型；后者不是 `pp.all`，证明参数省略符保留。本文不伪造新的 Lean 输出。

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cube_filter

模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (a b old : ℝ),
  1 < N →
    ↑N ^ b ≤ ↑cap →
      {p ∈
            ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
              (ImbalancedChen.roughPrimeUniverse N cap 0 (↑N ^ b)) |
          p ∈ ImbalancedChen.actualPrimeBoxTuples N (fun x => a) fun x => b} =
        {p ∈ ImbalancedChen.actualPrimeBoxTuples N (fun x => a) fun x => b |
          ImbalancedChen.actualPrimeTupleLog N p ∈
            ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds old)}
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter

模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (a b old : ℝ),
  a < b →
    1 < N →
      ↑N ^ b ≤ ↑cap →
        ∀ (m : ℕ) (j : Fin 4 → Fin (m + 1)),
          {p ∈
                ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
                  (ImbalancedChen.roughPrimeUniverse N cap 0 (↑N ^ b)) |
              ImbalancedChen.actualPrimeTupleLog N p ∈ ImbalancedChen.logPrimeMeshCell a b m j} =
            {p ∈ ImbalancedChen.actualPrimeBoxTuples N (fun x => a) fun x => b |
              ImbalancedChen.actualPrimeTupleLog N p ∈
                ImbalancedChen.logPrimeMeshCell a b m j ∩
                  ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                    (ImbalancedChen.ordinaryLowerFourGateBounds old)}
```

## ImbalancedChen.ordinaryLowerFourFrontier_cell_weighted_sum

模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (a b old : ℝ),
  a < b →
    1 < N →
      ↑N ^ b ≤ ↑cap →
        ∀ (m : ℕ) (j : Fin 4 → Fin (m + 1)) (f : (Fin 4 → ℕ) → ℝ),
          (∑
              p ∈
                ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
                  (ImbalancedChen.roughPrimeUniverse N cap 0 (↑N ^ b)),
              (∏ i, 1 / (↑(p i) - 1)) *
                if ImbalancedChen.actualPrimeTupleLog N p ∈ ImbalancedChen.logPrimeMeshCell a b m j then f p else 0) =
            ∑ p ∈ ImbalancedChen.actualPrimeBoxTuples N (fun x => a) fun x => b,
              (∏ i, 1 / (↑(p i) - 1)) *
                if
                    ImbalancedChen.actualPrimeTupleLog N p ∈
                      ImbalancedChen.logPrimeMeshCell a b m j ∩
                        ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                          (ImbalancedChen.ordinaryLowerFourGateBounds old) then
                  f p
                else 0
```

## ImbalancedChen.ordinaryLowerFourFrontier_cell_ownCube_difference

模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (a b old lambda : ℝ),
  a < b →
    1 < N →
      ↑N ^ b ≤ ↑cap →
        ∀ (m : ℕ) (j : Fin 4 → Fin (m + 1)),
          (∑
              p ∈
                ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
                  (ImbalancedChen.roughPrimeUniverse N cap 0 (↑N ^ b)),
              (∏ i, 1 / (↑(p i) - 1)) *
                if ImbalancedChen.actualPrimeTupleLog N p ∈ ImbalancedChen.logPrimeMeshCell a b m j then
                  ImbalancedChen.actualPrimeTupleOwnCubeMinus N cap lambda p -
                    ImbalancedChen.actualPrimeTupleOwnCubeMinus N cap old p
                else 0) =
            ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap a b lambda
                (ImbalancedChen.logPrimeMeshCell a b m j ∩
                  ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                    (ImbalancedChen.ordinaryLowerFourGateBounds old)) -
              ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap a b old
                (ImbalancedChen.logPrimeMeshCell a b m j ∩
                  ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                    (ImbalancedChen.ordinaryLowerFourGateBounds old))
```

## ImbalancedChen.actualSelectedPrefixLowerOwnCubeSum_eq_cells

模块：`ImbalancedChen.ActualSelectedPrefixLowerCellSum`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (I : Finset (Fin 4)) (old nu a b : ℚ),
  a < b →
    1 < N →
      ↑N ^ ↑b ≤ ↑cap →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          ImbalancedChen.actualSelectedPrefixOwnCubeSum true N cap (↑N ^ ↑b) I old nu a b m J * Real.log ↑N /
              ImbalancedChen.singularSeries N =
            ∑ j ∈ J,
              (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap (↑a) (↑b)
                  (↑(ImbalancedChen.selectedPrefixCellCap I old nu a b m j))
                  (ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                    ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                      (ImbalancedChen.ordinaryLowerFourGateBounds ↑old)) -
                ImbalancedChen.actualPrimeBoxOwnCubeMinusSum 3 N cap (↑a) (↑b) (↑old)
                  (ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                    ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                      (ImbalancedChen.ordinaryLowerFourGateBounds ↑old)))
```

## ImbalancedChen.selectedPrefixLowerRestorationIntegral_eq_integrals

模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
        ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J =
          ∑ j ∈ J,
            ∫ (t : Fin 4 → ℝ) in
              ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j ∩
                ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
                  (ImbalancedChen.ordinaryLowerFourGateBounds ↑old),
              (ImbalancedChen.primeOwnCubeGatedProfile (↑(ImbalancedChen.selectedPrefixCellCap I old nu a b m j)) t -
                  ImbalancedChen.primeOwnCubeGatedProfile (↑old) t) *
                ∏ i, 1 / t i
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerOwnCubeSum

模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))) (cap : ℕ → ℕ),
        (∀ᶠ (N : ℕ) in Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N}, ↑N ^ ↑b ≤ ↑(cap N)) →
          Filter.Tendsto
            (fun N =>
              ImbalancedChen.actualSelectedPrefixOwnCubeSum true N (cap N) (↑N ^ ↑b) I old nu a b m J * Real.log ↑N /
                ImbalancedChen.singularSeries N)
            (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
            (nhds (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_restoration

模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      b ≤ old →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          (∀ j ∈ J,
              ImbalancedChen.selectedBoxCapCheck I old nu (ImbalancedChen.qLogPrimeMeshLo a b m j)
                  (ImbalancedChen.qLogPrimeMeshHi a b m j) =
                true) →
            ∀ (cap : ℕ → ℕ),
              (∀ᶠ (N : ℕ) in Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N}, ↑N ^ ↑b ≤ ↑(cap N)) →
                Filter.Tendsto
                  (fun N =>
                    (ImbalancedChen.actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J -
                          ImbalancedChen.actualSmallRosserMinusDensity N (cap N) (↑N ^ ↑b) (↑N ^ ↑old)) *
                        Real.log ↑N /
                      ImbalancedChen.singularSeries N)
                  (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
                  (nhds (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_normalized

模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      2 * b ≤ old →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          (∀ j ∈ J,
              ImbalancedChen.selectedBoxCapCheck I old nu (ImbalancedChen.qLogPrimeMeshLo a b m j)
                  (ImbalancedChen.qLogPrimeMeshHi a b m j) =
                true) →
            ∀ (cap : ℕ → ℕ),
              (∀ᶠ (N : ℕ) in Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N}, ↑N ^ ↑b ≤ ↑(cap N)) →
                Filter.Tendsto
                  (fun N =>
                    ImbalancedChen.actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J * Real.log ↑N /
                      ImbalancedChen.singularSeries N)
                  (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
                  (nhds
                    (2 * Real.exp (-Real.eulerMascheroniConstant) / ↑b *
                        MathlibNt.SieveTheory.suzukiContinuousLowerFactor (↑old / ↑b) +
                      ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized

模块：`ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (I : Finset (Fin 4)) (old nu a b : ℚ),
  0 < a →
    a < b →
      2 * b ≤ old →
        ∀ (m : ℕ) (J : Finset (Fin 4 → Fin (m + 1))),
          (∀ j ∈ J,
              ImbalancedChen.selectedBoxCapCheck I old nu (ImbalancedChen.qLogPrimeMeshLo a b m j)
                  (ImbalancedChen.qLogPrimeMeshHi a b m j) =
                true) →
            Filter.Tendsto
              (fun N =>
                ImbalancedChen.actualSelectedPrefixLowerDensity N ⌈↑N ^ ↑b⌉₊ I old nu a b m J * Real.log ↑N /
                  ImbalancedChen.singularSeries N)
              (Filter.atTop ⊓ Filter.principal {N | 0 < N ∧ Even N})
              (nhds
                (2 * Real.exp (-Real.eulerMascheroniConstant) / ↑b *
                    MathlibNt.SieveTheory.suzukiContinuousLowerFactor (↑old / ↑b) +
                  ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.historicalPrefixProject_comp

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixProject_comp {α : Type*} {r d e : ℕ}
    (hrd : r ≤ d) (hde : d ≤ e) (t : Fin e → α) :
    historicalPrefixProject hrd (historicalPrefixProject hde t) =
      historicalPrefixProject (hrd.trans hde) t
```

实际审计 pretty 类型：

```lean
∀ {α : Type u_1} {r d e : ℕ} (hrd : r ≤ d) (hde : d ≤ e) (t : Fin e → α),
  ImbalancedChen.historicalPrefixProject hrd (ImbalancedChen.historicalPrefixProject hde t) =
    ImbalancedChen.historicalPrefixProject ⋯ t
```

## ImbalancedChen.mem_logPrimeMeshCell_historicalPrefixProject

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem mem_logPrimeMeshCell_historicalPrefixProject {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} {j : Fin d → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j) :
    historicalPrefixProject hrd t ∈
      logPrimeMeshCell a b m (historicalPrefixProject hrd j)
```

实际审计 pretty 类型：

```lean
∀ {r d m : ℕ} (hrd : r ≤ d) {a b : ℝ} {j : Fin d → Fin (m + 1)} {t : Fin d → ℝ},
  t ∈ ImbalancedChen.logPrimeMeshCell a b m j →
    ImbalancedChen.historicalPrefixProject hrd t ∈
      ImbalancedChen.logPrimeMeshCell a b m (ImbalancedChen.historicalPrefixProject hrd j)
```

## ImbalancedChen.historicalPrefixAncestorCell_unique

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixAncestorCell_unique {r d m : ℕ}
    (hrd : r ≤ d) {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)}
    {t : Fin d → ℝ} (ht : t ∈ logPrimeMeshCell a b m j)
    (hq : historicalPrefixProject hrd t ∈ logPrimeMeshCell a b m q) :
    q = historicalPrefixProject hrd j
```

实际审计 pretty 类型：

```lean
∀ {r d m : ℕ} (hrd : r ≤ d) {a b : ℝ},
  a ≤ b →
    ∀ {j : Fin d → Fin (m + 1)} {q : Fin r → Fin (m + 1)} {t : Fin d → ℝ},
      t ∈ ImbalancedChen.logPrimeMeshCell a b m j →
        ImbalancedChen.historicalPrefixProject hrd t ∈ ImbalancedChen.logPrimeMeshCell a b m q →
          q = ImbalancedChen.historicalPrefixProject hrd j
```

## ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem primeHistoryLogCoordinates_eq_historicalPrefixProject (N : ℝ)
    {r d : ℕ} (hrd : r ≤ d) {history : List ℕ} (hlen : history.length = d) :
    primeHistoryLogCoordinates N r (rosserAncestor r history) =
      historicalPrefixProject hrd (primeHistoryLogCoordinates N d history)
```

实际审计 pretty 类型：

```lean
∀ (N : ℝ) {r d : ℕ} (hrd : r ≤ d) {history : List ℕ},
  history.length = d →
    ImbalancedChen.primeHistoryLogCoordinates N r (ImbalancedChen.rosserAncestor r history) =
      ImbalancedChen.historicalPrefixProject hrd (ImbalancedChen.primeHistoryLogCoordinates N d history)
```

## ImbalancedChen.historicalPrefixLookup_on_cell

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixLookup_on_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1)) (hj : j ∈ J)
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = cap j
```

实际审计 pretty 类型：

```lean
∀ {d : ℕ} (a b : ℚ),
  a ≤ b →
    ∀ (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ),
      ∀ j ∈ J,
        t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j →
          ImbalancedChen.historicalPrefixLookup a b m J cap fallback t = cap j
```

## ImbalancedChen.historicalPrefixLookup_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixLookup_outside {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (ht : ∀ j ∈ J, t ∉ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t = fallback
```

实际审计 pretty 类型：

```lean
∀ {d : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ)
  (t : Fin d → ℝ),
  (∀ j ∈ J, t ∉ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j) →
    ImbalancedChen.historicalPrefixLookup a b m J cap fallback t = fallback
```

## ImbalancedChen.historicalPrefixLookup_on_any_cell

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixLookup_on_any_cell {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (j : Fin d → Fin (m + 1))
    (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    historicalPrefixLookup a b m J cap fallback t =
      if j ∈ J then cap j else fallback
```

实际审计 pretty 类型：

```lean
∀ {d : ℕ} (a b : ℚ),
  a ≤ b →
    ∀ (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
      (j : Fin d → Fin (m + 1)),
      t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j →
        ImbalancedChen.historicalPrefixLookup a b m J cap fallback t = if j ∈ J then cap j else fallback
```

## ImbalancedChen.historicalPrefixLookup_ge_fallback

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixLookup_ge_fallback {d : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin d → Fin (m + 1)))
    (old cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (hlevel : ∀ j ∈ J, old j ≤ cap j)
    (hinherit : ∀ j ∈ J,
      t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j → fallback = old j) :
    fallback ≤ historicalPrefixLookup a b m J cap fallback t
```

实际审计 pretty 类型：

```lean
∀ {d : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (old cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ)
  (t : Fin d → ℝ),
  (∀ j ∈ J, old j ≤ cap j) →
    (∀ j ∈ J, t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j → fallback = old j) →
      fallback ≤ ImbalancedChen.historicalPrefixLookup a b m J cap fallback t
```

## ImbalancedChen.historicalPrefixLookup_apply_sub

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem historicalPrefixLookup_apply_sub {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (J : Finset (Fin d → Fin (m + 1)))
    (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
    (f : ℚ → ℝ) :
    f (historicalPrefixLookup a b m J cap fallback t) - f fallback =
      ∑ j ∈ J, if t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j then
        f (cap j) - f fallback else 0
```

实际审计 pretty 类型：

```lean
∀ {d : ℕ} (a b : ℚ),
  a ≤ b →
    ∀ (m : ℕ) (J : Finset (Fin d → Fin (m + 1))) (cap : (Fin d → Fin (m + 1)) → ℚ) (fallback : ℚ) (t : Fin d → ℝ)
      (f : ℚ → ℝ),
      f (ImbalancedChen.historicalPrefixLookup a b m J cap fallback t) - f fallback =
        ∑ j ∈ J, if t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j then f (cap j) - f fallback else 0
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck_sound

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem levelCheck_sound (D : HistoricalPrefixCapData) (h : D.levelCheck = true) :
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧
      (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧
      (∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.levelCheck = true →
    (∀ j ∈ D.cells3, D.old ≤ D.cap3 j) ∧ (∀ j ∈ D.cells4, D.old4 j ≤ D.cap4 j) ∧ ∀ j ∈ D.cells5, D.old5 j ≤ D.cap5 j
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck_of_selectedBoxCapChecks

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (I3 : (Fin 3 → Fin (D.m + 1)) → Finset (Fin 3))
  (I4 : (Fin 4 → Fin (D.m + 1)) → Finset (Fin 4)) (I5 : (Fin 5 → Fin (D.m + 1)) → Finset (Fin 5))
  (nu3 : (Fin 3 → Fin (D.m + 1)) → ℚ) (nu4 : (Fin 4 → Fin (D.m + 1)) → ℚ) (nu5 : (Fin 5 → Fin (D.m + 1)) → ℚ),
  (∀ j ∈ D.cells3,
      D.cap3 j =
          ImbalancedChen.selectedBoxCap (I3 j) D.old (nu3 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
            (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
        ImbalancedChen.selectedBoxCapCheck (I3 j) D.old (nu3 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
            (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
          true) →
    (∀ j ∈ D.cells4,
        D.cap4 j =
            ImbalancedChen.selectedBoxCap (I4 j) (D.old4 j) (nu4 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
              (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
          ImbalancedChen.selectedBoxCapCheck (I4 j) (D.old4 j) (nu4 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
              (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
            true) →
      (∀ j ∈ D.cells5,
          D.cap5 j =
              ImbalancedChen.selectedBoxCap (I5 j) (D.old5 j) (nu5 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
                (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) ∧
            ImbalancedChen.selectedBoxCapCheck (I5 j) (D.old5 j) (nu5 j) (ImbalancedChen.qLogPrimeMeshLo D.a D.b D.m j)
                (ImbalancedChen.qLogPrimeMeshHi D.a D.b D.m j) =
              true) →
        D.levelCheck = true
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_on_cell

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent3_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 3 → ℝ) (j : Fin 3 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.cell3 j
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 3 → ℝ) (j : Fin 3 → Fin (D.m + 1)),
      t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j → D.exponent3 t = D.cell3 j
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_on_cell

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent4_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (j : Fin 4 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.cell4 j
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 4 → ℝ) (j : Fin 4 → Fin (D.m + 1)),
      t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j → D.exponent4 t = D.cell4 j
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_on_cell

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent5_on_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1))
    (ht : t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.cell5 j
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 5 → ℝ) (j : Fin 5 → Fin (D.m + 1)),
      t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j → D.exponent5 t = D.cell5 j
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent3_outside (D : HistoricalPrefixCapData) (t : Fin 3 → ℝ)
    (ht : ∀ j ∈ D.cells3,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent3 t = D.old
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (t : Fin 3 → ℝ),
  (∀ j ∈ D.cells3, t ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) → D.exponent3 t = D.old
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent4_outside (D : HistoricalPrefixCapData) (t : Fin 4 → ℝ)
    (ht : ∀ j ∈ D.cells4,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent4 t = D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (t : Fin 4 → ℝ),
  (∀ j ∈ D.cells4, t ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
    D.exponent4 t = D.exponent3 (ImbalancedChen.historicalPrefixProject ⋯ t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent5_outside (D : HistoricalPrefixCapData) (t : Fin 5 → ℝ)
    (ht : ∀ j ∈ D.cells5,
      t ∉ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.exponent5 t = D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (t : Fin 5 → ℝ),
  (∀ j ∈ D.cells5, t ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
    D.exponent5 t = D.exponent4 (ImbalancedChen.historicalPrefixProject ⋯ t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_apply_sub

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent4_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 4 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent4 t) -
        f (D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t)) =
      ∑ j ∈ D.cells4,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap4 j) - f (D.old4 j) else 0
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 4 → ℝ) (f : ℚ → ℝ),
      f (D.exponent4 t) - f (D.exponent3 (ImbalancedChen.historicalPrefixProject ⋯ t)) =
        ∑ j ∈ D.cells4,
          if t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j then f (D.cap4 j) - f (D.old4 j) else 0
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent5_apply_sub (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (t : Fin 5 → ℝ) (f : ℚ → ℝ) :
    f (D.exponent5 t) -
        f (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t)) =
      ∑ j ∈ D.cells5,
        if t ∈ logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then
          f (D.cap5 j) - f (D.old5 j) else 0
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    ∀ (t : Fin 5 → ℝ) (f : ℚ → ℝ),
      f (D.exponent5 t) - f (D.exponent4 (ImbalancedChen.historicalPrefixProject ⋯ t)) =
        ∑ j ∈ D.cells5,
          if t ∈ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j then f (D.cap5 j) - f (D.old5 j) else 0
```

## ImbalancedChen.HistoricalPrefixCapData.old_le_exponent3

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem old_le_exponent3 (D : HistoricalPrefixCapData) (hcheck : D.levelCheck = true)
    (t : Fin 3 → ℝ) : D.old ≤ D.exponent3 t
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData), D.levelCheck = true → ∀ (t : Fin 3 → ℝ), D.old ≤ D.exponent3 t
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_le_exponent4

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent3_le_exponent4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 4 → ℝ) :
    D.exponent3 (historicalPrefixProject (by omega : 3 ≤ 4) t) ≤ D.exponent4 t
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true → ∀ (t : Fin 4 → ℝ), D.exponent3 (ImbalancedChen.historicalPrefixProject ⋯ t) ≤ D.exponent4 t
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_le_exponent5

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem exponent4_le_exponent5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (t : Fin 5 → ℝ) :
    D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤ D.exponent5 t
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true → ∀ (t : Fin 5 → ℝ), D.exponent4 (ImbalancedChen.historicalPrefixProject ⋯ t) ≤ D.exponent5 t
```

## ImbalancedChen.HistoricalPrefixCapData.level3_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem level3_outside (D : HistoricalPrefixCapData) (N : ℝ) (history : List ℕ)
    (hout : ∀ j ∈ D.cells3, primeHistoryLogCoordinates N 3 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N history = N ^ (D.old : ℝ)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (history : List ℕ),
  (∀ j ∈ D.cells3,
      ImbalancedChen.primeHistoryLogCoordinates N 3 history ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
    D.level3 N history = N ^ ↑D.old
```

## ImbalancedChen.HistoricalPrefixCapData.level4_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem level4_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 4)
    (hout : ∀ j ∈ D.cells4, primeHistoryLogCoordinates N 4 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N history = D.level3 N (rosserAncestor 3 history)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (history : List ℕ),
  history.length = 4 →
    (∀ j ∈ D.cells4,
        ImbalancedChen.primeHistoryLogCoordinates N 4 history ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
      D.level4 N history = D.level3 N (ImbalancedChen.rosserAncestor 3 history)
```

## ImbalancedChen.HistoricalPrefixCapData.level5_outside

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem level5_outside (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates N 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = D.level4 N (rosserAncestor 4 history)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (history : List ℕ),
  history.length = 5 →
    (∀ j ∈ D.cells5,
        ImbalancedChen.primeHistoryLogCoordinates N 5 history ∉ ImbalancedChen.logPrimeMeshCell (↑D.a) (↑D.b) D.m j) →
      D.level5 N history = D.level4 N (ImbalancedChen.rosserAncestor 4 history)
```

## ImbalancedChen.HistoricalPrefixCapData.level3_ancestor_le_level4

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem level3_ancestor_le_level4 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 4) :
    D.level3 N (rosserAncestor 3 history) ≤ D.level4 N history
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true →
      ∀ (N : ℝ),
        1 < N →
          ∀ (history : List ℕ),
            history.length = 4 → D.level3 N (ImbalancedChen.rosserAncestor 3 history) ≤ D.level4 N history
```

## ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_le_level5

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem level4_ancestor_le_level5 (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N : ℝ) (hN : 1 < N)
    (history : List ℕ) (hlen : history.length = 5) :
    D.level4 N (rosserAncestor 4 history) ≤ D.level5 N history
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true →
      ∀ (N : ℝ),
        1 < N →
          ∀ (history : List ℕ),
            history.length = 5 → D.level4 N (ImbalancedChen.rosserAncestor 4 history) ≤ D.level5 N history
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy_even

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem upperThirdPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperThirdPolicy N true pre = true
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ), D.upperThirdPolicy N true pre = true
```

## ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy_even

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem upperFourthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFourthPolicy N true pre = true
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ), D.upperFourthPolicy N true pre = true
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_even

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem upperFifthPolicy_even (D : HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ) :
    D.upperFifthPolicy N true pre = true
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ) (pre : List ℕ), D.upperFifthPolicy N true pre = true
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_eq_oddFirstExitPolicy

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem upperFifthPolicy_eq_oddFirstExitPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    D.upperFifthPolicy N = oddFirstExitPolicy (fun pre => D.upperFifthPolicy N false pre)
```

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : ℝ),
  D.upperFifthPolicy N = ImbalancedChen.oddFirstExitPolicy fun pre => D.upperFifthPolicy N false pre
```

## ImbalancedChen.HistoricalPrefixCapData.actual_thirdToFifthSaving_eq

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true →
      ∀ (base : Bool → List ℕ → Bool) (N cap : ℕ),
        1 < ↑N →
          ∀ (z : ℝ),
            ImbalancedChen.firstExitRetainedPolynomial (ImbalancedChen.thirdCappedUpperPolicy base (D.level3 ↑N))
                  (fun p => 1 / (↑p - 1)) [] true 1 (ImbalancedChen.roughPrimeUniverse N cap 0 z) -
                ImbalancedChen.firstExitRetainedPolynomial
                  (ImbalancedChen.fifthCappedUpperPolicy base (D.level3 ↑N) (D.level5 ↑N)) (fun p => 1 / (↑p - 1)) []
                  true 1 (ImbalancedChen.roughPrimeUniverse N cap 0 z) =
              ImbalancedChen.actualHistoricalFourthSaving base (D.level3 ↑N) (D.level4 ↑N) N cap z +
                ImbalancedChen.actualHistoricalFifthSaving base (D.level3 ↑N) (D.level4 ↑N) (D.level5 ↑N) N cap z
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdToFifthSaving_eq

模块：`ImbalancedChen.HistoricalPrefixCertificate`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  D.a ≤ D.b →
    D.levelCheck = true →
      ∀ (N cap : ℕ),
        1 < ↑N →
          ∀ (z : ℝ),
            ImbalancedChen.firstExitRetainedPolynomial (D.upperThirdPolicy ↑N) (fun p => 1 / (↑p - 1)) [] true 1
                  (ImbalancedChen.roughPrimeUniverse N cap 0 z) -
                ImbalancedChen.firstExitRetainedPolynomial (D.upperFifthPolicy ↑N) (fun p => 1 / (↑p - 1)) [] true 1
                  (ImbalancedChen.roughPrimeUniverse N cap 0 z) =
              ImbalancedChen.actualHistoricalFourthSaving
                  (ImbalancedChen.ordinaryParityRosserPolicy false (↑N ^ ↑D.old)) (D.level3 ↑N) (D.level4 ↑N) N cap z +
                ImbalancedChen.actualHistoricalFifthSaving
                  (ImbalancedChen.ordinaryParityRosserPolicy false (↑N ^ ↑D.old)) (D.level3 ↑N) (D.level4 ↑N)
                  (D.level5 ↑N) N cap z
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
private theorem lowerRosserAdmissibleSet_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h21 : p2 < p1) :
    LowerAdmissibleSet Q [p2, p1].toFinset ↔
      (p1 : ℝ) * p2 ^ 3 < Q
```

实际审计 pretty 类型：

```lean
∀ (Q : ℝ) (p1 p2 : ℕ),
  p2 < p1 → (MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet Q [p2, p1].toFinset ↔ ↑p1 * ↑p2 ^ 3 < Q)
```

## ImbalancedChen.ordinaryRosserPrefixAdmissible_lower_two_iff

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem ordinaryRosserPrefixAdmissible_lower_two_iff
    (Q : ℝ) (p1 p2 : ℕ) (h2 : 0 < p2) (h21 : p2 < p1) :
    ordinaryRosserPrefixAdmissible true Q [p2, p1] ↔
      (p1 : ℝ) * p2 ^ 3 < Q
```

实际审计 pretty 类型：

```lean
∀ (Q : ℝ) (p1 p2 : ℕ),
  0 < p2 → p2 < p1 → (ImbalancedChen.ordinaryRosserPrefixAdmissible true Q [p2, p1] ↔ ↑p1 * ↑p2 ^ 3 < Q)
```

## ImbalancedChen.ordinaryLowerFour_parent_valid_iff

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem ordinaryLowerFour_parent_valid_iff
    (Q : ℝ) (p : Fin 4 → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hsort : StrictAnti p) :
    FirstExitValidSelection (ordinaryParityRosserPolicy true Q) [] true
      (List.ofFn p).dropLast ↔
      (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < Q
```

实际审计 pretty 类型：

```lean
∀ (Q : ℝ) (p : Fin 4 → ℕ),
  (∀ (i : Fin 4), Nat.Prime (p i)) →
    StrictAnti p →
      (ImbalancedChen.FirstExitValidSelection (ImbalancedChen.ordinaryParityRosserPolicy true Q) [] true
          (List.ofFn p).dropLast ↔
        ↑(p 0) * ↑(p 1) ^ 3 < Q)
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (Q : ℝ) (N cap : ℕ) (w z : ℝ) (p : Fin 4 → ℕ),
  p ∈
      ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true Q)
        (ImbalancedChen.roughPrimeUniverse N cap w z) ↔
    StrictAnti p ∧
      (∀ (i : Fin 4), p i < cap ∧ Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ ↑(p i) ∧ ↑(p i) < z) ∧ ↑(p 0) * ↑(p 1) ^ 3 < Q
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (Q : ℝ) (N cap : ℕ) (w z : ℝ),
  z ≤ ↑cap →
    ∀ (p : Fin 4 → ℕ),
      p ∈
          ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true Q)
            (ImbalancedChen.roughPrimeUniverse N cap w z) ↔
        StrictAnti p ∧ (∀ (i : Fin 4), Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ ↑(p i) ∧ ↑(p i) < z) ∧ ↑(p 0) * ↑(p 1) ^ 3 < Q
```

## ImbalancedChen.ordinaryLowerFour_cube_test_iff_log

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem ordinaryLowerFour_cube_test_iff_log {N : ℕ} (hN : 1 < N)
    (old : ℝ) (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) :
    (p 0 : ℝ) * (p 1 : ℝ) ^ 3 < (N : ℝ) ^ old ↔
      actualPrimeTupleLog N p 0 + 3 * actualPrimeTupleLog N p 1 < old
```

实际审计 pretty 类型：

```lean
∀ {N : ℕ},
  1 < N →
    ∀ (old : ℝ) (p : Fin 4 → ℕ),
      (∀ (i : Fin 4), 0 < p i) →
        (↑(p 0) * ↑(p 1) ^ 3 < ↑N ^ old ↔
          ImbalancedChen.actualPrimeTupleLog N p 0 + 3 * ImbalancedChen.actualPrimeTupleLog N p 1 < old)
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_log

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

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

实际审计 pretty 类型：

```lean
∀ (N cap : ℕ) (old w z : ℝ),
  1 < N →
    z ≤ ↑cap →
      ∀ (p : Fin 4 → ℕ),
        p ∈
            ImbalancedChen.firstExitFrontierTuples 3 (ImbalancedChen.ordinaryParityRosserPolicy true (↑N ^ old))
              (ImbalancedChen.roughPrimeUniverse N cap w z) ↔
          StrictAnti p ∧
            (∀ (i : Fin 4), Nat.Prime (p i) ∧ ¬p i ∣ N ∧ w ≤ ↑(p i) ∧ ↑(p i) < z) ∧
              ImbalancedChen.actualPrimeTupleLog N p 0 + 3 * ImbalancedChen.actualPrimeTupleLog N p 1 < old
```

## ImbalancedChen.ordinaryLowerFourGateForms_ne_zero

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem ordinaryLowerFourGateForms_ne_zero : ∀ j, ordinaryLowerFourGateForms j ≠ 0
```

实际审计 pretty 类型：

```lean
∀ (j : Fin 4), ImbalancedChen.ordinaryLowerFourGateForms j ≠ 0
```

## ImbalancedChen.mem_ordinaryLowerFourGateRegion

模块：`ImbalancedChen.OrdinaryLowerFourFrontier`；公理：`propext, Classical.choice, Quot.sound`。

完整源码声明头：

```lean
theorem mem_ordinaryLowerFourGateRegion (old : ℝ) (t : Fin 4 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryLowerFourGateForms (ordinaryLowerFourGateBounds old) ↔
      StrictAnti t ∧ t 0 + 3 * t 1 < old
```

实际审计 pretty 类型：

```lean
∀ (old : ℝ) (t : Fin 4 → ℝ),
  t ∈
      ImbalancedChen.primeAffineGateRegion ImbalancedChen.ordinaryLowerFourGateForms
        (ImbalancedChen.ordinaryLowerFourGateBounds old) ↔
    StrictAnti t ∧ t 0 + 3 * t 1 < old
```

