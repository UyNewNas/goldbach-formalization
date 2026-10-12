# Part 1 round 3：关键定理完整类型

以下声明头逐字提取自最终回执绑定、实际严格编译及原 checker 通过的源码；只省去 `:=` 后的证明体。没有省略声明的参数、前提或结论。完整命名空间在各节标题中给出。

对应的 Lean 环境类型、公理记录和逐声明类型哈希另见 `KEY_THEOREM_TYPES.json`；全部所属声明的实际审计记录在 `VERIFICATION.json`。此处为源码显示类型，避免 pretty-printer 对无关证明参数的隐藏影响阅读。

最终实际回执 SHA256：`4bd9c3220492d29202625fbfcf54745b34458eac7394fd7443bb74251c34b8db`。

## 1. `ImbalancedChen.mem_historicalUpperFiveFrontierTuples_iff_log_on_cell`

来源：`ImbalancedChen.HistoricalUpperFiveCellGeometry`；源码 SHA256 `a131b783d59540ea98cc11574f31489e2f75d519927445b49a2e4c688ab74cbe`。

```lean
theorem mem_historicalUpperFiveFrontierTuples_iff_log_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          0 ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ (D.b : ℝ)) ∧
        3 * actualPrimeTupleLog N p 0 < (D.old : ℝ) ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 <
              (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)
```

## 2. `ImbalancedChen.historicalUpperFiveFrontierTuples_cell_filter`

来源：`ImbalancedChen.HistoricalUpperFiveCellGeometry`；源码 SHA256 `a131b783d59540ea98cc11574f31489e2f75d519927445b49a2e4c688ab74cbe`。

```lean
theorem historicalUpperFiveFrontierTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) :
    (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms
              (D.fifthParentGateBounds j))
```

## 3. `ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection_eq_cells`

来源：`ImbalancedChen.ActualHistoricalFifthCellIntegral`；源码 SHA256 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。

```lean
theorem fifthPrimeCorrection_eq_cells (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) :
    D.fifthPrimeCorrection N cap =
      ∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j
```

## 4. `ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection_eq_residual_sums`

来源：`ImbalancedChen.ActualHistoricalFifthCellIntegral`；源码 SHA256 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。

```lean
theorem fifthCellPrimeCorrection_eq_residual_sums (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    D.fifthCellPrimeCorrection N cap j =
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.cap5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)) -
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j))
```

## 5. `ImbalancedChen.HistoricalPrefixCapData.fifthCorrectionIntegral_eq_integrals`

来源：`ImbalancedChen.ActualHistoricalFifthCellIntegral`；源码 SHA256 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。

```lean
theorem fifthCorrectionIntegral_eq_integrals (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∑ j ∈ D.cells5,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
            primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i
```

## 6. `ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection`

来源：`ImbalancedChen.ActualHistoricalFifthCellIntegral`；源码 SHA256 `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de`。

```lean
theorem tendsto_fifthPrimeCorrection (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fifthPrimeCorrection N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```

## 7. `ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_tupleSum_at_cutoff`

来源：`ImbalancedChen.ActualHistoricalFifthSavingIntegral`；源码 SHA256 `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e`。

```lean
theorem actualHistoricalFifthSaving_eq_tupleSum_at_cutoff
    (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) * D.fifthTupleOwnCubeDifference N cap p
```

## 8. `ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_fifthPrimeCorrection`

来源：`ImbalancedChen.ActualHistoricalFifthSavingIntegral`；源码 SHA256 `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e`。

```lean
theorem actualHistoricalFifthSaving_eq_fifthPrimeCorrection
    (D : HistoricalPrefixCapData) (N cap : ℕ) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ))
        N cap ((N : ℝ) ^ (D.b : ℝ)) *
        Real.log (N : ℝ) / singularSeries N =
      D.fifthPrimeCorrection N cap
```

## 9. `ImbalancedChen.HistoricalPrefixCapData.upperFourthToFifthSaving_eq`

来源：`ImbalancedChen.ActualHistoricalFifthSavingIntegral`；源码 SHA256 `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e`。

```lean
theorem upperFourthToFifthSaving_eq (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z
```

## 10. `ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving_ceil`

来源：`ImbalancedChen.ActualHistoricalFifthSavingIntegral`；源码 SHA256 `bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e`。

```lean
theorem tendsto_upperFourthToFifthSaving_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0
            ((N : ℝ) ^ (D.b : ℝ))) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))) 0
            ((N : ℝ) ^ (D.b : ℝ)))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```

## 11. `ImbalancedChen.actualPrimeFrontierTuples_ownedCell_cutoff_invariant`

来源：`ImbalancedChen.HistoricalFifthCutoffInvariance`；源码 SHA256 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`。

```lean
theorem actualPrimeFrontierTuples_ownedCell_cutoff_invariant
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (hN : 1 < N)
    (a b : ℝ) (hab : a < b) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1)) (z : ℝ) (hz : (N : ℝ) ^ b ≤ z) :
    (firstExitFrontierTuples k parent (roughPrimeUniverse N cap 0 z)).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j) =
      (firstExitFrontierTuples k parent
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ b))).filter
        (fun p => actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j)
```

## 12. `ImbalancedChen.HistoricalPrefixCapData.fifthOwnCubeDifference_outside`

来源：`ImbalancedChen.HistoricalFifthCutoffInvariance`；源码 SHA256 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`。

```lean
theorem fifthOwnCubeDifference_outside (D : HistoricalPrefixCapData)
    (N cap : ℕ) {history : List ℕ} (hlen : history.length = 5)
    (hout : ∀ j ∈ D.cells5, primeHistoryLogCoordinates (N : ℝ) 5 history ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    actualOwnCubeGatedMinusDensity N cap (D.level5 (N : ℝ)) history -
      actualOwnCubeGatedMinusDensity N cap
        (fun pre => D.level4 (N : ℝ) (rosserAncestor 4 pre)) history = 0
```

## 13. `ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge`

来源：`ImbalancedChen.HistoricalFifthCutoffInvariance`；源码 SHA256 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`。

```lean
theorem actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) (hz : (N : ℝ) ^ (D.b : ℝ) ≤ z) :
    actualHistoricalFifthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z *
        Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap
```

## 14. `ImbalancedChen.HistoricalPrefixCapData.tendsto_actualHistoricalFifthSaving_of_cutoff_ge`

来源：`ImbalancedChen.HistoricalFifthCutoffInvariance`；源码 SHA256 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`。

```lean
theorem tendsto_actualHistoricalFifthSaving_of_cutoff_ge (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) :
    Tendsto (fun N : ℕ =>
      actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N (cap N) (z N) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```

## 15. `ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving_of_cutoff_ge`

来源：`ImbalancedChen.HistoricalFifthCutoffInvariance`；源码 SHA256 `abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d`。

```lean
theorem tendsto_upperFourthToFifthSaving_of_cutoff_ge (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ) (z : ℕ → ℝ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ))
    (hz : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ z N) :
    Tendsto (fun N : ℕ =>
      (firstExitRetainedPolynomial (D.upperFourthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N (cap N) 0 (z N)) -
        firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N (cap N) 0 (z N))) *
          Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```
