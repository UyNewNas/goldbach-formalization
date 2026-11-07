# P2 本批关键完整接口

以下为实际编译器输出，与固定生产者原始 log 和 CI 原始 log 逐条相等。完整 pp.all 字段保留在同名 JSON；readable_type 保留全部量词和前提。

## ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal_range

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal_range :
∀ (i : Fin 60),
  LE.le.{0} 4 (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal i) ∧
    LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal i) 64
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates_checked

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates_checked :
∀ (i : Fin 60), Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).check Bool.true
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.geometry_checked

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.geometry_checked :
∀ (i : Fin 60),
  ImbalancedChen.Certificates.PairedV2.E0Geometry (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).1
    (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).2
    (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowZ i)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.certificate_inputs

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.certificate_inputs :
∀ (i : Fin 60),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).K ImbalancedChen.Certificates.PairedV2.K ∧
    Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).a ImbalancedChen.Certificates.PairedV2.a ∧
      Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).tl
          (ImbalancedChen.Certificates.PairedV2.tLower
            (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).1) ∧
        Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).tr
            (ImbalancedChen.Certificates.PairedV2.tUpper
              (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).1) ∧
          Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).ul
              (ImbalancedChen.Certificates.PairedV2.uLower
                (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).2) ∧
            Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).ur
                (ImbalancedChen.Certificates.PairedV2.uUpper
                  (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).2) ∧
              Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).Z
                (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowZ i)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral_eq_certificate

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral_eq_certificate :
∀ (i : Fin 60),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).K
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).a
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).tl
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).tr
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).ul
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).ur
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).Z)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral_bounds

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral_bounds :
∀ (i : Fin 60),
  LE.le.{0} (↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).lower)
      (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral i) ∧
    LE.le.{0} (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIntegral i)
      ↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.certificates i).upper
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.integral_semantics

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.integral_semantics :
Eq.{1} ImbalancedChen.Certificates.PairedV2.Batch4To64.integral
  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑ImbalancedChen.Certificates.PairedV2.K) 80)
    (∑ i,
      ∫ (t : ℝ) in
        ↑(ImbalancedChen.Certificates.PairedV2.tLower
            (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices
                i).1)..↑(ImbalancedChen.Certificates.PairedV2.tUpper
            (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).1),
        ∫ (u : ℝ) in
          ↑(ImbalancedChen.Certificates.PairedV2.uLower
              (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices
                  i).2)..↑(ImbalancedChen.Certificates.PairedV2.uUpper
              (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices i).2),
          ∫ (z : ℝ) in
            ↑ImbalancedChen.Certificates.PairedV2.a..↑(ImbalancedChen.Certificates.PairedV2.Batch4To64.rowZ i),
            ∫ (w : ℝ) in ↑ImbalancedChen.Certificates.PairedV2.a..z,
              HDiv.hDiv.{0, 0, 0} 1
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w)))
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Batch4To64.integral_bounds

```lean
ImbalancedChen.Certificates.PairedV2.Batch4To64.integral_bounds :
LE.le.{0} (↑ImbalancedChen.Certificates.PairedV2.Batch4To64.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Batch4To64.integral ∧
  LE.le.{0} ImbalancedChen.Certificates.PairedV2.Batch4To64.integral
    ↑ImbalancedChen.Certificates.PairedV2.Batch4To64.upperBound
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.source_ranges_disjoint

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.source_ranges_disjoint :
∀ (i : Fin 4) (j : Fin 60),
  Ne.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal i)
    (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal j)
```

公理依赖：propext, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.source_ordinal_coverage

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.source_ordinal_coverage :
∀ (n : ℕ),
  ((∃ i, Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal i) n) ∨
      ∃ i, Eq.{1} (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal i) n) ↔
    LT.lt.{0} n 64
```

公理依赖：propext, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices_injective

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices_injective :
Function.Injective.{1, 1} ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.prefix_batch_indices_disjoint

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.prefix_batch_indices_disjoint :
∀ (i : Fin 4) (j : Fin 60),
  Ne.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i)
    (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowIndices j)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.geometry_checked

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.geometry_checked :
∀ (i : Fin 64),
  ImbalancedChen.Certificates.PairedV2.E0Geometry (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).1
    (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).2
    (ImbalancedChen.Certificates.PairedV2.Prefix64.rowZ i)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.fibre_argument

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.fibre_argument :
∀ (i : Fin 64) {t u z w : ℝ},
  ImbalancedChen.Certificates.PairedV2.openFibreSupport (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).1
      (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).2
      (ImbalancedChen.Certificates.PairedV2.Prefix64.rowZ i) t u z w →
    LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.a) w ∧
      LT.lt.{0} w z ∧
        LT.lt.{0} z u ∧
          LT.lt.{0} u ↑ImbalancedChen.Certificates.PairedV2.h ∧
            LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.h) t ∧
              LT.lt.{0} t ↑ImbalancedChen.Certificates.PairedV2.d ∧
                LE.le.{0} (7 / 3)
                  (HDiv.hDiv.{0, 0, 0}
                    (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z) w) z)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts :
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.Prefix4.integral
    ImbalancedChen.Certificates.PairedV2.Batch4To64.integral)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_semantics

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.integral_semantics :
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑ImbalancedChen.Certificates.PairedV2.K) 80)
    (∑ i,
      ∫ (t : ℝ) in
        ↑(ImbalancedChen.Certificates.PairedV2.tLower
            (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices
                i).1)..↑(ImbalancedChen.Certificates.PairedV2.tUpper
            (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).1),
        ∫ (u : ℝ) in
          ↑(ImbalancedChen.Certificates.PairedV2.uLower
              (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices
                  i).2)..↑(ImbalancedChen.Certificates.PairedV2.uUpper
              (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i).2),
          ∫ (z : ℝ) in ↑ImbalancedChen.Certificates.PairedV2.a..↑(ImbalancedChen.Certificates.PairedV2.Prefix64.rowZ i),
            ∫ (w : ℝ) in ↑ImbalancedChen.Certificates.PairedV2.a..z,
              HDiv.hDiv.{0, 0, 0} 1
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w)))
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound_eq_sum

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound_eq_sum :
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound
  (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
    ImbalancedChen.Certificates.PairedV2.Batch4To64.lowerBound)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound_eq_sum

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound_eq_sum :
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound
  (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
    ImbalancedChen.Certificates.PairedV2.Batch4To64.upperBound)
```

公理依赖：propext, Classical.choice, Quot.sound

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_bounds

```lean
ImbalancedChen.Certificates.PairedV2.Prefix64.integral_bounds :
LE.le.{0} (↑ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix64.integral ∧
  LE.le.{0} ImbalancedChen.Certificates.PairedV2.Prefix64.integral
    ↑ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound
```

公理依赖：propext, Classical.choice, Quot.sound
