# P2 本批新增模块完整编译器类型

固定源码 `6acf61cc28f227a9154363f2347c386ec01dffb0`，交接 `076473720210ee602e6e9735902e16bb6c5f1398`。以下 56 条来自实际成功审计，含 private/generated 声明；同固定 SHA 的 GitHub Actions 输出逐条相同。

## ImbalancedChen.Certificates.PairedV2.E0Geometry

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `definition`

### 完整 pp.all 类型

```lean
(i j : Nat) → (Z : Rat) → Prop
```

### 完整可读类型

```lean
ℕ → ℕ → ℚ → Prop
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `definition`

### 完整 pp.all 类型

```lean
(i j : Nat) → (Z : Rat) → Bool
```

### 完整可读类型

```lean
ℕ → ℕ → ℚ → Bool
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_fibre_argument

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true)
  {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
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

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true →
    ∀ {t u z w : ℝ},
      ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w →
        LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.a) w ∧
          LT.lt.{0} w z ∧
            LT.lt.{0} z u ∧
              LT.lt.{0} u ↑ImbalancedChen.Certificates.PairedV2.h ∧
                LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.h) t ∧
                  LT.lt.{0} t ↑ImbalancedChen.Certificates.PairedV2.d ∧
                    LE.le.{0} (7 / 3)
                      (HDiv.hDiv.{0, 0, 0}
                        (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z)
                          w)
                        z)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_sound

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true),
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z
```

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true →
    ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.instDecidableE0Geometry

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `definition`

### 完整 pp.all 类型

```lean
(i j : Nat) → (Z : Rat) → Decidable (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
```

### 完整可读类型

```lean
(i j : ℕ) → (Z : ℚ) → Decidable (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.openFibreSupport

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `definition`

### 完整 pp.all 类型

```lean
(i j : Nat) → (Z : Rat) → (t u z w : Real) → Prop
```

### 完整可读类型

```lean
ℕ → ℕ → ℚ → ℝ → ℝ → ℝ → ℝ → Prop
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.E0Geometry.cutoff_bound

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z),
  @LE.le.{0} Rat Rat.instLE
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
      Z)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.PairedV2.tUpper i))
      (ImbalancedChen.Certificates.PairedV2.uUpper j))
```

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z →
    LE.le.{0} (HMul.hMul.{0, 0, 0} (13 / 3) Z)
      (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 (ImbalancedChen.Certificates.PairedV2.tUpper i))
        (ImbalancedChen.Certificates.PairedV2.uUpper j))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.E0Geometry.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i j : Nat) (Z : Rat),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
    (And (@LT.lt.{0} Nat instLTNat i (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))))
      (And (@LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))))
        (And
          (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            ImbalancedChen.Certificates.PairedV2.a)
          (And (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.a Z)
            (And
              (@Eq.{1} Rat Z
                (@Min.min.{0} Rat Rat.instInf (ImbalancedChen.Certificates.PairedV2.uLower j)
                  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                          (ImbalancedChen.Certificates.PairedV2.tUpper i))
                        (ImbalancedChen.Certificates.PairedV2.uUpper j)))
                    (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13))))))
              (And (@LE.le.{0} Rat Rat.instLE Z (ImbalancedChen.Certificates.PairedV2.uLower j))
                (And
                  (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.PairedV2.uLower j)
                    (ImbalancedChen.Certificates.PairedV2.uUpper j))
                  (And
                    (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedV2.uUpper j)
                      ImbalancedChen.Certificates.PairedV2.h)
                    (And
                      (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.h
                        (ImbalancedChen.Certificates.PairedV2.tLower i))
                      (And
                        (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.PairedV2.tLower i)
                          (ImbalancedChen.Certificates.PairedV2.tUpper i))
                        (And
                          (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedV2.tUpper i)
                            ImbalancedChen.Certificates.PairedV2.d)
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
                                  (ImbalancedChen.Certificates.PairedV2.tLower i)))
                              (ImbalancedChen.Certificates.PairedV2.uLower j))
                            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                              ImbalancedChen.Certificates.PairedV2.a)))))))))))))
```

### 完整可读类型

```lean
∀ (i j : ℕ) (Z : ℚ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
    (LT.lt.{0} i 512 ∧
      LT.lt.{0} j 512 ∧
        LT.lt.{0} 0 ImbalancedChen.Certificates.PairedV2.a ∧
          LT.lt.{0} ImbalancedChen.Certificates.PairedV2.a Z ∧
            Eq.{1} Z
                (Min.min.{0} (ImbalancedChen.Certificates.PairedV2.uLower j)
                  (HDiv.hDiv.{0, 0, 0}
                    (HMul.hMul.{0, 0, 0} 3
                      (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 (ImbalancedChen.Certificates.PairedV2.tUpper i))
                        (ImbalancedChen.Certificates.PairedV2.uUpper j)))
                    13)) ∧
              LE.le.{0} Z (ImbalancedChen.Certificates.PairedV2.uLower j) ∧
                LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.uLower j)
                    (ImbalancedChen.Certificates.PairedV2.uUpper j) ∧
                  LE.le.{0} (ImbalancedChen.Certificates.PairedV2.uUpper j) ImbalancedChen.Certificates.PairedV2.h ∧
                    LT.lt.{0} ImbalancedChen.Certificates.PairedV2.h (ImbalancedChen.Certificates.PairedV2.tLower i) ∧
                      LT.lt.{0} (ImbalancedChen.Certificates.PairedV2.tLower i)
                          (ImbalancedChen.Certificates.PairedV2.tUpper i) ∧
                        LE.le.{0} (ImbalancedChen.Certificates.PairedV2.tUpper i)
                            ImbalancedChen.Certificates.PairedV2.d ∧
                          LE.le.{0}
                            (HSub.hSub.{0, 0, 0}
                              (HSub.hSub.{0, 0, 0} (57 / 64)
                                (HMul.hMul.{0, 0, 0} (5 / 2) (ImbalancedChen.Certificates.PairedV2.tLower i)))
                              (ImbalancedChen.Certificates.PairedV2.uLower j))
                            (HMul.hMul.{0, 0, 0} 2 ImbalancedChen.Certificates.PairedV2.a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_argument

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z) {t u z w : Real}
  (hs : ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
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

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z →
    ∀ {t u z w : ℝ},
      ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w →
        LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.a) w ∧
          LT.lt.{0} w z ∧
            LT.lt.{0} z u ∧
              LT.lt.{0} u ↑ImbalancedChen.Certificates.PairedV2.h ∧
                LT.lt.{0} (↑ImbalancedChen.Certificates.PairedV2.h) t ∧
                  LT.lt.{0} t ↑ImbalancedChen.Certificates.PairedV2.d ∧
                    LE.le.{0} (7 / 3)
                      (HDiv.hDiv.{0, 0, 0}
                        (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} 1 t) u) z)
                          w)
                        z)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_nonempty

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z),
  @Exists.{1} Real fun (t : Real) =>
    @Exists.{1} Real fun (u : Real) =>
      @Exists.{1} Real fun (z : Real) =>
        @Exists.{1} Real fun (w : Real) => ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w
```

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z →
    ∃ t u z w, ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.E0Geometry.residual_bound

Module: `ImbalancedChen.Certificates.PairedV2Geometry`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z) {t u : Real}
  (ht :
    @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.tLower i)) t)
  (hu :
    @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.uLower j))
      u),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
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
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 5)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          t))
      u)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a))
```

### 完整可读类型

```lean
∀ {i j : ℕ} {Z : ℚ},
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z →
    ∀ {t u : ℝ},
      LE.le.{0} (↑(ImbalancedChen.Certificates.PairedV2.tLower i)) t →
        LE.le.{0} (↑(ImbalancedChen.Certificates.PairedV2.uLower j)) u →
          LE.le.{0} (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (57 / 64) (HMul.hMul.{0, 0, 0} (5 / 2) t)) u)
            (HMul.hMul.{0, 0, 0} 2 ↑ImbalancedChen.Certificates.PairedV2.a)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

### 完整可读类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

### 完整可读类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

### 完整可读类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

### 完整可读类型

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate_inputs

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  And
    (@Eq.{1} Rat
      (ImbalancedChen.Certificates.PairedIntegralCertificate.K
        (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
      ImbalancedChen.Certificates.PairedV2.K)
    (And
      (@Eq.{1} Rat
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
        ImbalancedChen.Certificates.PairedV2.a)
      (And
        (@Eq.{1} Rat
          (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
            (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (And
          (@Eq.{1} Rat
            (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
              (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
            (ImbalancedChen.Certificates.PairedV2.tUpper
              (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
          (And
            (@Eq.{1} Rat
              (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
                (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (And
              (@Eq.{1} Rat
                (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
                  (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
                (ImbalancedChen.Certificates.PairedV2.uUpper
                  (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
              (@Eq.{1} Rat
                (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
                  (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
                (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)))))))
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).K ImbalancedChen.Certificates.PairedV2.K ∧
    Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).a ImbalancedChen.Certificates.PairedV2.a ∧
      Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tl
          (ImbalancedChen.Certificates.PairedV2.tLower (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1) ∧
        Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tr
            (ImbalancedChen.Certificates.PairedV2.tUpper
              (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1) ∧
          Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ul
              (ImbalancedChen.Certificates.PairedV2.uLower
                (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2) ∧
            Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ur
                (ImbalancedChen.Certificates.PairedV2.uUpper
                  (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2) ∧
              Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).Z
                (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
  ImbalancedChen.Certificates.PairedIntegralCertificate
```

### 完整可读类型

```lean
Fin 4 → ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Bool
    (ImbalancedChen.Certificates.PairedIntegralCertificate.check
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
    Bool.true
```

### 完整可读类型

```lean
∀ (i : Fin 4), Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).check Bool.true
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_argument

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) {t u z w : Real}
  (hs :
    ImbalancedChen.Certificates.PairedV2.openFibreSupport
      (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
      (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
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

### 完整可读类型

```lean
∀ (i : Fin 4) {t u z w : ℝ},
  ImbalancedChen.Certificates.PairedV2.openFibreSupport (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w →
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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_nonempty

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Exists.{1} Real fun (t : Real) =>
    @Exists.{1} Real fun (u : Real) =>
      @Exists.{1} Real fun (z : Real) =>
        @Exists.{1} Real fun (w : Real) =>
          ImbalancedChen.Certificates.PairedV2.openFibreSupport
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
            (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
            (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  ∃ t u z w,
    ImbalancedChen.Certificates.PairedV2.openFibreSupport (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.geometry_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  ImbalancedChen.Certificates.PairedV2.E0Geometry
    (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
    (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  ImbalancedChen.Certificates.PairedV2.E0Geometry (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2 (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `definition`

### 完整 pp.all 类型

```lean
Real
```

### 完整可读类型

```lean
ℝ
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix4.integral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.Prefix4.integral
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound))
```

### 完整可读类型

```lean
LE.le.{0} (↑ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix4.integral ∧
  LE.le.{0} ImbalancedChen.Certificates.PairedV2.Prefix4.integral
    ↑ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_pos

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ImbalancedChen.Certificates.PairedV2.Prefix4.integral
```

### 完整可读类型

```lean
LT.lt.{0} 0 ImbalancedChen.Certificates.PairedV2.Prefix4.integral
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_semantics

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real.instAddCommMonoid
      (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
      @intervalIntegral.{0} Real Real.normedAddCommGroup
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
                    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a)
                (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uUpper
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tUpper
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑ImbalancedChen.Certificates.PairedV2.K) 80)
    (∑ i,
      ∫ (t : ℝ) in
        ↑(ImbalancedChen.Certificates.PairedV2.tLower
            (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices
                i).1)..↑(ImbalancedChen.Certificates.PairedV2.tUpper
            (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1),
        ∫ (u : ℝ) in
          ↑(ImbalancedChen.Certificates.PairedV2.uLower
              (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices
                  i).2)..↑(ImbalancedChen.Certificates.PairedV2.uUpper
              (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2),
          ∫ (z : ℝ) in ↑ImbalancedChen.Certificates.PairedV2.a..↑(ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i),
            ∫ (w : ℝ) in ↑ImbalancedChen.Certificates.PairedV2.a..z,
              HDiv.hDiv.{0, 0, 0} 1
                (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t u) (HPow.hPow.{0, 0, 0} z 2)) w)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
Rat
```

### 完整可读类型

```lean
ℚ
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.lower_sum

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Rat
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Rat Rat.addCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedIntegralCertificate.lower
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
  ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
```

### 完整可读类型

```lean
Eq.{1} (∑ i, (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).lower)
  ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0000_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000)
  Bool.true
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000.check Bool.true
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0001_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001)
  Bool.true
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001.check Bool.true
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0002_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002)
  Bool.true
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002.check Bool.true
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0003_checked

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003)
  Bool.true
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003.check Bool.true
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Prod.{0, 0} Nat Nat
```

### 完整可读类型

```lean
Fin 4 → Prod.{0, 0} ℕ ℕ
```

传递公理：。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `definition`

### 完整 pp.all 类型

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Real
```

### 完整可读类型

```lean
Fin 4 → ℝ
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral_eq_certificate

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))))
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).K
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).a
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tl
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tr
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ul
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ur
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).Z)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Nat
```

### 完整可读类型

```lean
Fin 4 → ℕ
```

传递公理：。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Rat
```

### 完整可读类型

```lean
Fin 4 → ℚ
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
Rat
```

### 完整可读类型

```lean
ℚ
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.upper_sum

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Rat
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Rat Rat.addCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedIntegralCertificate.upper
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
  ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
```

### 完整可读类型

```lean
Eq.{1} (∑ i, (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).upper)
  ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
      (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1874722) (@Rat.instOfNat (nat_lit 1874722))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191204489) (@Rat.instOfNat (nat_lit 347191204489)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191214953) (@Rat.instOfNat (nat_lit 347191214953)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 176528638941) (@Rat.instOfNat (nat_lit 176528638941)))
        (@OfNat.ofNat.{0} Rat (nat_lit 200000000000000) (@Rat.instOfNat (nat_lit 200000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 882643366613) (@Rat.instOfNat (nat_lit 882643366613)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 25362703) (@Rat.instOfNat (nat_lit 25362703)))
        (@OfNat.ofNat.{0} Rat (nat_lit 14802944) (@Rat.instOfNat (nat_lit 14802944))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453624463727) (@Rat.instOfNat (nat_lit 538453624463727)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453686055971) (@Rat.instOfNat (nat_lit 538453686055971)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 634063221377) (@Rat.instOfNat (nat_lit 634063221377)))
      (@OfNat.ofNat.{0} Rat (nat_lit 20000000000000000000) (@Rat.instOfNat (nat_lit 20000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 3170317936341) (@Rat.instOfNat (nat_lit 3170317936341)))
      (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000)))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000
  { K := ImbalancedChen.Certificates.PairedV2.K, a := ImbalancedChen.Certificates.PairedV2.a,
    tl := ImbalancedChen.Certificates.PairedV2.tLower 422, tr := ImbalancedChen.Certificates.PairedV2.tUpper 422,
    ul := ImbalancedChen.Certificates.PairedV2.uLower 510, ur := ImbalancedChen.Certificates.PairedV2.uUpper 510,
    Z := 76088109 / 532480000,
    logT :=
      { argument := 1875373 / 1874722, terms := 1, lower := 347191204489 / 1000000000000000,
        upper := 347191214953 / 1000000000000000 },
    logU :=
      { argument := 388777 / 388434, terms := 1, lower := 176528638941 / 200000000000000,
        upper := 882643366613 / 1000000000000000 },
    logZ :=
      { argument := 25362703 / 14802944, terms := 6, lower := 538453624463727 / 1000000000000000,
        upper := 538453686055971 / 1000000000000000 },
    lower := 634063221377 / 20000000000000000000, upper := 3170317936341 / 100000000000000000000 }
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1170333) (@Rat.instOfNat (nat_lit 1170333)))
      (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1874722) (@Rat.instOfNat (nat_lit 1874722))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191204489) (@Rat.instOfNat (nat_lit 347191204489)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191214953) (@Rat.instOfNat (nat_lit 347191214953)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 389120) (@Rat.instOfNat (nat_lit 389120)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 2755827571) (@Rat.instOfNat (nat_lit 2755827571)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3125000000000) (@Rat.instOfNat (nat_lit 3125000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 35274599767) (@Rat.instOfNat (nat_lit 35274599767)))
        (@OfNat.ofNat.{0} Rat (nat_lit 40000000000000) (@Rat.instOfNat (nat_lit 40000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1950555) (@Rat.instOfNat (nat_lit 1950555)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1138688) (@Rat.instOfNat (nat_lit 1138688))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538237220351071) (@Rat.instOfNat (nat_lit 538237220351071)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 134559320408441) (@Rat.instOfNat (nat_lit 134559320408441)))
        (@OfNat.ofNat.{0} Rat (nat_lit 250000000000000) (@Rat.instOfNat (nat_lit 250000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1582705120377) (@Rat.instOfNat (nat_lit 1582705120377)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 126616482467) (@Rat.instOfNat (nat_lit 126616482467)))
      (@OfNat.ofNat.{0} Rat (nat_lit 4000000000000000000) (@Rat.instOfNat (nat_lit 4000000000000000000)))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001
  { K := ImbalancedChen.Certificates.PairedV2.K, a := ImbalancedChen.Certificates.PairedV2.a,
    tl := ImbalancedChen.Certificates.PairedV2.tLower 422, tr := ImbalancedChen.Certificates.PairedV2.tUpper 422,
    ul := ImbalancedChen.Certificates.PairedV2.uLower 511, ur := ImbalancedChen.Certificates.PairedV2.uUpper 511,
    Z := 1170333 / 8192000,
    logT :=
      { argument := 1875373 / 1874722, terms := 1, lower := 347191204489 / 1000000000000000,
        upper := 347191214953 / 1000000000000000 },
    logU :=
      { argument := 389120 / 388777, terms := 1, lower := 2755827571 / 3125000000000,
        upper := 35274599767 / 40000000000000 },
    logZ :=
      { argument := 1950555 / 1138688, terms := 6, lower := 538237220351071 / 1000000000000000,
        upper := 134559320408441 / 250000000000000 },
    lower := 1582705120377 / 50000000000000000000, upper := 126616482467 / 4000000000000000000 }
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 9511851) (@Rat.instOfNat (nat_lit 9511851)))
      (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1876024) (@Rat.instOfNat (nat_lit 1876024)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347070704593) (@Rat.instOfNat (nat_lit 347070704593)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 173535357523) (@Rat.instOfNat (nat_lit 173535357523)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388091) (@Rat.instOfNat (nat_lit 388091))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3450870867) (@Rat.instOfNat (nat_lit 3450870867)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3906250000000) (@Rat.instOfNat (nat_lit 3906250000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 883423114317) (@Rat.instOfNat (nat_lit 883423114317)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3170617) (@Rat.instOfNat (nat_lit 3170617)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1850368) (@Rat.instOfNat (nat_lit 1850368))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 26927083162251) (@Rat.instOfNat (nat_lit 26927083162251)))
        (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000) (@Rat.instOfNat (nat_lit 50000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 269270862481803) (@Rat.instOfNat (nat_lit 269270862481803)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1586437652383) (@Rat.instOfNat (nat_lit 1586437652383)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1586438569309) (@Rat.instOfNat (nat_lit 1586438569309)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000)))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002
  { K := ImbalancedChen.Certificates.PairedV2.K, a := ImbalancedChen.Certificates.PairedV2.a,
    tl := ImbalancedChen.Certificates.PairedV2.tLower 423, tr := ImbalancedChen.Certificates.PairedV2.tUpper 423,
    ul := ImbalancedChen.Certificates.PairedV2.uLower 509, ur := ImbalancedChen.Certificates.PairedV2.uUpper 509,
    Z := 9511851 / 66560000,
    logT :=
      { argument := 1876024 / 1875373, terms := 1, lower := 347070704593 / 1000000000000000,
        upper := 173535357523 / 500000000000000 },
    logU :=
      { argument := 388434 / 388091, terms := 1, lower := 3450870867 / 3906250000000,
        upper := 883423114317 / 1000000000000000 },
    logZ :=
      { argument := 3170617 / 1850368, terms := 6, lower := 26927083162251 / 50000000000000,
        upper := 269270862481803 / 500000000000000 },
    lower := 1586437652383 / 50000000000000000000, upper := 1586438569309 / 50000000000000000000 }
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 9509793) (@Rat.instOfNat (nat_lit 9509793)))
      (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1876024) (@Rat.instOfNat (nat_lit 1876024)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347070704593) (@Rat.instOfNat (nat_lit 347070704593)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 173535357523) (@Rat.instOfNat (nat_lit 173535357523)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 176528638941) (@Rat.instOfNat (nat_lit 176528638941)))
        (@OfNat.ofNat.{0} Rat (nat_lit 200000000000000) (@Rat.instOfNat (nat_lit 200000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 882643366613) (@Rat.instOfNat (nat_lit 882643366613)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3169931) (@Rat.instOfNat (nat_lit 3169931)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1850368) (@Rat.instOfNat (nat_lit 1850368))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 134581319546397) (@Rat.instOfNat (nat_lit 134581319546397)))
        (@OfNat.ofNat.{0} Rat (nat_lit 250000000000000) (@Rat.instOfNat (nat_lit 250000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538325339594069) (@Rat.instOfNat (nat_lit 538325339594069)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1583981804581) (@Rat.instOfNat (nat_lit 1583981804581)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 3167965434447) (@Rat.instOfNat (nat_lit 3167965434447)))
      (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000)))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003
  { K := ImbalancedChen.Certificates.PairedV2.K, a := ImbalancedChen.Certificates.PairedV2.a,
    tl := ImbalancedChen.Certificates.PairedV2.tLower 423, tr := ImbalancedChen.Certificates.PairedV2.tUpper 423,
    ul := ImbalancedChen.Certificates.PairedV2.uLower 510, ur := ImbalancedChen.Certificates.PairedV2.uUpper 510,
    Z := 9509793 / 66560000,
    logT :=
      { argument := 1876024 / 1875373, terms := 1, lower := 347070704593 / 1000000000000000,
        upper := 173535357523 / 500000000000000 },
    logU :=
      { argument := 388777 / 388434, terms := 1, lower := 176528638941 / 200000000000000,
        upper := 882643366613 / 1000000000000000 },
    logZ :=
      { argument := 3169931 / 1850368, terms := 6, lower := 134581319546397 / 250000000000000,
        upper := 538325339594069 / 1000000000000000 },
    lower := 1583981804581 / 50000000000000000000, upper := 3167965434447 / 100000000000000000000 }
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
    (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1}
      (fun (x : Nat) => ImbalancedChen.Certificates.PairedIntegralCertificate)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002) fun (x : Nat) =>
      ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003)
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)
    (match ↑i with
    | 0 => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000
    | 1 => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001
    | 2 => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002
    | x => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real.instAddCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (∑ i, ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds._simp_1_2

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1}
    (ImbalancedChen.Certificates.pairedLocalIntegral ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).K
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).a
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tl
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).tr
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ul
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).ur
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i).Z)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 12676565261567) (@Rat.instOfNat (nat_lit 12676565261567)))
    (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound (12676565261567 / 100000000000000000000)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} (Prod.{0, 0} Nat Nat) (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1} (fun (x : Nat) => Prod.{0, 0} Nat Nat)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
          (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
          (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423)))
          (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
      fun (x : Nat) =>
      @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423)))
        (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i)
    (match ↑i with
    | 0 => Prod.mk.{0, 0} 422 510
    | 1 => Prod.mk.{0, 0} 422 511
    | 2 => Prod.mk.{0, 0} 423 509
    | x => Prod.mk.{0, 0} 423 510)
```

传递公理：。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4Data`; kind: `definition`

### 完整 pp.all 类型

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          (h_4 : (x : Nat) → motive x) → motive x
```

### 完整可读类型

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) → (Unit → motive 0) → (Unit → motive 1) → (Unit → motive 2) → ((x : ℕ) → motive x) → motive x
```

传递公理：。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a)
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.tLower
          (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.tUpper
          (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.uLower
          (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.uUpper
          (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)))
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral ↑ImbalancedChen.Certificates.PairedV2.K
      ↑ImbalancedChen.Certificates.PairedV2.a
      ↑(ImbalancedChen.Certificates.PairedV2.tLower (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1)
      ↑(ImbalancedChen.Certificates.PairedV2.tUpper (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).1)
      ↑(ImbalancedChen.Certificates.PairedV2.uLower (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2)
      ↑(ImbalancedChen.Certificates.PairedV2.uUpper (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i).2)
      ↑(ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1} (fun (x : Nat) => Rat)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
          (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 1170333) (@Rat.instOfNat (nat_lit 1170333)))
          (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000))))
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 9511851) (@Rat.instOfNat (nat_lit 9511851)))
          (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
      fun (x : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 9509793) (@Rat.instOfNat (nat_lit 9509793)))
        (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
```

### 完整可读类型

```lean
∀ (i : Fin 4),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
    (match ↑i with
    | 0 => 76088109 / 532480000
    | 1 => 1170333 / 8192000
    | 2 => 9511851 / 66560000
    | x => 9509793 / 66560000)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 12676572571081) (@Rat.instOfNat (nat_lit 12676572571081)))
    (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000))))
```

### 完整可读类型

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound (12676572571081 / 100000000000000000000)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_1

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h_1 h_2 h_3 h_4)
    (h_1 Unit.unit)
```

### 完整可读类型

```lean
∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit → motive 1) (h_3 : Unit → motive 2)
  (h_4 : (x : ℕ) → motive x),
  Eq.{u_1}
    (match 0 with
    | 0 => h_1 ()
    | 1 => h_2 ()
    | 2 => h_3 ()
    | x => h_4 x)
    (h_1 ())
```

传递公理：。

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_2

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h_1 h_2 h_3 h_4)
    (h_2 Unit.unit)
```

### 完整可读类型

```lean
∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit → motive 1) (h_3 : Unit → motive 2)
  (h_4 : (x : ℕ) → motive x),
  Eq.{u_1}
    (match 1 with
    | 0 => h_1 ()
    | 1 => h_2 ()
    | 2 => h_3 ()
    | x => h_4 x)
    (h_2 ())
```

传递公理：。

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_3

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h_1 h_2 h_3 h_4)
    (h_3 Unit.unit)
```

### 完整可读类型

```lean
∀ (motive : ℕ → Sort u_1) (h_1 : Unit → motive 0) (h_2 : Unit → motive 1) (h_3 : Unit → motive 2)
  (h_4 : (x : ℕ) → motive x),
  Eq.{u_1}
    (match 2 with
    | 0 => h_1 ()
    | 1 => h_2 ()
    | 2 => h_3 ()
    | x => h_4 x)
    (h_3 ())
```

传递公理：。

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_4

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `theorem`

### 完整 pp.all 类型

```lean
∀ (motive : Nat → Sort u_1) (x : Nat)
  (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → False) →
    (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → False) →
      (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → False) →
        @Eq.{u_1} (motive x)
          (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive x h_1 h_2 h_3 h_4) (h_4 x)
```

### 完整可读类型

```lean
∀ (motive : ℕ → Sort u_1) (x : ℕ) (h_1 : Unit → motive 0) (h_2 : Unit → motive 1) (h_3 : Unit → motive 2)
  (h_4 : (x : ℕ) → motive x),
  (Eq.{1} x 0 → False) →
    (Eq.{1} x 1 → False) →
      (Eq.{1} x 2 → False) →
        Eq.{u_1}
          (match x with
          | 0 => h_1 ()
          | 1 => h_2 ()
          | 2 => h_3 ()
          | x => h_4 x)
          (h_4 x)
```

传递公理：。

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.splitter

Module: `ImbalancedChen.Certificates.PairedV2Prefix4`; kind: `definition`

### 完整 pp.all 类型

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          (h_4 :
              (x : Nat) →
                (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → False) →
                  (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → False) →
                    (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → False) → motive x) →
            motive x
```

### 完整可读类型

```lean
(motive : ℕ → Sort u_1) →
  (x : ℕ) →
    (Unit → motive 0) →
      (Unit → motive 1) →
        (Unit → motive 2) →
          ((x : ℕ) → (Eq.{1} x 0 → False) → (Eq.{1} x 1 → False) → (Eq.{1} x 2 → False) → motive x) → motive x
```

传递公理：。
