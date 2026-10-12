# 完成审计中打印的编译器类型

仅包含绑定当前源或明确沿用已验证同源历史回执的完整审计结果。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k u v : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator_pos`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_eq_literal`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_lower_of_denominatorCap`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_gates`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_mem_physicalDomain`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k u v : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel_eq_physical_pullback`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(u : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX_eq`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k u v : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY_eq`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_bounds`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_factors_pos`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.continuousOn_chartKernel`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(t : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartX`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartY`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.mu`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_upper_bounds`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_denominator_le`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k u v : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual_semantics`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(k u v : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual_semantics`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Set.{0} (Prod.{0, 0} ℝ ℝ)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Set.{0} (Prod.{0, 0} Real Real)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_upper_bounds`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_denominator_le`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.rho`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(ℝ → ℝ → ℝ) → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(f : Real → Real → Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_weightedMass`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.step`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.step_eq`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`definition`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_ge_mu`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_le_mu`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_eq_setIntegral`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_mono`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (k u v : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (k : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (k : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 5 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (k u v : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
    (HDiv.hDiv.{0, 0, 0}
      (HMul.hMul.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 6 (abs.{0} k))
            (HPow.hPow.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.step 3))
          (HPow.hPow.{0, 0, 0} u 2))
        (HSub.hSub.{0, 0, 0} 1 v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel._proof_1))
              (@abs.{0} Real Real.lattice Real.instAddGroup k))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              ImbalancedChen.Certificates.AboveMuSecondCoarse.step
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 74 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 1 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_2`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 56 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_3`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 63 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_4`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 24 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_2`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 127 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.mu.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.mu (25 / 128)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 25)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 25) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 128)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_2)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 23 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
  (HMul.hMul.{0, 0, 0}
    (HMul.hMul.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
    (HPow.hPow.{0, 0, 0} (5 / 24) 2))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_2))
        (@OfNat.ofNat.{0} Real (nat_lit 24)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap._proof_1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 158 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_2`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 4 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_3`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 767 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 767) (instOfNatNat (nat_lit 767)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 31 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 52 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_2`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 255 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
  (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho 2)
    (HPow.hPow.{0, 0, 0} (53 / 256) 2))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      ImbalancedChen.Certificates.AboveMuSecondCoarse.rho (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_1))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 18 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_2`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 95 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 95) (instOfNatNat (nat_lit 95)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.rho.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.rho (19 / 96)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 19)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 96)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 96) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_2)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (f : ℝ → ℝ → ℝ),
  Eq.{1} (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f) (∫ (u : ℝ) (v : ℝ) in 0..1, f u v)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (f : Real → Real → Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (u : Real) =>
        @intervalIntegral.{0} Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (fun (v : Real) => f u v) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.step._proof_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 383 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 383) (instOfNatNat (nat_lit 383)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.AboveMuSecondCoarse.step.eq_1`

定义模块：`ImbalancedChen.Certificates.AboveMuSecondCoarse`；kind：`theorem`；源码 SHA256：`85fdde51712d86400c19e3175b8f5f4aebe7efeadd7c2b9357fea0bc5a8759c2`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.AboveMuSecondCoarse.step (1 / 384)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.step
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
    (@OfNat.ofNat.{0} Real (nat_lit 384)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 384) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.step._proof_1)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`inductive`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Type
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Type
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
DecidableEq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
DecidableEq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableValid_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Decidable c.Valid
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) →
  Decidable (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.instReprPairedIntegralCertificate`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Repr.{0} ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Repr.{0} ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.K`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.Valid`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Prop
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Prop
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.Z`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_inst`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
SizeOf.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
SizeOf.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.a`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.casesOn`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    ((K a tl tr ul ur Z : ℚ) →
        (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
          (lower upper : ℚ) →
            motive
              { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU,
                logZ := logZ, lower := lower, upper := upper }) →
      motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (mk :
        (K a tl tr ul ur Z : Rat) →
          (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
            (lower upper : Rat) →
              motive
                (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                  upper)) →
      motive t
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.check`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Bool
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Bool
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.ctorIdx`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.logT`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.logU`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.logZ`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.lower`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`constructor`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ →
  ℚ →
    ℚ →
      ℚ →
        ℚ →
          ℚ →
            ℚ →
              ImbalancedChen.Certificates.RationalLogCertificate →
                ImbalancedChen.Certificates.RationalLogCertificate →
                  ImbalancedChen.Certificates.RationalLogCertificate →
                    ℚ → ℚ → ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(K a tl tr ul ur Z : Rat) →
  (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
    (lower upper : Rat) → ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusion`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.PairedIntegralCertificate} →
    Eq.{1} t t' → ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusionType.{u} P t t'
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.PairedIntegralCertificate} →
    (eq : @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate t t') →
      ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusionType.{u} P t t'
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusionType`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Sort u →
  ImbalancedChen.Certificates.PairedIntegralCertificate → ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(P : Sort u) → (t t' : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.productLower`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.rec`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`recursor`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u} →
  ((K a tl tr ul ur Z : ℚ) →
      (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
        (lower upper : ℚ) →
          motive
            { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU, logZ := logZ,
              lower := lower, upper := upper }) →
    (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (mk :
      (K a tl tr ul ur Z : Rat) →
        (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
          (lower upper : Rat) →
            motive
              (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)) →
    (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → motive t
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.recOn`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    ((K a tl tr ul ur Z : ℚ) →
        (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
          (lower upper : ℚ) →
            motive
              { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU,
                logZ := logZ, lower := lower, upper := upper }) →
      motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (mk :
        (K a tl tr ul ur Z : Rat) →
          (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
            (lower upper : Rat) →
              motive
                (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                  upper)) →
      motive t
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.sum_check_sound`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.tl`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.tr`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.ul`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.upper`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.ur`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) → Decidable (Eq.{1} x x_1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) →
  Decidable (@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate x x_1)
```

传递公理：。

## `ImbalancedChen.Certificates.instReprPairedIntegralCertificate.repr`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → ℕ → Std.Format
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Nat → Std.Format
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.bracketLower
    (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 c.a) (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 c.logZ.upper) c.Z))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.bracketUpper
    (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 c.a) (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 c.logZ.lower) c.Z))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper c)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (ImbalancedChen.Certificates.RationalLogCertificate.lower
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk._flat_ctor`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ →
  ℚ →
    ℚ →
      ℚ →
        ℚ →
          ℚ →
            ℚ →
              ImbalancedChen.Certificates.RationalLogCertificate →
                ImbalancedChen.Certificates.RationalLogCertificate →
                  ImbalancedChen.Certificates.RationalLogCertificate →
                    ℚ → ℚ → ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(K a tl tr ul ur Z : Rat) →
  (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
    (lower upper : Rat) → ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk.inj`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {K a tl tr ul ur Z : ℚ} {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate}
  {lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : ℚ}
  {logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate} {lower_1 upper_1 : ℚ},
  Eq.{1}
      { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU, logZ := logZ,
        lower := lower, upper := upper }
      { K := K_1, a := a_1, tl := tl_1, tr := tr_1, ul := ul_1, ur := ur_1, Z := Z_1, logT := logT_1, logU := logU_1,
        logZ := logZ_1, lower := lower_1, upper := upper_1 } →
    Eq.{1} K K_1 ∧
      Eq.{1} a a_1 ∧
        Eq.{1} tl tl_1 ∧
          Eq.{1} tr tr_1 ∧
            Eq.{1} ul ul_1 ∧
              Eq.{1} ur ur_1 ∧
                Eq.{1} Z Z_1 ∧
                  Eq.{1} logT logT_1 ∧
                    Eq.{1} logU logU_1 ∧ Eq.{1} logZ logZ_1 ∧ Eq.{1} lower lower_1 ∧ Eq.{1} upper upper_1
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {K a tl tr ul ur Z : Rat} {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate}
  {lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : Rat}
  {logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate} {lower_1 upper_1 : Rat},
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 logT_1 logU_1 logZ_1
        lower_1 upper_1) →
    And (@Eq.{1} Rat K K_1)
      (And (@Eq.{1} Rat a a_1)
        (And (@Eq.{1} Rat tl tl_1)
          (And (@Eq.{1} Rat tr tr_1)
            (And (@Eq.{1} Rat ul ul_1)
              (And (@Eq.{1} Rat ur ur_1)
                (And (@Eq.{1} Rat Z Z_1)
                  (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT_1)
                    (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU_1)
                      (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ_1)
                        (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1)))))))))))
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk.injEq`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (K a tl tr ul ur Z : ℚ) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate)
  (lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : ℚ)
  (logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate) (lower_1 upper_1 : ℚ),
  Eq.{1}
    (Eq.{1}
      { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU, logZ := logZ,
        lower := lower, upper := upper }
      { K := K_1, a := a_1, tl := tl_1, tr := tr_1, ul := ul_1, ur := ur_1, Z := Z_1, logT := logT_1, logU := logU_1,
        logZ := logZ_1, lower := lower_1, upper := upper_1 })
    (Eq.{1} K K_1 ∧
      Eq.{1} a a_1 ∧
        Eq.{1} tl tl_1 ∧
          Eq.{1} tr tr_1 ∧
            Eq.{1} ul ul_1 ∧
              Eq.{1} ur ur_1 ∧
                Eq.{1} Z Z_1 ∧
                  Eq.{1} logT logT_1 ∧
                    Eq.{1} logU logU_1 ∧ Eq.{1} logZ logZ_1 ∧ Eq.{1} lower lower_1 ∧ Eq.{1} upper upper_1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (K a tl tr ul ur Z : Rat) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate)
  (lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : Rat)
  (logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate) (lower_1 upper_1 : Rat),
  @Eq.{1} Prop
    (@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 logT_1 logU_1 logZ_1
        lower_1 upper_1))
    (And (@Eq.{1} Rat K K_1)
      (And (@Eq.{1} Rat a a_1)
        (And (@Eq.{1} Rat tl tl_1)
          (And (@Eq.{1} Rat tr tr_1)
            (And (@Eq.{1} Rat ul ul_1)
              (And (@Eq.{1} Rat ur ur_1)
                (And (@Eq.{1} Rat Z Z_1)
                  (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT_1)
                    (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU_1)
                      (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ_1)
                        (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1))))))))))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk.noConfusion`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{P : Sort u} →
  {K a tl tr ul ur Z : ℚ} →
    {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate} →
      {lower upper K' a' tl' tr' ul' ur' Z' : ℚ} →
        {logT' logU' logZ' : ImbalancedChen.Certificates.RationalLogCertificate} →
          {lower' upper' : ℚ} →
            Eq.{1}
                { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU,
                  logZ := logZ, lower := lower, upper := upper }
                { K := K', a := a', tl := tl', tr := tr', ul := ul', ur := ur', Z := Z', logT := logT', logU := logU',
                  logZ := logZ', lower := lower', upper := upper' } →
              (Eq.{1} K K' →
                  Eq.{1} a a' →
                    Eq.{1} tl tl' →
                      Eq.{1} tr tr' →
                        Eq.{1} ul ul' →
                          Eq.{1} ur ur' →
                            Eq.{1} Z Z' →
                              Eq.{1} logT logT' →
                                Eq.{1} logU logU' → Eq.{1} logZ logZ' → Eq.{1} lower lower' → Eq.{1} upper upper' → P) →
                P
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{P : Sort u} →
  {K a tl tr ul ur Z : Rat} →
    {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate} →
      {lower upper K' a' tl' tr' ul' ur' Z' : Rat} →
        {logT' logU' logZ' : ImbalancedChen.Certificates.RationalLogCertificate} →
          {lower' upper' : Rat} →
            (eq :
                @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                    upper)
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K' a' tl' tr' ul' ur' Z' logT' logU' logZ'
                    lower' upper')) →
              (k :
                  (K_eq : @Eq.{1} Rat K K') →
                    (a_eq : @Eq.{1} Rat a a') →
                      (tl_eq : @Eq.{1} Rat tl tl') →
                        (tr_eq : @Eq.{1} Rat tr tr') →
                          (ul_eq : @Eq.{1} Rat ul ul') →
                            (ur_eq : @Eq.{1} Rat ur ur') →
                              (Z_eq : @Eq.{1} Rat Z Z') →
                                (logT_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT') →
                                  (logU_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU') →
                                    (logZ_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ') →
                                      (lower_eq : @Eq.{1} Rat lower lower') →
                                        (upper_eq : @Eq.{1} Rat upper upper') → P) →
                P
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.mk.sizeOf_spec`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (K a tl tr ul ur Z : ℚ) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) (lower upper : ℚ),
  Eq.{1}
    (SizeOf.sizeOf.{1}
      { K := K, a := a, tl := tl, tr := tr, ul := ul, ur := ur, Z := Z, logT := logT, logU := logU, logZ := logZ,
        lower := lower, upper := upper })
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HAdd.hAdd.{0, 0, 0}
                (HAdd.hAdd.{0, 0, 0}
                  (HAdd.hAdd.{0, 0, 0}
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{1} K)) (SizeOf.sizeOf.{1} a))
                        (SizeOf.sizeOf.{1} tl))
                      (SizeOf.sizeOf.{1} tr))
                    (SizeOf.sizeOf.{1} ul))
                  (SizeOf.sizeOf.{1} ur))
                (SizeOf.sizeOf.{1} Z))
              (SizeOf.sizeOf.{1} logT))
            (SizeOf.sizeOf.{1} logU))
          (SizeOf.sizeOf.{1} logZ))
        (SizeOf.sizeOf.{1} lower))
      (SizeOf.sizeOf.{1} upper))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (K a tl tr ul ur Z : Rat) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) (lower upper : Rat),
  @Eq.{1} Nat
    (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_inst
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst K))
                          (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst a))
                        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst tl))
                      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst tr))
                    (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst ul))
                  (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst ur))
                (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst Z))
              (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
                ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logT))
            (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
              ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logU))
          (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
            ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logZ))
        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst lower))
      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst upper))
```

传递公理：。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.productLower.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.productLower
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} c.K 80) c.logT.lower) c.logU.lower) c.bracketLower)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.productLower c)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.K c)
            (@OfNat.ofNat.{0} Rat (nat_lit 80) (@Rat.instOfNat (nat_lit 80))))
          (ImbalancedChen.Certificates.RationalLogCertificate.lower
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
        (ImbalancedChen.Certificates.RationalLogCertificate.lower
          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.productUpper
    (HMul.hMul.{0, 0, 0}
      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} c.K 80) c.logT.upper) c.logU.upper) c.bracketUpper)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper c)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.K c)
            (@OfNat.ofNat.{0} Rat (nat_lit 80) (@Rat.instOfNat (nat_lit 80))))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
        (ImbalancedChen.Certificates.RationalLogCertificate.upper
          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper c))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : ℚ),
  Eq.{1}
    { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
      lower := a_10, upper := a_11 }
    { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
      lower := a_10, upper := a_11 }
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 : Rat),
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_10`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 : ℚ) (b_4 b_5 b_6 : ImbalancedChen.Certificates.RationalLogCertificate) (b_7 b_8 : ℚ),
  ¬Eq.{1} a_3 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := b, ul := b_1, ur := b_2, Z := b_3, logT := b_4, logU := b_5, logZ := b_6,
          lower := b_7, upper := b_8 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 : Rat) (b_4 b_5 b_6 : ImbalancedChen.Certificates.RationalLogCertificate) (b_7 b_8 : Rat),
  Not (@Eq.{1} Rat a_3 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_11`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 : ℚ) (b_5 b_6 b_7 : ImbalancedChen.Certificates.RationalLogCertificate) (b_8 b_9 : ℚ),
  ¬Eq.{1} a_2 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := b, tr := b_1, ul := b_2, ur := b_3, Z := b_4, logT := b_5, logU := b_6, logZ := b_7,
          lower := b_8, upper := b_9 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 : Rat) (b_5 b_6 b_7 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_8 b_9 : Rat),
  Not (@Eq.{1} Rat a_2 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_12`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 : ℚ) (b_6 b_7 b_8 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_9 b_10 : ℚ),
  ¬Eq.{1} a_1 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := b, tl := b_1, tr := b_2, ul := b_3, ur := b_4, Z := b_5, logT := b_6, logU := b_7, logZ := b_8,
          lower := b_9, upper := b_10 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 : Rat) (b_6 b_7 b_8 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_9 b_10 : Rat),
  Not (@Eq.{1} Rat a_1 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_13`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : ℚ) (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_10 b_11 : ℚ),
  ¬Eq.{1} a b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := b, a := b_1, tl := b_2, tr := b_3, ul := b_4, ur := b_5, Z := b_6, logT := b_7, logU := b_8, logZ := b_9,
          lower := b_10, upper := b_11 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : Rat) (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_10 b_11 : Rat),
  Not (@Eq.{1} Rat a b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_2`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 b : ℚ),
  ¬Eq.{1} a_11 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := b } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b : Rat),
  Not (@Eq.{1} Rat a_11 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 b) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_3`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : ℚ),
  ¬Eq.{1} a_10 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := b, upper := b_1 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : Rat),
  Not (@Eq.{1} Rat a_10 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 b b_1) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_4`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : ℚ)
  (b : ImbalancedChen.Certificates.RationalLogCertificate) (b_1 b_2 : ℚ),
  ¬Eq.{1} a_9 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := b,
          lower := b_1, upper := b_2 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b : ImbalancedChen.Certificates.RationalLogCertificate) (b_1 b_2 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_9 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 b b_1 b_2) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_5`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : ℚ)
  (b b_1 : ImbalancedChen.Certificates.RationalLogCertificate) (b_2 b_3 : ℚ),
  ¬Eq.{1} a_8 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := b, logZ := b_1,
          lower := b_2, upper := b_3 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b b_1 : ImbalancedChen.Certificates.RationalLogCertificate) (b_2 b_3 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_8 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 b b_1 b_2 b_3) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_6`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : ℚ)
  (b b_1 b_2 : ImbalancedChen.Certificates.RationalLogCertificate) (b_3 b_4 : ℚ),
  ¬Eq.{1} a_7 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := b, logU := b_1, logZ := b_2,
          lower := b_3, upper := b_4 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b b_1 b_2 : ImbalancedChen.Certificates.RationalLogCertificate) (b_3 b_4 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_7 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 b b_1 b_2 b_3 b_4) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_7`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 b : ℚ)
  (b_1 b_2 b_3 : ImbalancedChen.Certificates.RationalLogCertificate) (b_4 b_5 : ℚ),
  ¬Eq.{1} a_6 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := b, logT := b_1, logU := b_2, logZ := b_3,
          lower := b_4, upper := b_5 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b : Rat) (b_1 b_2 b_3 : ImbalancedChen.Certificates.RationalLogCertificate) (b_4 b_5 : Rat),
  Not (@Eq.{1} Rat a_6 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 b b_1 b_2 b_3 b_4 b_5) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_8`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : ℚ) (b_2 b_3 b_4 : ImbalancedChen.Certificates.RationalLogCertificate) (b_5 b_6 : ℚ),
  ¬Eq.{1} a_5 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := b, Z := b_1, logT := b_2, logU := b_3, logZ := b_4,
          lower := b_5, upper := b_6 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : Rat) (b_2 b_3 b_4 : ImbalancedChen.Certificates.RationalLogCertificate) (b_5 b_6 : Rat),
  Not (@Eq.{1} Rat a_5 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 b b_1 b_2 b_3 b_4 b_5 b_6) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_9`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`theorem`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 : ℚ) (b_3 b_4 b_5 : ImbalancedChen.Certificates.RationalLogCertificate) (b_6 b_7 : ℚ),
  ¬Eq.{1} a_4 b →
    Eq.{1}
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8, logZ := a_9,
          lower := a_10, upper := a_11 }
        { K := a, a := a_1, tl := a_2, tr := a_3, ul := b, ur := b_1, Z := b_2, logT := b_3, logU := b_4, logZ := b_5,
          lower := b_6, upper := b_7 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 : Rat) (b_3 b_4 b_5 : ImbalancedChen.Certificates.RationalLogCertificate) (b_6 b_7 : Rat),
  Not (@Eq.{1} Rat a_4 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 b b_1 b_2 b_3 b_4 b_5 b_6 b_7) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq.match_1`

定义模块：`ImbalancedChen.Certificates.PairedCertificateChecker`；kind：`definition`；源码 SHA256：`454c02ef9db5ea4f50deec917ff00809e5c27f0a480b2bf8f150f01e201d227c`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(motive :
    ImbalancedChen.Certificates.PairedIntegralCertificate →
      ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    ((a a_1 a_2 a_3 a_4 a_5 a_6 : ℚ) →
        (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
          (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : ℚ) →
            (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
              (b_10 b_11 : ℚ) →
                motive
                  { K := a, a := a_1, tl := a_2, tr := a_3, ul := a_4, ur := a_5, Z := a_6, logT := a_7, logU := a_8,
                    logZ := a_9, lower := a_10, upper := a_11 }
                  { K := b, a := b_1, tl := b_2, tr := b_3, ul := b_4, ur := b_5, Z := b_6, logT := b_7, logU := b_8,
                    logZ := b_9, lower := b_10, upper := b_11 }) →
      motive x x_1
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(motive :
    ImbalancedChen.Certificates.PairedIntegralCertificate →
      ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (h_1 :
        (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) →
          (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
            (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : Rat) →
              (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
                (b_10 b_11 : Rat) →
                  motive
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10
                      a_11)
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10
                      b_11)) →
      motive x x_1
```

传递公理：。

## `ImbalancedChen.Certificates.intervalIntegrable_pairedFibreKernel`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreIntegral`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`definition`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(a Z : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreIntegral_eq`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreIntegral_eq_iterated`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreKernel`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`definition`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(t u z w : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreKernel_eq`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedLocalIntegral`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`definition`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(K a tl tr ul ur Z : Real) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedLocalIntegral_eq`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedLocalIntegral_eq_literal`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.PairedFibreIntegral.0.ImbalancedChen.Certificates.hasDerivAt_pairedFibrePrimitive`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedFibreKernel.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (t u z w : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 t)
      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 u)
        (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} z 2)) (HDiv.hDiv.{0, 0, 0} 1 w))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (t u z w : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) w))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.pairedLocalIntegral._proof_1`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 79 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.pairedLocalIntegral.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedFibreIntegral`；kind：`theorem`；源码 SHA256：`d8bcdab8e5010d16827f5074db713243adc6a1cd686ab2b69bd3f9b4e41039a4`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (K a tl tr ul ur Z : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} K 80)
      (∫ (t : ℝ) in tl..tr,
        ∫ (u : ℝ) in ul..ur,
          ∫ (z : ℝ) in a..Z, ∫ (w : ℝ) in a..z, ImbalancedChen.Certificates.pairedFibreKernel t u z w))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (K a tl tr ul ur Z : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
        (@OfNat.ofNat.{0} Real (nat_lit 80)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
            ImbalancedChen.Certificates.pairedLocalIntegral._proof_1)))
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
                    (fun (w : Real) => ImbalancedChen.Certificates.pairedFibreKernel t u z w) a z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            ul ur (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        tl tr (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`definition`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ → ℝ → ℝ → ℝ → Prop
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(t u z w : Real) → Prop
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`definition`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral_pos`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
LT.lt.{0} 0 ImbalancedChen.Certificates.PairedV2.firstIntegral
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ImbalancedChen.Certificates.PairedV2.firstIntegral
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_certificate_checked`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_coordinates`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_cutoff_definition`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_fibre_argument`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_fibre_nonempty`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_geometry_checked`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.logParameter.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (q : ℚ),
  Eq.{1} (ImbalancedChen.Certificates.logParameter q)
    (HDiv.hDiv.{0, 0, 0} (HSub.hSub.{0, 0, 0} q 1) (HAdd.hAdd.{0, 0, 0} q 1))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (q : Rat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logParameter q)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) q
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) q
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.Valid.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  Eq.{1} c.Valid
    (LT.lt.{0} 0 c.K ∧
      LT.lt.{0} 0 c.a ∧
        LE.le.{0} c.a c.Z ∧
          LT.lt.{0} 0 c.tl ∧
            LE.le.{0} c.tl c.tr ∧
              LT.lt.{0} 0 c.ul ∧
                LE.le.{0} c.ul c.ur ∧
                  Eq.{1} c.logT.argument (HDiv.hDiv.{0, 0, 0} c.tr c.tl) ∧
                    Eq.{1} c.logU.argument (HDiv.hDiv.{0, 0, 0} c.ur c.ul) ∧
                      Eq.{1} c.logZ.argument (HDiv.hDiv.{0, 0, 0} c.Z c.a) ∧
                        Eq.{1} c.logT.check Bool.true ∧
                          Eq.{1} c.logU.check Bool.true ∧
                            Eq.{1} c.logZ.check Bool.true ∧
                              LE.le.{0} 0 c.logT.lower ∧
                                LE.le.{0} 0 c.logU.lower ∧
                                  LE.le.{0} 0 c.bracketLower ∧
                                    LE.le.{0} c.lower c.productLower ∧ LE.le.{0} c.productUpper c.upper)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
    (And
      (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
      (And
        (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (And
          (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.a c)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c))
          (And
            (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
            (And
              (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c)
                (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
              (And
                (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
                (And
                  (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c)
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
                  (And
                    (@Eq.{1} Rat
                      (ImbalancedChen.Certificates.RationalLogCertificate.argument
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c))
                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c)
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c)))
                    (And
                      (@Eq.{1} Rat
                        (ImbalancedChen.Certificates.RationalLogCertificate.argument
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c))
                        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c)
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c)))
                      (And
                        (@Eq.{1} Rat
                          (ImbalancedChen.Certificates.RationalLogCertificate.argument
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c))
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.a c)))
                        (And
                          (@Eq.{1} Bool
                            (ImbalancedChen.Certificates.RationalLogCertificate.check
                              (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c))
                            Bool.true)
                          (And
                            (@Eq.{1} Bool
                              (ImbalancedChen.Certificates.RationalLogCertificate.check
                                (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c))
                              Bool.true)
                            (And
                              (@Eq.{1} Bool
                                (ImbalancedChen.Certificates.RationalLogCertificate.check
                                  (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c))
                                Bool.true)
                              (And
                                (@LE.le.{0} Rat Rat.instLE
                                  (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                  (ImbalancedChen.Certificates.RationalLogCertificate.lower
                                    (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
                                (And
                                  (@LE.le.{0} Rat Rat.instLE
                                    (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                    (ImbalancedChen.Certificates.RationalLogCertificate.lower
                                      (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
                                  (And
                                    (@LE.le.{0} Rat Rat.instLE
                                      (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c))
                                    (And
                                      (@LE.le.{0} Rat Rat.instLE
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.lower c)
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.productLower c))
                                      (@LE.le.{0} Rat Rat.instLE
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper c)
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.upper
                                          c)))))))))))))))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedIntegralCertificate.check.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate), Eq.{1} c.check (Decidable.decide c.Valid)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check c)
    (@Decidable.decide (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
      (ImbalancedChen.Certificates.instDecidableValid_1 c))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.K.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.K (8452171 / 1250000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.K
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 8452171) (@Rat.instOfNat (nat_lit 8452171)))
    (@OfNat.ofNat.{0} Rat (nat_lit 1250000) (@Rat.instOfNat (nat_lit 1250000))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.a.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.a (417 / 5000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.a
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 417) (@Rat.instOfNat (nat_lit 417)))
    (@OfNat.ofNat.{0} Rat (nat_lit 5000) (@Rat.instOfNat (nat_lit 5000))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.d.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.d (59 / 250)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.d
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 59) (@Rat.instOfNat (nat_lit 59)))
    (@OfNat.ofNat.{0} Rat (nat_lit 250) (@Rat.instOfNat (nat_lit 250))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstCertificate.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstCertificate
  { K := ImbalancedChen.Certificates.PairedV2.K, a := ImbalancedChen.Certificates.PairedV2.a,
    tl := ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex,
    tr := ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex,
    ul := ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex,
    ur := ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex,
    Z := ImbalancedChen.Certificates.PairedV2.firstZ,
    logT :=
      { argument := 1875373 / 1874722, terms := 1, lower := 347191204489 / 1000000000000000,
        upper := 347191214953 / 1000000000000000 },
    logU :=
      { argument := 388777 / 388434, terms := 1, lower := 176528638941 / 200000000000000,
        upper := 882643366613 / 1000000000000000 },
    logZ :=
      { argument := 25362703 / 14802944, terms := 6, lower := 538453624463727 / 1000000000000000,
        upper := 538453686055971 / 1000000000000000 },
    lower := 31703 / 1000000000000, upper := 31704 / 1000000000000 }
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate ImbalancedChen.Certificates.PairedV2.firstCertificate
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
    (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
    ImbalancedChen.Certificates.PairedV2.firstZ
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
      (@OfNat.ofNat.{0} Rat (nat_lit 31703) (@Rat.instOfNat (nat_lit 31703)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000) (@Rat.instOfNat (nat_lit 1000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 31704) (@Rat.instOfNat (nat_lit 31704)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000) (@Rat.instOfNat (nat_lit 1000000000000)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80 0
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 937360 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 937360) (instOfNatNat (nat_lit 937360)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 4999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 76088108 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 76088108) (instOfNatNat (nat_lit 76088108)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 532479999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 532479999) (instOfNatNat (nat_lit 532479999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 4095999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4095999) (instOfNatNat (nat_lit 4095999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 1875372 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1875372) (instOfNatNat (nat_lit 1875372)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 8191999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8191999) (instOfNatNat (nat_lit 8191999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 194216 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 194216) (instOfNatNat (nat_lit 194216)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 1279999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1279999) (instOfNatNat (nat_lit 1279999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 388776 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 388776) (instOfNatNat (nat_lit 388776)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 2559999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2559999) (instOfNatNat (nat_lit 2559999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 416 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstFibreSupport.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (t u z w : ℝ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w)
    (LE.le.{0} (937361 / 4096000) t ∧
      LE.le.{0} t (1875373 / 8192000) ∧
        LE.le.{0} (194217 / 1280000) u ∧
          LE.le.{0} u (388777 / 2560000) ∧
            LT.lt.{0} (417 / 5000) w ∧ LT.lt.{0} w z ∧ LT.lt.{0} z (76088109 / 532480000))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (t u z w : Real),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w)
    (And
      (@LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 937361)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
              ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1))
          (@OfNat.ofNat.{0} Real (nat_lit 4096000)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
              ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2)))
        t)
      (And
        (@LE.le.{0} Real Real.instLE t
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1875373)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
                ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3))
            (@OfNat.ofNat.{0} Real (nat_lit 8192000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
                ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4))))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 194217)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
                  ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5))
              (@OfNat.ofNat.{0} Real (nat_lit 1280000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
                  ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6)))
            u)
          (And
            (@LE.le.{0} Real Real.instLE u
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 388777)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
                    ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7))
                (@OfNat.ofNat.{0} Real (nat_lit 2560000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
                    ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8))))
            (And
              (@LT.lt.{0} Real Real.instLT
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 417)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                      ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9))
                  (@OfNat.ofNat.{0} Real (nat_lit 5000)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                      ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10)))
                w)
              (And (@LT.lt.{0} Real Real.instLT w z)
                (@LT.lt.{0} Real Real.instLT z
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 76088109)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
                        ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11))
                    (@OfNat.ofNat.{0} Real (nat_lit 532480000)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
                        ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12))))))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 8452170 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8452170) (instOfNatNat (nat_lit 8452170)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_2`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 1249999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1249999) (instOfNatNat (nat_lit 1249999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.firstIntegral.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstIntegral
  (ImbalancedChen.Certificates.pairedLocalIntegral (8452171 / 1250000) (417 / 5000) (937361 / 4096000)
    (1875373 / 8192000) (194217 / 1280000) (388777 / 2560000) (76088109 / 532480000))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.firstIntegral
  (ImbalancedChen.Certificates.pairedLocalIntegral
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 8452171)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8452171) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_1))
      (@OfNat.ofNat.{0} Real (nat_lit 1250000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1250000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_2)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 417)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9))
      (@OfNat.ofNat.{0} Real (nat_lit 5000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 937361)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1))
      (@OfNat.ofNat.{0} Real (nat_lit 4096000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1875373)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3))
      (@OfNat.ofNat.{0} Real (nat_lit 8192000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 194217)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5))
      (@OfNat.ofNat.{0} Real (nat_lit 1280000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 388777)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7))
      (@OfNat.ofNat.{0} Real (nat_lit 2560000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 76088109)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11))
      (@OfNat.ofNat.{0} Real (nat_lit 532480000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstTIndex.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstTIndex 422
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstTIndex
  (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstUIndex.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstUIndex 510
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstUIndex
  (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstZ.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.firstZ (76088109 / 532480000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.firstZ
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
    (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.h.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.h (19 / 125)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.h
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 19) (@Rat.instOfNat (nat_lit 19)))
    (@OfNat.ofNat.{0} Rat (nat_lit 125) (@Rat.instOfNat (nat_lit 125))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.mu.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.Certificates.PairedV2.mu (25 / 128)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.mu
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 25) (@Rat.instOfNat (nat_lit 25)))
    (@OfNat.ofNat.{0} Rat (nat_lit 128) (@Rat.instOfNat (nat_lit 128))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.tLower.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (i : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.tLower i)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.mu
      (HDiv.hDiv.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.d ImbalancedChen.Certificates.PairedV2.mu) ↑i)
        512))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (i : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tLower i)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.mu
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.d
            ImbalancedChen.Certificates.PairedV2.mu)
          (@Nat.cast.{0} Rat Rat.instNatCast i))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.tUpper.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (i : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.tUpper i)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.mu
      (HDiv.hDiv.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.d ImbalancedChen.Certificates.PairedV2.mu)
          (HAdd.hAdd.{0, 0, 0} (↑i) 1))
        512))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (i : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tUpper i)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.mu
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.d
            ImbalancedChen.Certificates.PairedV2.mu)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (@Nat.cast.{0} Rat Rat.instNatCast i)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.uLower.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (j : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.uLower j)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.a
      (HDiv.hDiv.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.h ImbalancedChen.Certificates.PairedV2.a) ↑j)
        512))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (j : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uLower j)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.a
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.h
            ImbalancedChen.Certificates.PairedV2.a)
          (@Nat.cast.{0} Rat Rat.instNatCast j))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.uUpper.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (j : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.PairedV2.uUpper j)
    (HAdd.hAdd.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.a
      (HDiv.hDiv.{0, 0, 0}
        (HMul.hMul.{0, 0, 0}
          (HSub.hSub.{0, 0, 0} ImbalancedChen.Certificates.PairedV2.h ImbalancedChen.Certificates.PairedV2.a)
          (HAdd.hAdd.{0, 0, 0} (↑j) 1))
        512))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (j : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uUpper j)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.a
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.h
            ImbalancedChen.Certificates.PairedV2.a)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (@Nat.cast.{0} Rat Rat.instNatCast j)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate.Valid.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  Eq.{1} c.Valid
    (LE.le.{0} 1 c.argument ∧
      LE.le.{0} c.lower (ImbalancedChen.Certificates.logSeriesLower c.argument c.terms) ∧
        LE.le.{0} (ImbalancedChen.Certificates.logSeriesUpper c.argument c.terms) c.upper)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  @Eq.{1} Prop (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
    (And
      (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.RationalLogCertificate.argument c))
      (And
        (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.RationalLogCertificate.lower c)
          (ImbalancedChen.Certificates.logSeriesLower (ImbalancedChen.Certificates.RationalLogCertificate.argument c)
            (ImbalancedChen.Certificates.RationalLogCertificate.terms c)))
        (@LE.le.{0} Rat Rat.instLE
          (ImbalancedChen.Certificates.logSeriesUpper (ImbalancedChen.Certificates.RationalLogCertificate.argument c)
            (ImbalancedChen.Certificates.RationalLogCertificate.terms c))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper c))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate.check.eq_1`

定义模块：`ImbalancedChen.Certificates.PairedV2`；kind：`theorem`；源码 SHA256：`e8b6cdf4c1bbf9382c58b9002704183b3608f15e57f2d0837b5157f93d41eef7`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate), Eq.{1} c.check (Decidable.decide c.Valid)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  @Eq.{1} Bool (ImbalancedChen.Certificates.RationalLogCertificate.check c)
    (@Decidable.decide (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
      (ImbalancedChen.Certificates.instDecidableValid c))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.K`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.a`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.d`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstCertificate`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstGroup`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
String
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
String
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstOrdinal`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstStoredLowerQ160`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℤ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Int
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstStoredUpperQ160`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℤ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Int
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstTIndex`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstUIndex`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat
```

传递公理：。

## `ImbalancedChen.Certificates.PairedV2.firstZ`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.h`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.mu`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.tLower`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(i : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.tUpper`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(i : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.uLower`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(j : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.uUpper`

定义模块：`ImbalancedChen.Certificates.PairedV2Data`；kind：`definition`；源码 SHA256：`a9fa2f53e2adca9b61efdf0ed6992d22b79b7807d10f0921154795cee38faa82`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(j : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`inductive`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Type
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Type
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
DecidableEq.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
DecidableEq.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableValid`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) → Decidable c.Valid
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) →
  Decidable (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.instReprRationalLogCertificate`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Repr.{0} ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Repr.{0} ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.logParameter`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(q : Rat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.logSeriesLower`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ → ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(q : Rat) → (n : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.logSeriesUpper`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ → ℕ → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(q : Rat) → (n : Nat) → Rat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_bounds`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate.Valid`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Prop
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) → Prop
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(t : ImbalancedChen.Certificates.RationalLogCertificate) → Nat
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
SizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
SizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.argument`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.casesOn`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.RationalLogCertificate → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    ((argument : ℚ) →
        (terms : ℕ) →
          (lower upper : ℚ) → motive { argument := argument, terms := terms, lower := lower, upper := upper }) →
      motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    (mk :
        (argument : Rat) →
          (terms : Nat) →
            (lower upper : Rat) →
              motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
      motive t
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.check`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Bool
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) → Bool
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate.check_sound`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.RationalLogCertificate.ctorIdx`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Nat
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.lower`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`constructor`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ → ℕ → ℚ → ℚ → ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(argument : Rat) → (terms : Nat) → (lower upper : Rat) → ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.noConfusion`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.RationalLogCertificate} →
    Eq.{1} t t' → ImbalancedChen.Certificates.RationalLogCertificate.noConfusionType.{u} P t t'
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.RationalLogCertificate} →
    (eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate t t') →
      ImbalancedChen.Certificates.RationalLogCertificate.noConfusionType.{u} P t t'
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.noConfusionType`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Sort u →
  ImbalancedChen.Certificates.RationalLogCertificate → ImbalancedChen.Certificates.RationalLogCertificate → Sort u
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(P : Sort u) → (t t' : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.rec`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`recursor`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.RationalLogCertificate → Sort u} →
  ((argument : ℚ) →
      (terms : ℕ) →
        (lower upper : ℚ) → motive { argument := argument, terms := terms, lower := lower, upper := upper }) →
    (t : ImbalancedChen.Certificates.RationalLogCertificate) → motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (mk :
      (argument : Rat) →
        (terms : Nat) →
          (lower upper : Rat) →
            motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
    (t : ImbalancedChen.Certificates.RationalLogCertificate) → motive t
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.recOn`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{motive : ImbalancedChen.Certificates.RationalLogCertificate → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    ((argument : ℚ) →
        (terms : ℕ) →
          (lower upper : ℚ) → motive { argument := argument, terms := terms, lower := lower, upper := upper }) →
      motive t
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    (mk :
        (argument : Rat) →
          (terms : Nat) →
            (lower upper : Rat) →
              motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
      motive t
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.terms`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Nat
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.upper`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℚ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) → Decidable (Eq.{1} x x_1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) →
  Decidable (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate x x_1)
```

传递公理：。

## `ImbalancedChen.Certificates.instReprRationalLogCertificate.repr`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → ℕ → Std.Format
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Nat → Std.Format
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.logSeriesLower.eq_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (q : ℚ) (n : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.logSeriesLower q n)
    (HMul.hMul.{0, 0, 0} 2
      (∑ i ∈ Finset.range n,
        HDiv.hDiv.{0, 0, 0}
          (HPow.hPow.{0, 0, 0} (ImbalancedChen.Certificates.logParameter q)
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 i) 1))
          ↑(HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 i) 1)))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (q : Rat) (n : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logSeriesLower q n)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
      (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid (Finset.range n) fun (i : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
            (ImbalancedChen.Certificates.logParameter q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Rat Rat.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.logSeriesUpper.eq_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (q : ℚ) (n : ℕ),
  Eq.{1} (ImbalancedChen.Certificates.logSeriesUpper q n)
    (HAdd.hAdd.{0, 0, 0} (ImbalancedChen.Certificates.logSeriesLower q n)
      (HDiv.hDiv.{0, 0, 0}
        (HMul.hMul.{0, 0, 0} 2
          (HPow.hPow.{0, 0, 0} (ImbalancedChen.Certificates.logParameter q)
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 n) 1)))
        (HSub.hSub.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} (ImbalancedChen.Certificates.logParameter q) 2))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (q : Rat) (n : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logSeriesUpper q n)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (ImbalancedChen.Certificates.logSeriesLower q n)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
            (ImbalancedChen.Certificates.logParameter q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat
            (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
            (ImbalancedChen.Certificates.logParameter q)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 2] [NeZero.{u_2} 2], Eq.{1} (Eq.{u_2 + 1} 2 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

传递公理：`propext`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_2`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 3] [NeZero.{u_2} 3], Eq.{1} (Eq.{u_2 + 1} 3 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

传递公理：`propext`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_3`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α] [inst_1 : OfNat.{u_2} α 4] [NeZero.{u_2} 4], Eq.{1} (Eq.{u_2 + 1} 4 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

传递公理：`propext`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_4`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [NoZeroDivisors.{u_1} M₀] {a b : M₀},
  Ne.{u_1 + 1} a 0 → Ne.{u_1 + 1} b 0 → Eq.{1} (Eq.{u_1 + 1} (HMul.hMul.{u_1, u_1, u_1} a b) 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

传递公理：`propext`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_5`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀} [IsReduced.{u_1} M₀] (n : ℕ),
  Ne.{u_1 + 1} a 0 → Eq.{1} (Eq.{u_1 + 1} (HPow.hPow.{u_1, 0, u_1} a n) 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat)
  (h :
    @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀
      (@HPow.hPow.{u_1, 0, u_1} M₀ Nat M₀
        (@instHPow.{u_1, 0} M₀ Nat
          (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst))))
        a n)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))))
    False
```

传递公理：`propext`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_6`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : ℤ),
  Ne.{u_3 + 1} a 0 → Eq.{1} (Eq.{u_3 + 1} (HPow.hPow.{u_3, 0, u_3} a n) 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : Int),
  @Ne.{u_3 + 1} G₀ a
      (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_3} G₀
          (@MulZeroClass.toZero.{u_3} G₀
            (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
              (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))) →
    @Eq.{1} Prop
      (@Eq.{u_3 + 1} G₀
        (@HPow.hPow.{u_3, 0, u_3} G₀ Int G₀
          (@instHPow.{u_3, 0} G₀ Int
            (@ZPow.toPow.{u_3} G₀ (@DivInvMonoid.toZPow.{u_3} G₀ (@GroupWithZero.toDivInvMonoid.{u_3} G₀ inst))))
          a n)
        (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
          (@Zero.toOfNat0.{u_3} G₀
            (@MulZeroClass.toZero.{u_3} G₀
              (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
                (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))))
      False
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_7`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [CharZero.{u_1} R] (n : ℕ),
  Eq.{1} (Eq.{u_1 + 1} (HAdd.hAdd.{u_1, u_1, u_1} (↑n) 1) 0) False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [@CharZero.{u_1} R inst] (n : Nat),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} R
      (@HAdd.hAdd.{u_1, u_1, u_1} R R R
        (@instHAdd.{u_1} R
          (@AddSemigroup.toAdd.{u_1} R
            (@AddMonoid.toAddSemigroup.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst))))
        (@Nat.cast.{u_1} R (@AddMonoidWithOne.toNatCast.{u_1} R inst) n)
        (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R inst))))
      (@OfNat.ofNat.{u_1} R (nat_lit 0)
        (@Zero.toOfNat0.{u_1} R
          (@AddZero.toZero.{u_1} R
            (@AddZeroClass.toAddZero.{u_1} R
              (@AddMonoid.toAddZeroClass.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst)))))))
    False
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk._flat_ctor`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℚ → ℕ → ℚ → ℚ → ImbalancedChen.Certificates.RationalLogCertificate
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(argument : Rat) → (terms : Nat) → (lower upper : Rat) → ImbalancedChen.Certificates.RationalLogCertificate
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk.inj`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {argument : ℚ} {terms : ℕ} {lower upper argument_1 : ℚ} {terms_1 : ℕ} {lower_1 upper_1 : ℚ},
  Eq.{1} { argument := argument, terms := terms, lower := lower, upper := upper }
      { argument := argument_1, terms := terms_1, lower := lower_1, upper := upper_1 } →
    Eq.{1} argument argument_1 ∧ Eq.{1} terms terms_1 ∧ Eq.{1} lower lower_1 ∧ Eq.{1} upper upper_1
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {argument : Rat} {terms : Nat} {lower upper argument_1 : Rat} {terms_1 : Nat} {lower_1 upper_1 : Rat},
  @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument_1 terms_1 lower_1 upper_1) →
    And (@Eq.{1} Rat argument argument_1)
      (And (@Eq.{1} Nat terms terms_1) (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1)))
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk.injEq`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (argument : ℚ) (terms : ℕ) (lower upper argument_1 : ℚ) (terms_1 : ℕ) (lower_1 upper_1 : ℚ),
  Eq.{1}
    (Eq.{1} { argument := argument, terms := terms, lower := lower, upper := upper }
      { argument := argument_1, terms := terms_1, lower := lower_1, upper := upper_1 })
    (Eq.{1} argument argument_1 ∧ Eq.{1} terms terms_1 ∧ Eq.{1} lower lower_1 ∧ Eq.{1} upper upper_1)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (argument : Rat) (terms : Nat) (lower upper argument_1 : Rat) (terms_1 : Nat) (lower_1 upper_1 : Rat),
  @Eq.{1} Prop
    (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument_1 terms_1 lower_1 upper_1))
    (And (@Eq.{1} Rat argument argument_1)
      (And (@Eq.{1} Nat terms terms_1) (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1))))
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk.noConfusion`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
{P : Sort u} →
  {argument : ℚ} →
    {terms : ℕ} →
      {lower upper argument' : ℚ} →
        {terms' : ℕ} →
          {lower' upper' : ℚ} →
            Eq.{1} { argument := argument, terms := terms, lower := lower, upper := upper }
                { argument := argument', terms := terms', lower := lower', upper := upper' } →
              (Eq.{1} argument argument' → Eq.{1} terms terms' → Eq.{1} lower lower' → Eq.{1} upper upper' → P) → P
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
{P : Sort u} →
  {argument : Rat} →
    {terms : Nat} →
      {lower upper argument' : Rat} →
        {terms' : Nat} →
          {lower' upper' : Rat} →
            (eq :
                @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
                  (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
                  (ImbalancedChen.Certificates.RationalLogCertificate.mk argument' terms' lower' upper')) →
              (k :
                  (argument_eq : @Eq.{1} Rat argument argument') →
                    (terms_eq : @Eq.{1} Nat terms terms') →
                      (lower_eq : @Eq.{1} Rat lower lower') → (upper_eq : @Eq.{1} Rat upper upper') → P) →
                P
```

传递公理：。

## `ImbalancedChen.Certificates.RationalLogCertificate.mk.sizeOf_spec`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (argument : ℚ) (terms : ℕ) (lower upper : ℚ),
  Eq.{1} (SizeOf.sizeOf.{1} { argument := argument, terms := terms, lower := lower, upper := upper })
    (HAdd.hAdd.{0, 0, 0}
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (SizeOf.sizeOf.{1} argument)) (SizeOf.sizeOf.{1} terms))
        (SizeOf.sizeOf.{1} lower))
      (SizeOf.sizeOf.{1} upper))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (argument : Rat) (terms : Nat) (lower upper : Rat),
  @Eq.{1} Nat
    (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst argument))
          (@SizeOf.sizeOf.{1} Nat instSizeOfNat terms))
        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst lower))
      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst upper))
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a : ℚ) (a_1 : ℕ) (a_2 a_3 : ℚ),
  Eq.{1} { argument := a, terms := a_1, lower := a_2, upper := a_3 }
    { argument := a, terms := a_1, lower := a_2, upper := a_3 }
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 : Rat),
  @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
    (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
    (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_2`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a : ℚ) (a_1 : ℕ) (a_2 a_3 b : ℚ),
  ¬Eq.{1} a_3 b →
    Eq.{1} { argument := a, terms := a_1, lower := a_2, upper := a_3 }
        { argument := a, terms := a_1, lower := a_2, upper := b } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b : Rat),
  Not (@Eq.{1} Rat a_3 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 b) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_3`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a : ℚ) (a_1 : ℕ) (a_2 a_3 b b_1 : ℚ),
  ¬Eq.{1} a_2 b →
    Eq.{1} { argument := a, terms := a_1, lower := a_2, upper := a_3 }
        { argument := a, terms := a_1, lower := b, upper := b_1 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b b_1 : Rat),
  Not (@Eq.{1} Rat a_2 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 b b_1) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_4`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a : ℚ) (a_1 : ℕ) (a_2 a_3 : ℚ) (b : ℕ) (b_1 b_2 : ℚ),
  ¬Eq.{1} a_1 b →
    Eq.{1} { argument := a, terms := a_1, lower := a_2, upper := a_3 }
        { argument := a, terms := b, lower := b_1, upper := b_2 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 : Rat) (b : Nat) (b_1 b_2 : Rat),
  Not (@Eq.{1} Nat a_1 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a b b_1 b_2) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_5`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`theorem`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (a : ℚ) (a_1 : ℕ) (a_2 a_3 b : ℚ) (b_1 : ℕ) (b_2 b_3 : ℚ),
  ¬Eq.{1} a b →
    Eq.{1} { argument := a, terms := a_1, lower := a_2, upper := a_3 }
        { argument := b, terms := b_1, lower := b_2, upper := b_3 } →
      False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b : Rat) (b_1 : Nat) (b_2 b_3 : Rat),
  Not (@Eq.{1} Rat a b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk b b_1 b_2 b_3) →
      False
```

传递公理：。

## `ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq.match_1`

定义模块：`ImbalancedChen.Certificates.RationalLogCertificate`；kind：`definition`；源码 SHA256：`4d705f561d4ba07e01dd7b3af1b0a73bcbf28c9dd6d2ddfd4ae288fb84de9d22`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(motive :
    ImbalancedChen.Certificates.RationalLogCertificate →
      ImbalancedChen.Certificates.RationalLogCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) →
    ((a : ℚ) →
        (a_1 : ℕ) →
          (a_2 a_3 b : ℚ) →
            (b_1 : ℕ) →
              (b_2 b_3 : ℚ) →
                motive { argument := a, terms := a_1, lower := a_2, upper := a_3 }
                  { argument := b, terms := b_1, lower := b_2, upper := b_3 }) →
      motive x x_1
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(motive :
    ImbalancedChen.Certificates.RationalLogCertificate →
      ImbalancedChen.Certificates.RationalLogCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) →
    (h_1 :
        (a : Rat) →
          (a_1 : Nat) →
            (a_2 a_3 b : Rat) →
              (b_1 : Nat) →
                (b_2 b_3 : Rat) →
                  motive (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
                    (ImbalancedChen.Certificates.RationalLogCertificate.mk b b_1 b_2 b_3)) →
      motive x x_1
```

传递公理：。

## `ImbalancedChen.part3IntervalAPCount`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(L U q a : Nat) → Nat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount_abs_sub_le_two`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount_coprimeMean_error`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount_le_add_two`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalCoprimeCount`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℕ → ℕ → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(L U q : Nat) → Nat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalCoprimeCount_eq_sum`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotAPCount`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(L U q a m : Nat) → Nat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotCoprimeCount`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℕ → ℕ → ℕ → ℕ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(L U q m : Nat) → Nat
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotRemainder`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(L U q a m : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotRemainder_abs_le_two`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotRemainder_eq_zero_of_not_coprime`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotSignedError`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`definition`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Finset.{0} ℕ → Finset.{0} ℕ → (ℕ → ℂ) → (ℕ → ℂ) → ℕ → ℕ → ℕ → ℂ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(S Q : Finset.{0} Nat) → (α ρ : Nat → Complex) → (L U a : Nat) → Complex
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotSignedError_norm_le`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotSignedError_norm_le_box`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotSignedError_norm_le_card`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotSignedError_norm_le_of_mass`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount.eq_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a : ℕ),
  Eq.{1} (ImbalancedChen.part3IntervalAPCount L U q a) (Finset.card.{0} ({n ∈ Finset.Ico.{0} L U | n ≡ a [MOD q]}))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalAPCount L U q a)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount_le_add_two._proof_1_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a b : ℕ),
  LE.le.{0} (Nat.count (fun n => n ≡ a [MOD q]) U) (HAdd.hAdd.{0, 0, 0} (Nat.count (fun n => n ≡ b [MOD q]) U) 1) →
    LE.le.{0} (Nat.count (fun n => n ≡ b [MOD q]) L) (HAdd.hAdd.{0, 0, 0} (Nat.count (fun n => n ≡ a [MOD q]) L) 1) →
      LE.le.{0} (Nat.count (fun n => n ≡ a [MOD q]) L) (Nat.count (fun n => n ≡ a [MOD q]) U) →
        LE.le.{0} (Nat.count (fun n => n ≡ b [MOD q]) L) (Nat.count (fun n => n ≡ b [MOD q]) U) →
          ¬LE.le.{0} (HSub.hSub.{0, 0, 0} (Nat.count (fun n => n ≡ a [MOD q]) U) (Nat.count (fun n => n ≡ a [MOD q]) L))
                (HAdd.hAdd.{0, 0, 0}
                  (HSub.hSub.{0, 0, 0} (Nat.count (fun n => n ≡ b [MOD q]) U) (Nat.count (fun n => n ≡ b [MOD q]) L))
                  2) →
            False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a b : Nat)
  (hU :
    @LE.le.{0} Nat instLENat
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hL :
    @LE.le.{0} Nat instLENat
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ha :
    @LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U))
  (hb :
    @LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)),
  Not
      (@LE.le.{0} Nat instLENat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
          (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
            (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.part3IntervalAPCount_le_add_two._proof_1_3`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q : ℕ), ¬LE.le.{0} L U → ¬LE.le.{0} U L → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q : Nat) (hLU : Not (@LE.le.{0} Nat instLENat L U)), Not (@LE.le.{0} Nat instLENat U L) → False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.part3IntervalCoprimeCount.eq_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q : ℕ),
  Eq.{1} (ImbalancedChen.part3IntervalCoprimeCount L U q) (Finset.card.{0} ({n ∈ Finset.Ico.{0} L U | q.Coprime n}))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalCoprimeCount L U q)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat (fun (n : Nat) => Nat.Coprime q n) (Nat.instDecidableCoprime q)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3IntervalCoprimeCount_eq_sum._simp_1_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotAPCount.eq_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a m : ℕ),
  Eq.{1} (ImbalancedChen.part3LongSlotAPCount L U q a m)
    (Finset.card.{0} ({n ∈ Finset.Ico.{0} L U | HMul.hMul.{0, 0, 0} m n ≡ a [MOD q]}))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a m : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3LongSlotAPCount L U q a m)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat
        (fun (n : Nat) => Nat.ModEq q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m n) a)
        (fun (a_1 : Nat) =>
          @Nat.instDecidableModEq q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a_1) a)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotCoprimeCount.eq_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q m : ℕ),
  Eq.{1} (ImbalancedChen.part3LongSlotCoprimeCount L U q m)
    (Finset.card.{0} ({n ∈ Finset.Ico.{0} L U | (HMul.hMul.{0, 0, 0} m n).Coprime q}))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q m : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3LongSlotCoprimeCount L U q m)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat
        (fun (n : Nat) => Nat.Coprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m n) q)
        (fun (a : Nat) =>
          Nat.instDecidableCoprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a) q)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.part3LongSlotRemainder.eq_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U q a m : ℕ),
  Eq.{1} (ImbalancedChen.part3LongSlotRemainder L U q a m)
    (HSub.hSub.{0, 0, 0} (↑(ImbalancedChen.part3LongSlotAPCount L U q a m))
      (HDiv.hDiv.{0, 0, 0} ↑(ImbalancedChen.part3LongSlotCoprimeCount L U q m) ↑q.totient))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U q a m : Nat),
  @Eq.{1} Real (ImbalancedChen.part3LongSlotRemainder L U q a m)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3LongSlotAPCount L U q a m))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3LongSlotCoprimeCount L U q m))
        (@Nat.cast.{0} Real Real.instNatCast (Nat.totient q))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._proof_1_5`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (L U n : ℕ), ¬(LE.le.{0} L n ∧ LT.lt.{0} n U ↔ LT.lt.{0} n U ∧ ¬LT.lt.{0} n L) → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (L U n : Nat),
  Not
      (Iff
        (And (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) L n)
          (@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder) n U))
        (And (@LT.lt.{0} Nat instLTNat n U) (Not (@LT.lt.{0} Nat instLTNat n L)))) →
    False
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_2`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : LocallyFiniteOrder.{u_1} α] {a b x : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.Ico.{u_1} a b) x) (LE.le.{u_1} a x ∧ LT.lt.{u_1} x b)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Ico.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LT.lt.{u_1} α (@Preorder.toLT.{u_1} α inst) x b))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_3`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (SDiff.sdiff.{u_1} s t) a) (Membership.mem.{u_1, u_1} s a ∧ a ∉ t)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@SDiff.sdiff.{u_1} (Finset.{u_1} α) (@Finset.instSDiff.{u_1} α inst) s t) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (Not
        (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) t a)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_4`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {n m : ℕ}, Eq.{1} (Membership.mem.{0, 0} (Finset.range n) m) (LT.lt.{0} m n)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_1`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (U q a b : ℕ),
  ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 1)
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 1) 1) →
    False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_2`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (U q a b : ℕ),
  ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 1)
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 0) 1) →
    False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_3`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (U q a b : ℕ),
  ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 0)
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 1) 1) →
    False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `_private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_4`

定义模块：`ImbalancedChen.Part3LongSlotDistribution`；kind：`theorem`；源码 SHA256：`67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (U q a b : ℕ),
  ¬LE.le.{0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 0)
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} U q) 0) 1) →
    False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.currentChen_buchstab_eleven_twentieths`

定义模块：`ImbalancedChen.CurrentChenBuchstabRefinement`；kind：`theorem`；源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_buchstab_lower_first_segment`

定义模块：`ImbalancedChen.CurrentChenBuchstabRefinement`；kind：`theorem`；源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → s ≤ 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_buchstab_lower_on_tail`

定义模块：`ImbalancedChen.CurrentChenBuchstabRefinement`；kind：`theorem`；源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a L : ℝ},
  2 ≤ a →
    (∀ u ∈ Set.Icc a (a + 1), L ≤ LiLiuPrereqBuchstab.buchstab u) →
      ∀ (u : ℝ), a ≤ u → L ≤ LiLiuPrereqBuchstab.buchstab u
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_buchstab_lower_transition`

定义模块：`ImbalancedChen.CurrentChenBuchstabRefinement`；kind：`theorem`；源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {s : ℝ}, 3 ≤ s → s ≤ 10 / 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `_private.ImbalancedChen.CurrentChenBuchstabRefinement.0.ImbalancedChen.currentChen_log_rational_lower`

定义模块：`ImbalancedChen.CurrentChenBuchstabRefinement`；kind：`theorem`；源码 SHA256：`02e565bf35ecff746ce3d552b64bc0cad3a402aecfd1484c1e9d4a967f159ca5`。

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {x : ℝ}, 1 ≤ x → 2 * ((x - 1) / (x + 1)) ≤ Real.log x
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_four_currentC`

定义模块：`ImbalancedChen.CurrentChenLowerScale`；kind：`theorem`；源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_lower_scale_from_finite_weight_bound`

定义模块：`ImbalancedChen.CurrentChenLowerScale`；kind：`theorem`；源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_lower_scale_of_equal_finite_budgets`

定义模块：`ImbalancedChen.CurrentChenLowerScale`；kind：`theorem`；源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChen_lower_scale_of_finite_budgets`

定义模块：`ImbalancedChen.CurrentChenLowerScale`；kind：`theorem`；源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentC.eq_1`

定义模块：`ImbalancedChen.CurrentChenLowerScale`；kind：`theorem`；源码 SHA256：`cea233e4897e4f550760ca82eba84e6ca9254593a8cbba030f22940e3086ab13`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
Eq.{1} ImbalancedChen.currentC (49044063 / 25000000)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
@Eq.{1} Real ImbalancedChen.currentC
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 49044063)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 49044063) Real.instNatCast ImbalancedChen.currentC._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 25000000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 25000000) Real.instNatCast ImbalancedChen.currentC._proof_2)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenPairedElevenWeight_eq_unselected`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY10PrimeSelector`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ → ℝ → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} ℕ ℕ) (Prod.{0, 0} ℕ ℕ))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (A H : Real) → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY10Tuples_eq_selector_filter`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11FullPrimeSelector`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ → ℝ → ℝ → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} ℕ ℕ) (Prod.{0, 0} ℕ ℕ))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (A H D : Real) → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11FullTuples_eq_selector_filter`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11Selected_add_compl`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY6Selected_add_compl`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY7PrimeSelector`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ → Finset.{0} (Prod.{0, 0} ℕ ℕ)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (D : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY7Tuples_eq_selector_filter`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY8PrimeSelector`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ → ℝ → Finset.{0} (Prod.{0, 0} ℕ ℕ)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (A C : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY8Tuples_eq_selector_filter`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY9PrimeSelector`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ → ℝ → Finset.{0} (Prod.{0, 0} ℕ ℕ)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (H D : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY9Tuples_eq_selector_filter`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chen_sum_quotient_tuple_card_moving_cutoff`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum_ge_of_joint_last_bounds`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_term_bounds`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum_ge_of_term_bounds`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon10`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon10_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon11`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → (Prod.{0, 0} ℕ ℕ → Prop) → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (E : Prod.{0, 0} Nat Nat → Prop) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon11_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon1_eq_actual_siftedSum`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon1_eq_actual_sifted_card`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon2`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon2_eq_actual_siftedSum`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon2_eq_actual_sifted_card`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon3_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon4_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon5`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon5_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon6`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → (Prod.{0, 0} ℕ ℕ → Prop) → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → (E : Prod.{0, 0} Nat Nat → Prop) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon6_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon7`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon7_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon8`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon8_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon9`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`definition`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
ℕ → ℝ
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
(N : Nat) → Real
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon9_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY10_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY11Selected_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY6Selected_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY7_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY8_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY9_eq_siftedQuotientPrimeSource`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY10PrimeSelector.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A H : ℝ),
  Eq.{1} (ImbalancedChen.chenY10PrimeSelector N A H)
    ({t ∈
        SProd.sprod.{0, 0, 0}
          (SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N)
            (ImbalancedChen.chenAdditivePrimeCarrier N))
          (SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N)
            (ImbalancedChen.chenAdditivePrimeCarrier N)) |
      LE.le.{0} A ↑t.1.1 ∧
        LT.lt.{0} t.1.1 t.1.2 ∧ LT.lt.{0} t.1.2 t.2.1 ∧ LT.lt.{0} t.2.1 t.2.2 ∧ LT.lt.{0} (↑t.2.2) H})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A H : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY10PrimeSelector N A H)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        And
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                  H)))))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H))))
          (Real.decidableLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (@instDecidableAnd
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@instDecidableAnd
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H))
              (Nat.decLt (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@instDecidableAnd
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (Real.decidableLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
        (@Finset.instSProd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY10Tuples_eq_selector_filter._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ}, LT.lt.{0} P N → Eq.{1} (HSub.hSub.{0, 0, 0} N P) 0 → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chenY10Tuples_eq_selector_filter._simp_1_3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY10Tuples_eq_selector_filter._simp_1_4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11FullPrimeSelector.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A H D : ℝ),
  Eq.{1} (ImbalancedChen.chenY11FullPrimeSelector N A H D)
    ({t ∈
        SProd.sprod.{0, 0, 0}
          (SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N)
            (ImbalancedChen.chenAdditivePrimeCarrier N))
          (SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N)
            (ImbalancedChen.chenAdditivePrimeCarrier N)) |
      LE.le.{0} A ↑t.1.1 ∧
        LT.lt.{0} t.1.1 t.1.2 ∧
          LT.lt.{0} t.1.2 t.2.1 ∧ LT.lt.{0} (↑t.2.1) H ∧ LE.le.{0} H ↑t.2.2 ∧ LT.lt.{0} (↑t.2.2) D})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY11FullPrimeSelector N A H D)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        And
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                    D))))))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)))))
          (Real.decidableLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (@instDecidableAnd
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@instDecidableAnd
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)))
              (Nat.decLt (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@instDecidableAnd
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))
                (Real.decidableLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (@instDecidableAnd
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)
                  (Real.decidableLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (Real.decidableLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
        (@Finset.instSProd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11FullTuples_eq_selector_filter._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ}, LT.lt.{0} P N → Eq.{1} (HSub.hSub.{0, 0, 0} N P) 0 → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chenY11FullTuples_eq_selector_filter._simp_1_3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY11FullTuples_eq_selector_filter._simp_1_4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY7PrimeSelector.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (D : ℝ),
  Eq.{1} (ImbalancedChen.chenY7PrimeSelector N D)
    ({t ∈
        SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) (ImbalancedChen.chenAdditivePrimeCarrier N) |
      LE.le.{0} D ↑t.1 ∧ LT.lt.{0} t.1 t.2 ∧ LT.lt.{0} ↑t.2 √(HDiv.hDiv.{0, 0, 0} ↑N ↑t.1)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY7PrimeSelector N D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat t) (@Prod.snd.{0, 0} Nat Nat t))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
          (Real.decidableLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY7Tuples_eq_selector_filter._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ}, LT.lt.{0} P N → Eq.{1} (HSub.hSub.{0, 0, 0} N P) 0 → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chenY7Tuples_eq_selector_filter._simp_1_3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY7Tuples_eq_selector_filter._simp_1_4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY8PrimeSelector.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (A C : ℝ),
  Eq.{1} (ImbalancedChen.chenY8PrimeSelector N A C)
    ({t ∈
        SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) (ImbalancedChen.chenAdditivePrimeCarrier N) |
      LE.le.{0} A ↑t.1 ∧ LT.lt.{0} (↑t.1) C ∧ LE.le.{0} C ↑t.2 ∧ LT.lt.{0} ↑t.2 √(HDiv.hDiv.{0, 0, 0} ↑N ↑t.1)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (A C : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY8PrimeSelector N A C)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
          (Real.decidableLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (@instDecidableAnd
              (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
              (Real.decidableLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY8Tuples_eq_selector_filter._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ}, LT.lt.{0} P N → Eq.{1} (HSub.hSub.{0, 0, 0} N P) 0 → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chenY8Tuples_eq_selector_filter._simp_1_3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY8Tuples_eq_selector_filter._simp_1_4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY9PrimeSelector.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (H D : ℝ),
  Eq.{1} (ImbalancedChen.chenY9PrimeSelector N H D)
    ({t ∈
        SProd.sprod.{0, 0, 0} (ImbalancedChen.chenAdditivePrimeCarrier N) (ImbalancedChen.chenAdditivePrimeCarrier N) |
      LE.le.{0} H ↑t.1 ∧ LT.lt.{0} (↑t.1) D ∧ LE.le.{0} D ↑t.2 ∧ LT.lt.{0} ↑t.2 √(HDiv.hDiv.{0, 0, 0} ↑N ↑t.1)})
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY9PrimeSelector N H D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
          (Real.decidableLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (@instDecidableAnd
              (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
              (Real.decidableLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY9Tuples_eq_selector_filter._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ}, LT.lt.{0} P N → Eq.{1} (HSub.hSub.{0, 0, 0} N P) 0 → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chenY9Tuples_eq_selector_filter._simp_1_3`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred.{u_1 + 1} p] {s : Finset.{u_1} α} {a : α},
  Eq.{1} (Membership.mem.{u_1, u_1} (Finset.filter.{u_1} p s) a) (Membership.mem.{u_1, u_1} s a ∧ p a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chenY9Tuples_eq_selector_filter._simp_1_4`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  Eq.{1} (Membership.mem.{max u_1 u_2, max u_1 u_2} (SProd.sprod.{u_1, u_2, max u_1 u_2} s t) p)
    (Membership.mem.{u_1, u_1} s p.1 ∧ Membership.mem.{u_2, u_2} t p.2)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier._proof_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P : ℕ} {p : ℕ}, LT.lt.{0} P N → ¬LT.lt.{0} 0 (HSub.hSub.{0, 0, 0} N P) → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P p : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  Not
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)) →
    False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier._proof_1_2`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {N P p : ℕ}, LT.lt.{0} P N → LE.le.{0} p (HSub.hSub.{0, 0, 0} N P) → LT.lt.{0} 0 P → ¬LT.lt.{0} p N → False
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {N P p : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N)
  (hle : @LE.le.{0} Nat instLENat p (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
  (hPpos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P),
  Not (@LT.lt.{0} Nat instLTNat p N) → False
```

传递公理：`propext`, `Quot.sound`。

## `ImbalancedChen.currentChenPairedPrimeSum.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenPairedPrimeSum N E)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ImbalancedChen.currentChenPairedWeight (HSub.hSub.{0, 0, 0} N P) (↑N) E)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenPairedPrimeSum N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      ImbalancedChen.currentChenPairedWeight (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
        (@Nat.cast.{0} Real Real.instNatCast N) E)
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon1._proof_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 416 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon1._proof_2`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 4999 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon1.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon1 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY1 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY1 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon10.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon10 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY10 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon10 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY10 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon11.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenUpsilon11 N E)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY11Selected (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)) (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)) fun t => ¬E t))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon11 N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))
          fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon2._proof_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 18 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon2._proof_2`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 124 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon2.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon2 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY2 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY2 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon3._proof_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 2 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon3.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon3 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY3 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (1 / 3))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon3 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY3 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon3._proof_1))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon4._proof_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 58 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon4._proof_2`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
(HAdd.hAdd.{0, 0, 0} 249 1).AtLeastTwo
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

传递公理：`propext`。

## `ImbalancedChen.currentChenUpsilon4.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon4 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY4 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (59 / 250))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon4 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY4 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon5.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon5 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY5 (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon5 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY5 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon6.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ) (E : Prod.{0, 0} ℕ ℕ → Prop),
  Eq.{1} (ImbalancedChen.currentChenUpsilon6 N E)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY6Selected (HSub.hSub.{0, 0, 0} N P) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (19 / 125)) (HPow.hPow.{0, 0, 0} (↑N) (59 / 250)) fun t => ¬E t))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon6 N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY6Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))
          fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon7.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon7 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY7 (HSub.hSub.{0, 0, 0} N P) (↑N) (HPow.hPow.{0, 0, 0} (↑N) (59 / 250))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon7 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY7 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon8.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon8 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY8 (HSub.hSub.{0, 0, 0} N P) (↑N) (HPow.hPow.{0, 0, 0} (↑N) (417 / 5000))
          (HPow.hPow.{0, 0, 0} (↑N) (1 / 3))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon8 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY8 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon3._proof_1))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.currentChenUpsilon9.eq_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ (N : ℕ),
  Eq.{1} (ImbalancedChen.currentChenUpsilon9 N)
    (∑ P ∈ ImbalancedChen.chenAdditivePrimeCarrier N,
      ↑(ImbalancedChen.chenY9 (HSub.hSub.{0, 0, 0} N P) (↑N) (HPow.hPow.{0, 0, 0} (↑N) (19 / 125))
          (HPow.hPow.{0, 0, 0} (↑N) (59 / 250))))
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon9 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY9 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.sum_chenY11Selected_eq_siftedQuotientPrimeSource._simp_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a b : Prop}, Eq.{1} (a ∧ b) (b ∧ a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a b : Prop}, @Eq.{1} Prop (And a b) (And b a)
```

传递公理：`propext`。

## `ImbalancedChen.sum_chenY6Selected_eq_siftedQuotientPrimeSource._simp_1_1`

定义模块：`ImbalancedChen.CurrentChenMeanLedger`；kind：`theorem`；源码 SHA256：`30597d5f381031fc7d7e794fe105a11d6981053b34a1406d46f40bf7840dc0c8`。

编译器可读类型（原始 `readable_type` 字段）：

```lean
∀ {a b : Prop}, Eq.{1} (a ∧ b) (b ∧ a)
```

编译器完整类型（原始 `type` 字段，保留审计的打印设置）：

```lean
∀ {a b : Prop}, @Eq.{1} Prop (And a b) (And b a)
```

传递公理：`propext`。

## `ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_eleven_twentieths`

定义模块：`ImbalancedChen.CurrentPairedBuchstabBridge`；kind：`theorem`；源码 SHA256：`280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## `ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_gain`

定义模块：`ImbalancedChen.CurrentPairedBuchstabBridge`；kind：`theorem`；源码 SHA256：`280481d294ebd6c9fa73e74e19b5dbd2efcb2018af6c6a1953d746cee80a7550`。

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

传递公理：`propext`, `Classical.choice`, `Quot.sound`。
