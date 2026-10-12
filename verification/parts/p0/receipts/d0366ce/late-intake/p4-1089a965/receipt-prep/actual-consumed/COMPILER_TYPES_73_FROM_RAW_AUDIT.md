# 从失败运行的已完成 Audit 原始输出提取的完整编译器类型

源 SHA：`1089a965e20664e63ffd51e0105c11befa406a1f`；run `38288356713`；artifact `11768093422`。

**73 项均为实际编译器打印类型，不是源码声明头。** 对应 Audit strict stage exit 0；`pp.all=true`、`pp.privateNames=true`，并记录 universe parameters。全部原始 `PART4_UPPER_AUDIT_DECL`、五模块 count 和总计 73 均存在。

原始日志 member：`run-1791828370977599814/axioms-and-types.log`；SHA-256：`e2c2d23216027005e6ec65794abaa565c964c65d0d3f74df30689f131b2dca86`。

CI 最终失败于后续 aggregate fresh timeout；最终 source/object/binary 重查未完成。此为 P0 派生保存的已完成阶段输出，不是成功封存回执，也不是生产者尚未生成的四个导出文件。
## `ImbalancedChen.RealB_cast_le_actualSmallRoughRho_main_add_errors`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：2
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N cap : Nat) (retainOdd : List.{0} Nat → Bool) (w z L : Real)
  (hb : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hL : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
  (hwL : @LE.le.{0} Real Real.instLE w L) (hwz : @LE.le.{0} Real Real.instLE w z)
  (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap)),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
              (ImbalancedChen.physicalDensitySum (ImbalancedChen.actualSmallRoughModuli retainOdd N cap w z)
                (ImbalancedChen.actualSmallRoughRho retainOdd N cap w z L)))
            (ImbalancedChen.realPhysicalCoprimeCorrection b N T
              (ImbalancedChen.actualSmallRoughModuli retainOdd N cap w z)
              (ImbalancedChen.actualSmallRoughRho retainOdd N cap w z L)))
          (ImbalancedChen.realPhysicalDistributionError b N T
            (ImbalancedChen.actualSmallRoughModuli retainOdd N cap w z)
            (ImbalancedChen.actualSmallRoughRho retainOdd N cap w z L)))
        (@Nat.cast.{0} Real Real.instNatCast
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：3
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N z : Nat)
  (hb : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@Nat.cast.{0} Real Real.instNatCast
          (@Finset.card.{0} Nat (ImbalancedChen.realSiftedHalfProductSource b N T z)))
        (@Nat.cast.{0} Real Real.instNatCast z))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.RealB_cast_le_same_rho_main_add_distribution_of_gate`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：4
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N z : Nat) (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hb1 : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hcap :
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast z)
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) T
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b))))
  (hsupport :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q d →
        @Ne.{1} Real (rho d) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Dvd.dvd.{0} Nat Nat.instDvd d (ImbalancedChen.sieveProduct N z))
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
            (ImbalancedChen.physicalDensitySum Q rho))
          (ImbalancedChen.realPhysicalDistributionError b N T Q rho))
        (@Nat.cast.{0} Real Real.instNatCast z))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.RealB_cast_le_same_rho_main_add_errors`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：5
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N z : Nat) (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hb : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
              (ImbalancedChen.physicalDensitySum Q rho))
            (ImbalancedChen.realPhysicalCoprimeCorrection b N T Q rho))
          (ImbalancedChen.realPhysicalDistributionError b N T Q rho))
        (@Nat.cast.{0} Real Real.instNatCast z))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.RealB_cast_le_same_rho_outer_main_add_errors`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：6
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N z : Nat) (S Q : Finset.{0} Nat) (weight rho : Nat → Real)
  (hb : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hSN :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Nat instLENat m N)
  (hsource :
    @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      (ImbalancedChen.realHalfProductSource b N T) S)
  (houter :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Real Real.instLE
          (@ite.{1} Real
            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
              (ImbalancedChen.realHalfProductSource b N T) m)
            (@Finset.decidableMem.{0} Nat instDecidableEqNat m (ImbalancedChen.realHalfProductSource b N T))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (weight m))
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (ImbalancedChen.finiteSourceMass S weight) (ImbalancedChen.physicalDensitySum Q rho))
            (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
              @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (ImbalancedChen.finiteCoprimeMass S weight d) (ImbalancedChen.finiteSourceMass S weight))
                  (@Nat.cast.{0} Real Real.instNatCast (Nat.totient d)))))
          (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
              (ImbalancedChen.finitePrimitiveDiscrepancy S weight N d)))
        (@Nat.cast.{0} Real Real.instNatCast z))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：7
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} (N z : Nat) (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hb : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hT : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.realHalfProductSource b N T)
          fun (m : Nat) =>
          ImbalancedChen.physicalDivisorSum Q rho (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m))
        (@Nat.cast.{0} Real Real.instNatCast z))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) T
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## `ImbalancedChen.abs_physicalDensitySum_smallRoughRho_sub_le`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：8
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {w : Real} {small rough : Finset.{0} Nat}
  (hsmall :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) small d →
        ImbalancedChen.SmallPrimeSupportedAt w d)
  (hrough :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) rough d →
        ImbalancedChen.RoughPrimeSupportedAt w d)
  (compiled raw betaMinus betaPlus : Nat → Real) {M : Real}
  (hminus :
    @LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.reciprocalTotientDensity small betaMinus)) M)
  (hplus :
    @LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.reciprocalTotientDensity small betaPlus)) M),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.physicalDensitySum (ImbalancedChen.smallRoughModuli small rough)
          (ImbalancedChen.smallRoughRho small rough compiled betaMinus betaPlus))
        (ImbalancedChen.physicalDensitySum (ImbalancedChen.smallRoughModuli small rough)
          (ImbalancedChen.smallRoughRho small rough raw betaMinus betaPlus))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M
      (ImbalancedChen.reciprocalTotientDensity rough fun (d : Nat) =>
        @abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (compiled d) (raw d))))
```

## `ImbalancedChen.abs_signAttachedValue_sub_le`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：9
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {c d lo hi M : Real} (hlo : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup lo) M)
  (hhi : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup hi) M),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (ImbalancedChen.signAttachedValue c lo hi)
        (ImbalancedChen.signAttachedValue d lo hi)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) c d)))
```

## `ImbalancedChen.abs_signSensitiveReciprocalTotientDensity_sub_le`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：10
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (rough : Finset.{0} Nat) (compiled raw : Nat → Real) {lo hi M : Real}
  (hlo : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup lo) M)
  (hhi : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup hi) M),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.signSensitiveReciprocalTotientDensity rough compiled lo hi)
        (ImbalancedChen.signSensitiveReciprocalTotientDensity rough raw lo hi)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M
      (ImbalancedChen.reciprocalTotientDensity rough fun (d : Nat) =>
        @abs.{0} Real Real.lattice Real.instAddGroup
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (compiled d) (raw d))))
```

## `ImbalancedChen.actualAttachedRho_majorant_of_rough_domination`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：11
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N cap : Nat) (w z L : Real) (rough : Finset.{0} Nat) (raw compiled : Nat → Real)
  (hrough :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) rough d →
        ImbalancedChen.RoughPrimeSupportedAt w d)
  (hraw :
    ∀ (n : Int),
      @LE.le.{0} Real Real.instLE (ImbalancedChen.actualIntervalRoughIndicator N w z n)
        (ImbalancedChen.supportedDivisorSum rough raw (Int.natAbs n)))
  (hdom :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) rough d →
        @LE.le.{0} Real Real.instLE (raw d) (compiled d))
  (hL : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
  (hwL : @LE.le.{0} Real Real.instLE w L) (hwz : @LE.le.{0} Real Real.instLE w z)
  (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap)) (n : Int),
  @LE.le.{0} Real Real.instLE (ImbalancedChen.actualSmallRoughIndicator N z n)
    (ImbalancedChen.physicalDivisorSum
      (ImbalancedChen.smallRoughModuli (ImbalancedChen.actualSmallRosserSupport N cap w) rough)
      (ImbalancedChen.smallRoughRho (ImbalancedChen.actualSmallRosserSupport N cap w) rough compiled
        (ImbalancedChen.actualSmallRosserMinus N cap w L) (ImbalancedChen.actualSmallRosserPlus N cap w L))
      (Int.natAbs n))
```

## `ImbalancedChen.actualSelectedPrefixSplicePolicy_upper_even`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：12
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {d : Nat} (N : Real) (I : Finset.{0} (Fin d)) (old nu a b : Rat) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (pre : List.{0} Nat),
  @Eq.{1} Bool (@ImbalancedChen.actualSelectedPrefixSplicePolicy d Bool.false N I old nu a b m J Bool.true pre)
    Bool.true
```

## `ImbalancedChen.actualSelectedPrefixUpperDensity_eq_fixedRoughDensity`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：13
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N cap : Nat) (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) (old nu a b : Rat)
  (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Eq.{1} Real (ImbalancedChen.actualSelectedPrefixUpperDensity N cap I old nu a b m J)
    (ImbalancedChen.reciprocalTotientDensity
      (ImbalancedChen.fixedRoughSupport
        (@ImbalancedChen.actualSelectedPrefixSplicePolicy (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          Bool.false (@Nat.cast.{0} Real Real.instNatCast N) I old nu a b m J Bool.false)
        N cap (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b)))
      (ImbalancedChen.fixedRoughCoefficient
        (@ImbalancedChen.actualSelectedPrefixSplicePolicy (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          Bool.false (@Nat.cast.{0} Real Real.instNatCast N) I old nu a b m J Bool.false)
        N cap (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))))
```

## `ImbalancedChen.actualSmallPrimeFinset_eq_sievePrimes_ceil`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：14
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N cap : Nat) (z : Real) (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap)),
  @Eq.{1} (Finset.{0} Nat) (ImbalancedChen.actualSmallPrimeFinset N cap z)
    (ImbalancedChen.sievePrimes N
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
```

## `ImbalancedChen.actualSmallPrimeProduct_eq_sieveProduct_ceil`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：15
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N cap : Nat) (z : Real) (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap)),
  @Eq.{1} Nat (ImbalancedChen.actualSmallPrimeProduct N cap z)
    (ImbalancedChen.sieveProduct N
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
```

## `ImbalancedChen.actualSmallRosserSupport_dvd_sieveProduct_ceil`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：16
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N cap : Nat) (w z : Real) (hwz : @LE.le.{0} Real Real.instLE w z) {d : Nat}
  (hd :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.actualSmallRosserSupport N cap w) d),
  @Dvd.dvd.{0} Nat Nat.instDvd d
    (ImbalancedChen.sieveProduct N
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
```

## `ImbalancedChen.actualSmallRoughIndicator_eq_sieveProduct_natAbs`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：17
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat) (z : Real) (n : Int),
  @Eq.{1} Real (ImbalancedChen.actualSmallRoughIndicator N z n)
    (@ite.{1} Real
      (Nat.Coprime (Int.natAbs n)
        (ImbalancedChen.sieveProduct N
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z)))
      (Nat.instDecidableCoprime (Int.natAbs n)
        (ImbalancedChen.sieveProduct N
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## `ImbalancedChen.actualSmallRoughModuli_dvd_sieveProduct_ceil`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：18
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retainOdd : List.{0} Nat → Bool) (N cap : Nat) (w z : Real) (hwz : @LE.le.{0} Real Real.instLE w z) {d : Nat}
  (hd :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.actualSmallRoughModuli retainOdd N cap w z) d),
  @Dvd.dvd.{0} Nat Nat.instDvd d
    (ImbalancedChen.sieveProduct N
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
```

## `ImbalancedChen.actualSmallRoughModuli_eq_firstExitAttachment`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：19
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retained : Bool → List.{0} Nat → Bool)
  (heven : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (retained Bool.true pre) Bool.true) (N cap : Nat) (w z : Real),
  @Eq.{1} (Finset.{0} Nat) (ImbalancedChen.actualSmallRoughModuli (retained Bool.false) N cap w z)
    (ImbalancedChen.smallRoughModuli (ImbalancedChen.actualSmallRosserSupport N cap w)
      (ImbalancedChen.firstExitRetainedModuli retained (ImbalancedChen.roughPrimeUniverse N cap w z)))
```

## `ImbalancedChen.actualSmallRoughRho_eq_firstExitAttachment`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：20
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retained : Bool → List.{0} Nat → Bool)
  (heven : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (retained Bool.true pre) Bool.true) (N cap : Nat) (w z L : Real),
  @Eq.{1} (Nat → Real) (ImbalancedChen.actualSmallRoughRho (retained Bool.false) N cap w z L)
    (ImbalancedChen.smallRoughRho (ImbalancedChen.actualSmallRosserSupport N cap w)
      (ImbalancedChen.firstExitRetainedModuli retained (ImbalancedChen.roughPrimeUniverse N cap w z))
      (fun (d : Nat) =>
        @Int.cast.{0} Real Real.instIntCast
          (ImbalancedChen.firstExitRetainedCoefficient retained (ImbalancedChen.roughPrimeUniverse N cap w z) d))
      (ImbalancedChen.actualSmallRosserMinus N cap w L) (ImbalancedChen.actualSmallRosserPlus N cap w L))
```

## `ImbalancedChen.actualSmallRoughRho_sieveProduct_majorant`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：21
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retainOdd : List.{0} Nat → Bool) (N cap : Nat) (w z L : Real)
  (hL : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
  (hwL : @LE.le.{0} Real Real.instLE w L) (hwz : @LE.le.{0} Real Real.instLE w z)
  (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap)) (n : Nat),
  @LE.le.{0} Real Real.instLE
    (@ite.{1} Real
      (Nat.Coprime n
        (ImbalancedChen.sieveProduct N
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z)))
      (Nat.instDecidableCoprime n
        (ImbalancedChen.sieveProduct N
          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (ImbalancedChen.physicalDivisorSum (ImbalancedChen.actualSmallRoughModuli retainOdd N cap w z)
      (ImbalancedChen.actualSmallRoughRho retainOdd N cap w z L) n)
```

## `ImbalancedChen.compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：22
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N) {w : Real}
  {small rough : Finset.{0} Nat}
  (hsmall :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) small d →
        ImbalancedChen.SmallPrimeSupportedAt w d)
  (hrough :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) rough d →
        ImbalancedChen.RoughPrimeSupportedAt w d)
  (compiled raw betaMinus betaPlus : Nat → Real) (M rawBound compilerReserve : Real)
  (hminus :
    @LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.reciprocalTotientDensity small betaMinus)) M)
  (hplus :
    @LE.le.{0} Real Real.instLE
      (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.reciprocalTotientDensity small betaPlus)) M)
  (hraw :
    @LE.le.{0} Real Real.instLE
      (ImbalancedChen.physicalDensitySum (ImbalancedChen.smallRoughModuli small rough)
        (ImbalancedChen.smallRoughRho small rough raw betaMinus betaPlus))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) rawBound
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
  (hcompiler :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M
        (ImbalancedChen.reciprocalTotientDensity rough fun (d : Nat) =>
          @abs.{0} Real Real.lattice Real.instAddGroup
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (compiled d) (raw d))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) compilerReserve
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
  (hbudget :
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) rawBound compilerReserve)
      ImbalancedChen.currentK),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (ImbalancedChen.physicalDensitySum (ImbalancedChen.smallRoughModuli small rough)
          (ImbalancedChen.smallRoughRho small rough compiled betaMinus betaPlus))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
      (ImbalancedChen.singularSeries N))
    ImbalancedChen.currentK
```

## `ImbalancedChen.densityScale_pos`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：23
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
```

## `ImbalancedChen.density_le_manuscriptScale_iff_normalized`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：24
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
  (density coefficient : Real),
  Iff
    (@LE.le.{0} Real Real.instLE density
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) coefficient
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
    (@LE.le.{0} Real Real.instLE
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) density
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N))
      coefficient)
```

## `ImbalancedChen.eventually_RealB_le_currentK_log_of_same_rho_inputs`

- 所属模块：`ImbalancedChen.RealUpperCountingAssembly`
- 类别：`theorem`；原始 Audit 行：25
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b kappa sieveExponent : Real}
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hb1 : @LT.lt.{0} Real Real.instLT b (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hkappa :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) kappa)
  (hsieve :
    @LT.lt.{0} Real Real.instLT sieveExponent (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (Q : Real → Nat → Finset.{0} Nat) (rho : Real → Nat → Nat → Real)
  (hmajor :
    ∀ (delta : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              ∀ (n : Nat),
                @LE.le.{0} Real Real.instLE
                  (@ite.{1} Real
                    (Nat.Coprime n
                      (ImbalancedChen.sieveProduct N
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@Nat.cast.{0} Real Real.instNatCast N) sieveExponent))))
                    (Nat.instDecidableCoprime n
                      (ImbalancedChen.sieveProduct N
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                            (@Nat.cast.{0} Real Real.instNatCast N) sieveExponent))))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (ImbalancedChen.physicalDivisorSum (Q delta N) (rho delta N) n))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  (hdensity :
    ∀ (delta : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              @LE.le.{0} Real Real.instLE (ImbalancedChen.physicalDensitySum (Q delta N) (rho delta N))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ImbalancedChen.currentK delta)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  (hcoprime :
    ∀ (delta : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              @LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (ImbalancedChen.realPhysicalCoprimeCorrection b N (ImbalancedChen.manuscriptHalfProductCutoff kappa N)
                    (Q delta N) (rho delta N)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                  (ImbalancedChen.singularNormalization N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  (hdistribution :
    ∀ (delta : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
        @Filter.Eventually.{0} Nat
          (fun (N : Nat) =>
            @Even.{0} Nat instAddNat N →
              @LE.le.{0} Real Real.instLE
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (ImbalancedChen.realPhysicalDistributionError b N (ImbalancedChen.manuscriptHalfProductCutoff kappa N)
                    (Q delta N) (rho delta N)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                  (ImbalancedChen.singularNormalization N)))
          (@Filter.atTop.{0} Nat Nat.instPreorder))
  (epsilon : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @Even.{0} Nat instAddNat N →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.RealB b N))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ImbalancedChen.currentK
                  (Real.log
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b)))
                epsilon)
              (ImbalancedChen.singularNormalization N)))
      (@Filter.atTop.{0} Nat Nat.instPreorder)
```

## `ImbalancedChen.exists_actualSmallRoughRho_density_le_currentK_of_full_policy_limits`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：26
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (nu sieveR epsilonMax rawBound : Real)
  (hnu : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) nu)
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) sieveR)
  (hepsilonMax :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonMax)
  (retainOdd : Real → Nat → List.{0} Nat → Bool) (cap : Nat → Nat) (integral : Real → Real)
  (hcap :
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR))
          (@Nat.cast.{0} Real Real.instNatCast (cap N)))
      (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@Filter.principal.{0} Nat
          (@Set.ofPred.{0} Nat fun (N : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
              (@Even.{0} Nat instAddNat N)))))
  (hIntegral :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @LT.lt.{0} Real Real.instLT epsilon epsilonMax →
          @Filter.Tendsto.{0, 0} Nat Real
            (fun (N : Nat) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (ImbalancedChen.reciprocalTotientDensity
                    (ImbalancedChen.fixedRoughSupport (retainOdd epsilon N) N (cap N)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast N)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR)))
                    (ImbalancedChen.fixedRoughCoefficient (retainOdd epsilon N) N (cap N)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast N)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR))))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
                (ImbalancedChen.singularSeries N))
            (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@Filter.principal.{0} Nat
                (@Set.ofPred.{0} Nat fun (N : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
                    (@Even.{0} Nat instAddNat N))))
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (integral epsilon)))
  (hCertificate :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @LT.lt.{0} Real Real.instLT epsilon epsilonMax → @LE.le.{0} Real Real.instLE (integral epsilon) rawBound)
  (hgap : @LT.lt.{0} Real Real.instLT rawBound ImbalancedChen.currentK),
  @Exists.{1} Real fun (epsilon : Real) =>
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon)
      (And
        (@LT.lt.{0} Real Real.instLT epsilon
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 8)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
        (And (@LT.lt.{0} Real Real.instLT epsilon epsilonMax)
          (And
            (@LE.le.{0} Real Real.instLE
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) epsilon
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              sieveR)
            (@Exists.{1} Nat fun (N₀ : Nat) =>
              And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N₀)
                (∀ (N : Nat),
                  @LE.le.{0} Nat instLENat N₀ N →
                    @Even.{0} Nat instAddNat N →
                      have w : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              epsilon (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))));
                      have z : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR);
                      have L : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu epsilon);
                      @LE.le.{0} Real Real.instLE
                        (ImbalancedChen.physicalDensitySum
                          (ImbalancedChen.actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
                          (ImbalancedChen.actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) ImbalancedChen.currentK
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))))))
```

## `ImbalancedChen.exists_actualSmallRoughRho_density_le_of_full_policy_limits`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：27
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (nu sieveR epsilonMax rawBound densityCap : Real)
  (hnu : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) nu)
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) sieveR)
  (hepsilonMax :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilonMax)
  (retainOdd : Real → Nat → List.{0} Nat → Bool) (cap : Nat → Nat) (integral : Real → Real)
  (hcap :
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR))
          (@Nat.cast.{0} Real Real.instNatCast (cap N)))
      (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@Filter.principal.{0} Nat
          (@Set.ofPred.{0} Nat fun (N : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
              (@Even.{0} Nat instAddNat N)))))
  (hIntegral :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @LT.lt.{0} Real Real.instLT epsilon epsilonMax →
          @Filter.Tendsto.{0, 0} Nat Real
            (fun (N : Nat) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (ImbalancedChen.reciprocalTotientDensity
                    (ImbalancedChen.fixedRoughSupport (retainOdd epsilon N) N (cap N)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast N)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR)))
                    (ImbalancedChen.fixedRoughCoefficient (retainOdd epsilon N) N (cap N)
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                        (@Nat.cast.{0} Real Real.instNatCast N)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR))))
                  (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
                (ImbalancedChen.singularSeries N))
            (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
              (@Filter.principal.{0} Nat
                (@Set.ofPred.{0} Nat fun (N : Nat) =>
                  And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
                    (@Even.{0} Nat instAddNat N))))
            (@nhds.{0} Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (integral epsilon)))
  (hCertificate :
    ∀ (epsilon : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
        @LT.lt.{0} Real Real.instLT epsilon epsilonMax → @LE.le.{0} Real Real.instLE (integral epsilon) rawBound)
  (hgap : @LT.lt.{0} Real Real.instLT rawBound densityCap),
  @Exists.{1} Real fun (epsilon : Real) =>
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon)
      (And
        (@LT.lt.{0} Real Real.instLT epsilon
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 8)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
        (And (@LT.lt.{0} Real Real.instLT epsilon epsilonMax)
          (And
            (@LE.le.{0} Real Real.instLE
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) epsilon
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              sieveR)
            (@Exists.{1} Nat fun (N₀ : Nat) =>
              And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N₀)
                (∀ (N : Nat),
                  @LE.le.{0} Nat instLENat N₀ N →
                    @Even.{0} Nat instAddNat N →
                      have w : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              epsilon (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))));
                      have z : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu sieveR);
                      have L : Real :=
                        @HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) nu epsilon);
                      @LE.le.{0} Real Real.instLE
                        (ImbalancedChen.physicalDensitySum
                          (ImbalancedChen.actualSmallRoughModuli (retainOdd epsilon N) N (cap N) w z)
                          (ImbalancedChen.actualSmallRoughRho (retainOdd epsilon N) N (cap N) w z L))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) densityCap
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))))))))
```

## `ImbalancedChen.fifthCappedUpperPolicy_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：28
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (base : Bool → List.{0} Nat → Bool) (Q3 Q5 : List.{0} Nat → Real)
  (hbase : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (base Bool.true pre) Bool.true) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.fifthCappedUpperPolicy base Q3 Q5 Bool.true pre) Bool.true
```

## `ImbalancedChen.firstExitDepthSplicePolicy_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：29
- Universe parameters：`["u_1"]`
- Transitive axioms：`["propext"]`

```lean
∀ {α : Type u_1} (k : Nat) (parent replacement : Bool → List.{u_1} α → Bool)
  (hparent : ∀ (pre : List.{u_1} α), @Eq.{1} Bool (parent Bool.true pre) Bool.true)
  (hreplacement : ∀ (pre : List.{u_1} α), @Eq.{1} Bool (replacement Bool.true pre) Bool.true) (pre : List.{u_1} α),
  @Eq.{1} Bool (@ImbalancedChen.firstExitDepthSplicePolicy.{u_1} α k parent replacement Bool.true pre) Bool.true
```

## `ImbalancedChen.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：30
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retained : Bool → List.{0} Nat → Bool)
  (heven : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (retained Bool.true pre) Bool.true) (N cap : Nat) (w z : Real),
  @Eq.{1} Real
    (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat retained
      (fun (p : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@Nat.cast.{0} Real Real.instNatCast p)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (ImbalancedChen.roughPrimeUniverse N cap w z))
    (ImbalancedChen.reciprocalTotientDensity (ImbalancedChen.fixedRoughSupport (retained Bool.false) N cap w z)
      (ImbalancedChen.fixedRoughCoefficient (retained Bool.false) N cap w z))
```

## `ImbalancedChen.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：31
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retained : Bool → List.{0} Nat → Bool)
  (heven : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (retained Bool.true pre) Bool.true) (N cap : Nat) (w z : Real)
  (d : Nat),
  @Eq.{1} Real (ImbalancedChen.fixedRoughCoefficient (retained Bool.false) N cap w z d)
    (@Int.cast.{0} Real Real.instIntCast
      (ImbalancedChen.firstExitRetainedCoefficient retained (ImbalancedChen.roughPrimeUniverse N cap w z) d))
```

## `ImbalancedChen.fixedRoughDensity_nonneg`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：32
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retainOdd : List.{0} Nat → Bool) (N cap : Nat) (w z : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (ImbalancedChen.reciprocalTotientDensity (ImbalancedChen.fixedRoughSupport retainOdd N cap w z)
      (ImbalancedChen.fixedRoughCoefficient retainOdd N cap w z))
```

## `ImbalancedChen.fixedRoughSupport_dvd_sieveProduct_ceil`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：33
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retainOdd : List.{0} Nat → Bool) (N cap : Nat) (w z : Real) {d : Nat}
  (hd :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.fixedRoughSupport retainOdd N cap w z) d),
  @Dvd.dvd.{0} Nat Nat.instDvd d
    (ImbalancedChen.sieveProduct N
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
```

## `ImbalancedChen.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：34
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (retained : Bool → List.{0} Nat → Bool)
  (heven : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (retained Bool.true pre) Bool.true) (N cap : Nat) (w z : Real),
  @Eq.{1} (Finset.{0} Nat) (ImbalancedChen.fixedRoughSupport (retained Bool.false) N cap w z)
    (ImbalancedChen.firstExitRetainedModuli retained (ImbalancedChen.roughPrimeUniverse N cap w z))
```

## `ImbalancedChen.fourthCappedUpperPolicy_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：35
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (base : Bool → List.{0} Nat → Bool) (Q3 Q4 : List.{0} Nat → Real)
  (hbase : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (base Bool.true pre) Bool.true) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.fourthCappedUpperPolicy base Q3 Q4 Bool.true pre) Bool.true
```

## `ImbalancedChen.mem_realSiftedHalfProductSource`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：36
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N m z : Nat},
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.realSiftedHalfProductSource b N T z) m)
    (And
      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
        (ImbalancedChen.realHalfProductSource b N T) m)
      (Nat.Coprime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)
        (ImbalancedChen.sieveProduct N z)))
```

## `ImbalancedChen.oddFirstExitPolicy_eq_of_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：37
- Universe parameters：`["u_1"]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ {α : Type u_1} (retained : Bool → List.{u_1} α → Bool)
  (heven : ∀ (pre : List.{u_1} α), @Eq.{1} Bool (retained Bool.true pre) Bool.true),
  @Eq.{u_1 + 1} ((positive : Bool) → (selectedPrefix : List.{u_1} α) → Bool)
    (@ImbalancedChen.oddFirstExitPolicy.{u_1} α (retained Bool.false)) retained
```

## `ImbalancedChen.realHalfProductCongruenceMass`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`definition`；原始 Audit 行：38
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
(b : Real) → (N : Nat) → (T : Real) → (d : Nat) → Real
```

## `ImbalancedChen.realHalfProductCoprimeMass`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`definition`；原始 Audit 行：39
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
(b : Real) → (N : Nat) → (T : Real) → (d : Nat) → Real
```

## `ImbalancedChen.realHalfProductCoprimeMass_eq_card_of_gate`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：40
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N z d : Nat}
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hT : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hcap :
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast z)
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) T
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b))))
  (hd : @Dvd.dvd.{0} Nat Nat.instDvd d (ImbalancedChen.sieveProduct N z)),
  @Eq.{1} Real (ImbalancedChen.realHalfProductCoprimeMass b N T d)
    (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
```

## `ImbalancedChen.realHalfProductSource_coprime_of_dvd_sieveProduct`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：41
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N m z d : Nat}
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hT : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hcap :
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast z)
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) T
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b))))
  (hm :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.realHalfProductSource b N T) m)
  (hd : @Dvd.dvd.{0} Nat Nat.instDvd d (ImbalancedChen.sieveProduct N z)), Nat.Coprime m d
```

## `ImbalancedChen.realHalfProductSource_filter_dvd_eq_filter_modEq`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：42
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N d : Nat) (T : Real),
  @Eq.{1} (Finset.{0} Nat)
    (@Finset.filter.{0} Nat
      (fun (m : Nat) =>
        @Dvd.dvd.{0} Nat Nat.instDvd d (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m))
      (fun (a : Nat) => Nat.decidable_dvd d (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N a))
      (ImbalancedChen.realHalfProductSource b N T))
    (@Finset.filter.{0} Nat (fun (m : Nat) => Nat.ModEq d m N) (fun (a : Nat) => @Nat.instDecidableModEq d a N)
      (ImbalancedChen.realHalfProductSource b N T))
```

## `ImbalancedChen.realHalfProductSource_primePartner_card_le_realSifted_add_cap`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：43
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N z : Nat) (T : Real),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat
        (fun (m : Nat) =>
          And (@LT.lt.{0} Nat instLTNat m N)
            (Nat.Prime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)))
        (fun (a : Nat) =>
          @instDecidableAnd (@LT.lt.{0} Nat instLTNat a N)
            (Nat.Prime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N a)) (Nat.decLt a N)
            (Nat.decidablePrime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N a)))
        (ImbalancedChen.realHalfProductSource b N T)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{0} Nat (ImbalancedChen.realSiftedHalfProductSource b N T z)) z)
```

## `ImbalancedChen.realHalfProductSource_prime_divisor_rough`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：44
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N m ell : Nat}
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hT : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hm :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.realHalfProductSource b N T) m)
  (hell : Nat.Prime ell) (hdvd : @Dvd.dvd.{0} Nat Nat.instDvd ell m),
  @LT.lt.{0} Real Real.instLT
    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) T
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b)))
    (@Nat.cast.{0} Real Real.instNatCast ell)
```

## `ImbalancedChen.realPhysicalCoprimeCorrection`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`definition`；原始 Audit 行：45
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
(b : Real) → (N : Nat) → (T : Real) → (Q : Finset.{0} Nat) → (rho : Nat → Real) → Real
```

## `ImbalancedChen.realPhysicalCoprimeCorrection_eq_zero_of_gate`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：46
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N z : Nat} (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hT : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) T)
  (hcap :
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast z)
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) T
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b))))
  (hsupport :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q d →
        @Ne.{1} Real (rho d) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Dvd.dvd.{0} Nat Nat.instDvd d (ImbalancedChen.sieveProduct N z)),
  @Eq.{1} Real (ImbalancedChen.realPhysicalCoprimeCorrection b N T Q rho)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## `ImbalancedChen.realPhysicalDistributionError`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`definition`；原始 Audit 行：47
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
(b : Real) → (N : Nat) → (T : Real) → (Q : Finset.{0} Nat) → (rho : Nat → Real) → Real
```

## `ImbalancedChen.realSiftedHalfProductSource`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`definition`；原始 Audit 行：48
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
(b : Real) → (N : Nat) → (T : Real) → (z : Nat) → Finset.{0} Nat
```

## `ImbalancedChen.realSiftedHalfProductSource_card_le_same_rho_main_add_errors`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：49
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N z : Nat) (T : Real) (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realSiftedHalfProductSource b N T z)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
          (ImbalancedChen.physicalDensitySum Q rho))
        (ImbalancedChen.realPhysicalCoprimeCorrection b N T Q rho))
      (ImbalancedChen.realPhysicalDistributionError b N T Q rho))
```

## `ImbalancedChen.realSiftedHalfProductSource_card_le_sum_physicalDivisorSum`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：50
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N z : Nat) (T : Real) (Q : Finset.{0} Nat) (rho : Nat → Real)
  (hmajor :
    ∀ (n : Nat),
      @LE.le.{0} Real Real.instLE
        (@ite.{1} Real (Nat.Coprime n (ImbalancedChen.sieveProduct N z))
          (Nat.instDecidableCoprime n (ImbalancedChen.sieveProduct N z))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
        (ImbalancedChen.physicalDivisorSum Q rho n)),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realSiftedHalfProductSource b N T z)))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.realHalfProductSource b N T) fun (m : Nat) =>
      ImbalancedChen.physicalDivisorSum Q rho (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m))
```

## `ImbalancedChen.same_rho_normalized_mainTerm`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：51
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat) (mass : Real) (Q : Finset.{0} Nat) (rho : Nat → Real),
  @Eq.{1} Real
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mass
        (ImbalancedChen.physicalDensitySum Q rho))
      (ImbalancedChen.singularNormalization N))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mass
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (@Nat.cast.{0} Real Real.instNatCast N))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (ImbalancedChen.physicalDensitySum Q rho)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N)))
```

## `ImbalancedChen.signSensitiveReciprocalTotientDensity_eq_sum_attached`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：52
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (rough : Finset.{0} Nat) (c : Nat → Real) (lo hi : Real),
  @Eq.{1} Real (ImbalancedChen.signSensitiveReciprocalTotientDensity rough c lo hi)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid rough fun (d : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (ImbalancedChen.signAttachedValue (c d) lo hi) (@Nat.cast.{0} Real Real.instNatCast (Nat.totient d)))
```

## `ImbalancedChen.sourceMassScale_mul_densityScale`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：53
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (ImbalancedChen.singularSeries N) (Real.log (@Nat.cast.{0} Real Real.instNatCast N))))
    (ImbalancedChen.singularNormalization N)
```

## `ImbalancedChen.sum_physicalDivisorSum_realHalfProductSource`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：54
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N : Nat) (T : Real) (Q : Finset.{0} Nat) (rho : Nat → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.realHalfProductSource b N T) fun (m : Nat) =>
      ImbalancedChen.physicalDivisorSum Q rho (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
        (ImbalancedChen.realHalfProductCongruenceMass b N T d))
```

## `ImbalancedChen.sum_rho_mul_realHalfProductCongruenceMass_eq`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：55
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N : Nat) (T : Real) (Q : Finset.{0} Nat) (rho : Nat → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
        (ImbalancedChen.realHalfProductCongruenceMass b N T d))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat (ImbalancedChen.realHalfProductSource b N T)))
          (ImbalancedChen.physicalDensitySum Q rho))
        (ImbalancedChen.realPhysicalCoprimeCorrection b N T Q rho))
      (ImbalancedChen.realPhysicalDistributionError b N T Q rho))
```

## `ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：56
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat) (S Q : Finset.{0} Nat) (weight rho : Nat → Real)
  (hSN :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Nat instLENat m N),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (weight m)
        (ImbalancedChen.physicalDivisorSum Q rho (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)))
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
        (ImbalancedChen.finiteCongruenceMass S weight N d))
```

## `ImbalancedChen.sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：57
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat) (S Q : Finset.{0} Nat) (weight rho : Nat → Real)
  (hSN :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Nat instLENat m N),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (weight m)
        (ImbalancedChen.physicalDivisorSum Q rho (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (ImbalancedChen.finiteSourceMass S weight) (ImbalancedChen.physicalDensitySum Q rho))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (ImbalancedChen.finiteCoprimeMass S weight d) (ImbalancedChen.finiteSourceMass S weight))
              (@Nat.cast.{0} Real Real.instNatCast (Nat.totient d)))))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (d : Nat) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (rho d)
          (ImbalancedChen.finitePrimitiveDiscrepancy S weight N d)))
```

## `ImbalancedChen.supportedDivisorSum_le_of_coefficient_le`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：58
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (rough : Finset.{0} Nat) (raw compiled : Nat → Real)
  (hdom :
    ∀ (d : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) rough d →
        @LE.le.{0} Real Real.instLE (raw d) (compiled d))
  (n : Nat),
  @LE.le.{0} Real Real.instLE (ImbalancedChen.supportedDivisorSum rough raw n)
    (ImbalancedChen.supportedDivisorSum rough compiled n)
```

## `ImbalancedChen.thirdCappedUpperPolicy_even_retained`

- 所属模块：`ImbalancedChen.ActualUpperPolicyDensity`
- 类别：`theorem`；原始 Audit 行：59
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (base : Bool → List.{0} Nat → Bool) (Q3 : List.{0} Nat → Real)
  (hbase : ∀ (pre : List.{0} Nat), @Eq.{1} Bool (base Bool.true pre) Bool.true) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.thirdCappedUpperPolicy base Q3 Bool.true pre) Bool.true
```

## `_private.ImbalancedChen.UpperCoefficientPerturbation.0.ImbalancedChen.abs_mul_sub_mul_le_of_opposite_signs`

- 所属模块：`ImbalancedChen.UpperCoefficientPerturbation`
- 类别：`theorem`；原始 Audit 行：60
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {c d lo hi M : Real}
  (hc : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c)
  (hd : @LE.le.{0} Real Real.instLE d (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hlo : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup lo) M)
  (hhi : @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup hi) M),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c hi)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) d lo)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) M
      (@abs.{0} Real Real.lattice Real.instAddGroup
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) c d)))
```

## `ImbalancedChen.actualSmallRoughIndicator_eq_sieveProduct_natAbs._simp_1_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：61
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ {n m : Nat}, @Eq.{1} Prop (Nat.Coprime n m) (Nat.Coprime m n)
```

## `ImbalancedChen.currentK.eq_1`

- 所属模块：`ImbalancedChen.RealUpperCountingAssembly`
- 类别：`theorem`；原始 Audit 行：62
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
@Eq.{1} Real ImbalancedChen.currentK
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 8452171)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 8452171) Real.instNatCast ImbalancedChen.currentK._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 1250000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 1250000) Real.instNatCast ImbalancedChen.currentK._proof_2)))
```

## `ImbalancedChen.densityScale_pos._proof_1_1`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：63
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N),
  Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) → False
```

## `ImbalancedChen.density_le_manuscriptScale_iff_normalized._proof_1_1`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：64
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ {N : Nat} (hN : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N),
  Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) → False
```

## `ImbalancedChen.eventually_RealB_le_currentK_log_of_same_rho_inputs._proof_1_3`

- 所属模块：`ImbalancedChen.RealUpperCountingAssembly`
- 类别：`theorem`；原始 Audit 行：65
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ (N : Nat)
  (hN :
    @LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N),
  Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) → False
```

## `ImbalancedChen.exists_actualSmallRoughRho_density_le_of_full_policy_limits._proof_1_1`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：66
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ (Nattach Nraw N : Nat)
  (hN2 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N),
  Not (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N) → False
```

## `ImbalancedChen.manuscriptHalfProductCutoff.eq_1`

- 所属模块：`ImbalancedChen.RealUpperCountingAssembly`
- 类别：`theorem`；原始 Audit 行：67
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (κ : Real) (N : Nat),
  @Eq.{1} Real (ImbalancedChen.manuscriptHalfProductCutoff κ N)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          ImbalancedChen.manuscriptHalfProductCutoff._proof_1))
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) κ)))
```

## `ImbalancedChen.mem_realSiftedHalfProductSource._simp_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：68
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ {b T : Real} {N m z : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.realSiftedHalfProductSource b N T z) m)
    (And
      (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
        (ImbalancedChen.realHalfProductSource b N T) m)
      (Nat.Coprime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)
        (ImbalancedChen.sieveProduct N z)))
```

## `ImbalancedChen.mem_realSiftedHalfProductSource._simp_1_2`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：69
- Universe parameters：`["u_1"]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

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

## `ImbalancedChen.realHalfProductCoprimeMass.eq_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：70
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N : Nat) (T : Real) (d : Nat),
  @Eq.{1} Real (ImbalancedChen.realHalfProductCoprimeMass b N T d)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} Nat
        (@Finset.filter.{0} Nat (fun (m : Nat) => Nat.Coprime m d) (fun (a : Nat) => Nat.instDecidableCoprime a d)
          (ImbalancedChen.realHalfProductSource b N T))))
```

## `ImbalancedChen.realHalfProductSource_primePartner_card_le_realSifted_add_cap._proof_1_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：71
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Quot.sound"]`

```lean
∀ (N : Nat) ⦃m n : Nat⦄ (hmN : @LT.lt.{0} Nat instLTNat m N) (hnN : @LT.lt.{0} Nat instLTNat n N)
  (hmn :
    @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N n)),
  Not (@Eq.{1} Nat m n) → False
```

## `ImbalancedChen.realSiftedHalfProductSource.eq_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：72
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (b : Real) (N : Nat) (T : Real) (z : Nat),
  @Eq.{1} (Finset.{0} Nat) (ImbalancedChen.realSiftedHalfProductSource b N T z)
    (@Finset.filter.{0} Nat
      (fun (m : Nat) =>
        Nat.Coprime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N m)
          (ImbalancedChen.sieveProduct N z))
      (fun (a : Nat) =>
        Nat.instDecidableCoprime (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N a)
          (ImbalancedChen.sieveProduct N z))
      (ImbalancedChen.realHalfProductSource b N T))
```

## `ImbalancedChen.sieveProduct.eq_1`

- 所属模块：`ImbalancedChen.RealPhysicalUpperWeightBridge`
- 类别：`theorem`；原始 Audit 行：73
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N z : Nat),
  @Eq.{1} Nat (ImbalancedChen.sieveProduct N z)
    (@Finset.prod.{0, 0} Nat Nat Nat.instCommMonoid (ImbalancedChen.sievePrimes N z) fun (ell : Nat) => ell)
```

## `ImbalancedChen.singularNormalization.eq_1`

- 所属模块：`ImbalancedChen.ActualUpperDensityAssembly`
- 类别：`theorem`；原始 Audit 行：74
- Universe parameters：`[]`
- Transitive axioms：`["propext", "Classical.choice", "Quot.sound"]`

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.singularNormalization N)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (ImbalancedChen.singularSeries N)
        (@Nat.cast.{0} Real Real.instNatCast N))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (Real.log (@Nat.cast.{0} Real Real.instNatCast N))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```
