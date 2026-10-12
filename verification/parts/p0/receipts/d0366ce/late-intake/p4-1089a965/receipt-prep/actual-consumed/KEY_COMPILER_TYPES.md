# 从失败运行的已完成 Audit 原始输出提取的完整编译器类型

源 SHA：`1089a965e20664e63ffd51e0105c11befa406a1f`；run `38288356713`；artifact `11768093422`。

**73 项均为实际编译器打印类型，不是源码声明头。** 对应 Audit strict stage exit 0；`pp.all=true`、`pp.privateNames=true`，并记录 universe parameters。全部原始 `PART4_UPPER_AUDIT_DECL`、五模块 count 和总计 73 均存在。

原始日志 member：`run-1791828370977599814/axioms-and-types.log`；SHA-256：`e2c2d23216027005e6ec65794abaa565c964c65d0d3f74df30689f131b2dca86`。

CI 最终失败于后续 aggregate fresh timeout；最终 source/object/binary 重查未完成。此为 P0 派生保存的已完成阶段输出，不是成功封存回执，也不是生产者尚未生成的四个导出文件。

## 本文件范围

下列 8 个关键公开声明逐字保存实际完整 pp.all 类型。其 `hIntegral`、`hCertificate`、compiler budget 和 same-rho 四输入仍是参数；本 Audit 不含 CurrentMainTheorem，不能把其最终入口另称本次已审计。

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
