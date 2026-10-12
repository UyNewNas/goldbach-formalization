# 已接受 P2 producer 的完整 pp.all 原文

来源为 f0c00f9ccce98e04af439321a92eb9fd0dd26203 的生产源码及已接受生产记录，
并与 e6d6d57323cc358cef060fb243ec386c13cb662d 的实际 P2 CI 原始 audit 记录相同。
本文件不是 d0366ce 新 core 类型导出。五份 .txt 保留各 type 字段的 UTF-8 原字节，不另添换行。

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_semantics

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) Real
      Real.instAddCommMonoid
      (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) =>
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
                (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix64.rowZ i))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uUpper
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tUpper
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices i))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

原始传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_bounds

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix64.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix64.integral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.Prefix64.integral
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix64.upperBound))
```

原始传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix64.integral_eq_parts

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix64.integral
  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
    ImbalancedChen.Certificates.PairedV2.Prefix4.integral ImbalancedChen.Certificates.PairedV2.Batch4To64.integral)
```

原始传递公理：`propext`, `Classical.choice`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix64.source_ordinal_coverage

```lean
∀ (n : Nat),
  Iff
    (Or
      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @Eq.{1} Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal i) n)
      (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))) =>
        @Eq.{1} Nat (ImbalancedChen.Certificates.PairedV2.Batch4To64.rowOrdinal i) n))
    (@LT.lt.{0} Nat instLTNat n (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
```

原始传递公理：`propext`, `Quot.sound`。

## ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices_injective

```lean
@Function.Injective.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) (Prod.{0, 0} Nat Nat)
  ImbalancedChen.Certificates.PairedV2.Prefix64.rowIndices
```

原始传递公理：`propext`, `Classical.choice`, `Quot.sound`。

