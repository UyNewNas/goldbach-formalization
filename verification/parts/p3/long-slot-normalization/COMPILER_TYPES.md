# 编译器确认的完整类型

来源：成功的 defining-module 审计；不是源码正则提取。

## ImbalancedChen.part3_eventually_longSlot_logAccuracy

```lean
∀ (theta : ℝ),
  LT.lt.{0} theta 1 →
    ∀ (K : ℕ) (epsilon : ℝ),
      LT.lt.{0} 0 epsilon →
        ∀ᶠ (N : ℕ) in Filter.atTop.{0},
          ∀ (M D L U a : ℕ) (alpha rho : ℕ → ℂ),
            LE.le.{0} (HMul.hMul.{0, 0, 0} ↑M ↑D) (HPow.hPow.{0, 0, 0} (↑N) theta) →
              (∀ (m : ℕ), Membership.mem.{0, 0} (Finset.Icc.{0} 1 M) m → LE.le.{0} (Norm.norm.{0} (alpha m)) 1) →
                (∀ (q : ℕ),
                    Membership.mem.{0, 0} ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) q →
                      LE.le.{0} (Norm.norm.{0} (rho q)) 1) →
                  LE.le.{0}
                    (Norm.norm.{0}
                      (ImbalancedChen.part3LongSlotSignedError (Finset.Icc.{0} 1 M)
                        ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) alpha rho L U a))
                    (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} epsilon ↑N) (HPow.hPow.{0, 0, 0} (Real.log ↑N) K))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

<details>
<summary>完整 pp.all 输出</summary>

```lean
∀ (theta : Real)
  (htheta : @LT.lt.{0} Real Real.instLT theta (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (K : Nat) (epsilon : Real)
  (hepsilon :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon),
  @Filter.Eventually.{0} Nat
    (fun (N : Nat) =>
      ∀ (M D L U a : Nat) (alpha rho : Nat → Complex),
        @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast M) (@Nat.cast.{0} Real Real.instNatCast D))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N) theta) →
          (∀ (m : Nat),
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                  m →
                @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (alpha m))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (∀ (q : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    q →
                  @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (rho q))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              @LE.le.{0} Real Real.instLE
                (@Norm.norm.{0} Complex Complex.instNorm
                  (ImbalancedChen.part3LongSlotSignedError
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    alpha rho L U a))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                    (@Nat.cast.{0} Real Real.instNatCast N))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast N)) K)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
```

</details>

## ImbalancedChen.part3_eventually_longSlot_singularNormalization

```lean
∀ (theta : ℝ),
  LT.lt.{0} theta 1 →
    ∀ (epsilon : ℝ),
      LT.lt.{0} 0 epsilon →
        ∀ᶠ (N : ℕ) in Filter.atTop.{0},
          ∀ (M D L U a : ℕ) (alpha rho : ℕ → ℂ),
            LE.le.{0} (HMul.hMul.{0, 0, 0} ↑M ↑D) (HPow.hPow.{0, 0, 0} (↑N) theta) →
              (∀ (m : ℕ), Membership.mem.{0, 0} (Finset.Icc.{0} 1 M) m → LE.le.{0} (Norm.norm.{0} (alpha m)) 1) →
                (∀ (q : ℕ),
                    Membership.mem.{0, 0} ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) q →
                      LE.le.{0} (Norm.norm.{0} (rho q)) 1) →
                  LE.le.{0}
                    (Norm.norm.{0}
                      (ImbalancedChen.part3LongSlotSignedError (Finset.Icc.{0} 1 M)
                        ({q ∈ Finset.Icc.{0} 1 D | a.Coprime q}) alpha rho L U a))
                    (HMul.hMul.{0, 0, 0} epsilon (ImbalancedChen.singularNormalization N))
```

传递公理：`propext`, `Classical.choice`, `Quot.sound`。

<details>
<summary>完整 pp.all 输出</summary>

```lean
∀ (theta : Real)
  (htheta : @LT.lt.{0} Real Real.instLT theta (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (epsilon : Real)
  (hepsilon :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon),
  @Filter.Eventually.{0} Nat
    (fun (N : Nat) =>
      ∀ (M D L U a : Nat) (alpha rho : Nat → Complex),
        @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast M) (@Nat.cast.{0} Real Real.instNatCast D))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N) theta) →
          (∀ (m : Nat),
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                  m →
                @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (alpha m))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (∀ (q : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    q →
                  @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (rho q))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              @LE.le.{0} Real Real.instLE
                (@Norm.norm.{0} Complex Complex.instNorm
                  (ImbalancedChen.part3LongSlotSignedError
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    alpha rho L U a))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                  (ImbalancedChen.singularNormalization N)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
```

</details>

