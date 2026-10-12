# P5 第三批固定源码：完整关键类型

固定交接：`bf54caeb5e708474cacefac13a171d307b4c64f2`。下列类型按实际编译器记录或固定源码分别标记；不将默认打印的省略号改写为完整类型。

## InitialSource：编译器确认类型

8 个所属声明均已在生产者 audit 中枚举。其旧审计记录缺少导入对象前后身份；P0 是否正式接收须另依本批接收标准。

```lean
ImbalancedChen.currentChen_goldbachS1_le_sifted_add_primeFactors :
∀ (N : ℕ) (tau A z : ℝ),
  N ≠ 0 →
    0 ≤ tau →
      A ≤ z →
        ↑(MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau) N z) ≤
          ↑(ImbalancedChen.chenSiftedPrimeSource N A).card + ↑N.primeFactors.card
```

```lean
ImbalancedChen.currentChen_initial_sieve_coefficient :
33 / 2 * Real.exp (-Real.eulerMascheroniConstant) *
    MathlibNt.SieveTheory.SwitchingPrinciple.dimensionOneLowerLinearSieveFactor 4 =
  33 / 4 * Real.log 3
```

```lean
ImbalancedChen.currentChen_singularSeries_eq_liuSingularSeries :
∀ (N : ℕ), ImbalancedChen.singularSeries N = MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N
```

```lean
ImbalancedChen.currentChen_twinPrimeConstant_eq_liuUniversalProduct :
ImbalancedChen.twinPrimeConstant = MathlibNt.SieveTheory.SingularSeries.liuUniversalProduct
```

```lean
ImbalancedChen.eventually_currentChen_primeFactors_negligible :
∀ (epsilon : ℝ),
  0 < epsilon → ∀ᶠ (N : ℕ) in Filter.atTop, ↑N.primeFactors.card ≤ epsilon * ImbalancedChen.singularNormalization N
```

```lean
ImbalancedChen.currentChen_goldbachS1_le_sifted_add_primeFactors._proof_1_1 :
∀ (N : ℕ) (tau A z : ℝ),
  {n ∈
            Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau) |
          ¬n.Coprime N}.card ≤
      N.primeFactors.card →
    {n ∈
              Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
                (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau) |
            n.Coprime N}.card ≤
        (ImbalancedChen.chenSiftedPrimeSource N A).card →
      {n ∈
                  Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
                    (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau) |
                n.Coprime N}.card +
            {a ∈
                  Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
                    (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau) |
                ¬a.Coprime N}.card =
          (Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau)).card →
        ¬(Finset.filter (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N 1 z)
                  (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N tau)).card ≤
              (ImbalancedChen.chenSiftedPrimeSource N A).card + N.primeFactors.card →
          False
```

```lean
ImbalancedChen.eventually_currentChen_primeFactors_negligible._proof_1_1 :
∀ (N : ℕ), 1 ≤ N → N = 0 → False
```

```lean
ImbalancedChen.singularSeries.eq_1 :
∀ (N : ℕ),
  ImbalancedChen.singularSeries N =
    ImbalancedChen.twinPrimeConstant * ∏ p ∈ ImbalancedChen.oddPrimeDivisors N, (↑p - 1) / (↑p - 2)
```

## S1Carrier：17 个完整公开编译器类型

36 个所属声明的公理审计已通过；其中 2 个生成声明的默认类型有 `⋯`。本节仅称 17 个公开类型完整，另存其精确 Expr。

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.mem_goldbachS1SiftingPrimes_iff :
∀ {N : Nat} {z : Real} {p : Nat},
  Iff
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1SiftingPrimes N z) p)
    (And
      (@LT.lt.{0} Nat instLTNat p
        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) z))
      (And (Nat.Prime p) (Not (@Dvd.dvd.{0} Nat Nat.instDvd p N))))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes_squarefree :
∀ (N : Nat) (z : Real),
  @Squarefree.{0} Nat Nat.instMonoid (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z)
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes_ne_zero :
∀ (N : Nat) (z : Real),
  @Ne.{1} Nat (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes_primeFactors :
∀ (N : Nat) (z : Real),
  @Eq.{1} (Finset.{0} Nat) (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).primeFactors
    (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1SiftingPrimes N z)
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.prime_dvd_goldbachS1ProdPrimes_iff :
∀ {N : Nat} {z : Real} {p : Nat},
  Nat.Prime p →
    Iff
      (@Dvd.dvd.{0} Nat Nat.instDvd p (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z))
      (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast p) z)
        (Not (@Dvd.dvd.{0} Nat Nat.instDvd p N)))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes_coprime_N :
∀ (N : Nat) (z : Real), (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).Coprime N
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_dvd_prodPrimes_coprime_N :
∀ {N d : Nat} {z : Real},
  @Dvd.dvd.{0} Nat Nat.instDvd d (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) →
    d.Coprime N
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint_le :
∀ (N : Nat) {ε : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) N
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint_add_one :
∀ {N : Nat} {ε : Real},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) ε)
          (@Nat.cast.{0} Real Real.instNatCast N)))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.mem_goldbachPrimeCarrier_iff_prime_le_goldbachS1Endpoint :
∀ {N p : Nat} {ε : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      Iff
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachPrimeCarrier N ε) p)
        (And (Nat.Prime p)
          (@LE.le.{0} Nat instLENat p (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε)))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_coprime_prodPrimes_iff_literalHPoint :
∀ (N : Nat) (z : Real) (n : Nat),
  Iff ((MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).Coprime n)
    (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.literalHPoint N
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) z n)
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_mod_mem_unitResidues :
∀ {N d : Nat} {z : Real},
  @Dvd.dvd.{0} Nat Nat.instDvd d (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (AnalyticNumberTheory.Sieve.unitResidues d) (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) N d)
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_multSum_eq_primesInAP :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real} {d : Nat},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      @Eq.{1} Real
        (@BoundingSieve.multSum
          (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) d)
        (@Nat.cast.{0} Real Real.instNatCast
          (MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) d
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) N d)))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_siftedSum_eq :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) (ε z : Real),
  @Eq.{1} Real
    (@BoundingSieve.siftedSum
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z))
    (@Int.cast.{0} Real Real.instIntCast
      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N ε) N z))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_nu_eq_inv_totient :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real} {d : Nat},
  @Dvd.dvd.{0} Nat Nat.instDvd d (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) →
    @Eq.{1} Real
      (@DFunLike.coe.{1, 1, 1} (@ArithmeticFunction.{0} Real Real.instZero) Nat (fun x => Real)
        (@ArithmeticFunction.instFunLikeNat.{0} Real Real.instZero)
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z).nu d)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@Nat.cast.{0} Real Real.instNatCast d.totient))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_mainSum_eq_totientSum :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) (ε z : Real) (μ : Nat → Real),
  @Eq.{1} Real
    (@BoundingSieve.mainSum (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z)
      μ)
    (∑ d ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).divisors,
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (μ d) (@Nat.cast.{0} Real Real.instNatCast d.totient))
```

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_rem_eq_standardPrimeAPError :
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      ∀ {d : Nat},
        @Dvd.dvd.{0} Nat Nat.instDvd d
            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) →
          @Eq.{1} Real
            (@BoundingSieve.rem
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) d)
            (MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPError
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) d
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) N d))
```

## InitialMean 及其直接供应者：源码提取，未编译

```lean
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N
```

```lean
theorem goldbachS1_beta_fixed_normalized_lower
    (s δ : ℝ) (hs4 : 4 ≤ s) (hslt : s < (33 / 8 : ℝ)) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - ε) *
              dimensionOneLowerLinearSieveFactor s - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (goldbachS1 (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ))
```
