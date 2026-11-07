# P5 S1LowerRosser：两个公开接口的完整编译器类型

固定交接提交：`7b1283e4a70874e4fb7004bafad0793069bdea71`。下列文字逐项来自实际成功审计日志，P0 只读核对了原始日志与 JSON 的逐字段相等。

打印格式为默认 `Meta.ppExpr`、启用 `pp.explicit / pp.universes / pp.fullNames / pp.proofs` 的实际完整输出，并有 `type_expr_repr` 原始表达式。**这不是 `pp.all` 输出。** 两个公开类型均无省略；全 8 项记录的 1 个 generated 默认类型有省略，但其 explicit 和 Expr 完整。全量原始 Expr 见 `COMPILER_TYPES_8.json`。

## MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve_lowerErrSum_le_prefixSum

### 编译器默认可读完整类型

```lean
∀ {N : ℕ} (hEven : Even N) {ε z : ℝ},
  0 ≤ ε →
    2 ≤ MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε →
      ∀ {D Q0 : ℕ},
        D ≤ Q0 + 1 →
          MathlibNt.SieveTheory.LinearSieve.lowerErrSum
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) D
              (MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D) ≤
            ∑ q ∈ Finset.Icc 1 Q0, MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q
```

### 同次编译器 explicit 完整类型

```lean
∀ {N : Nat} (hEven : @Even.{0} Nat instAddNat N) {ε z : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
      ∀ {D Q0 : Nat},
        @LE.le.{0} Nat instLENat D
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          @LE.le.{0} Real Real.instLE
            (MathlibNt.SieveTheory.LinearSieve.lowerErrSum
              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1BoundingSieve N hEven ε z) D
              (MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D))
            (∑
              q ∈
                @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Q0,
              MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q)
```

传递公理：`propext, Classical.choice, Quot.sound`。

## MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_lowerRosser_mainTerm_sub_prefix_le

### 编译器默认可读完整类型

```lean
∀ {N : ℕ} {ε z : ℝ},
  0 < ε →
    ε < 1 →
      Even N →
        2 ≤ MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε →
          2 ≤ z →
            ∀ {D Q0 : ℕ},
              (∀ p ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).primeFactors,
                  p < D) →
                D ≤ Q0 + 1 →
                  MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
                          ↑(MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) *
                        ∑ d ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).divisors,
                          MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D d /
                            ↑d.totient -
                      ∑ q ∈ Finset.Icc 1 Q0,
                        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q ≤
                    ↑(MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
                        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N ε) N z)
```

### 同次编译器 explicit 完整类型

```lean
∀ {N : Nat} {ε z : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ε →
    @LT.lt.{0} Real Real.instLT ε (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @Even.{0} Nat instAddNat N →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε) →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              z →
            ∀ {D Q0 : Nat},
              (∀ (p : Nat),
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).primeFactors p →
                    @LT.lt.{0} Nat instLTNat p D) →
                @LE.le.{0} Nat instLENat D
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q0
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  @LE.le.{0} Real Real.instLE
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral
                          (@Nat.cast.{0} Real Real.instNatCast
                            (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1Endpoint N ε)))
                        (∑
                          d ∈ (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z).divisors,
                          @HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (MathlibNt.SieveTheory.LinearSieve.lowerRosserWeight
                              (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1ProdPrimes N z) D d)
                            (@Nat.cast.{0} Real Real.instNatCast d.totient)))
                      (∑
                        q ∈
                          @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) Q0,
                        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q))
                    (@Int.cast.{0} Real Real.instIntCast
                      (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1
                        (MathlibNt.SieveTheory.LiLiuOnePlusOneNine.goldbachDifferenceCarrier N ε) N z))
```

传递公理：`propext, Classical.choice, Quot.sound`。

## 下一供应节点：仅源码提取，未编译候选

固定 goldbach pin `09b97db5764ade1246bfb77206baa1b124760958` 的 `LiLiuGoldbachS1MainMass.lean`，SHA256 `4fdcdd6001278a1c7636a40ba8f2e2e6c685a20331a4b0c803c0146f516a4533`。本次通过固定上游 API 独立读取并匹配源码哈希；没有执行该模块。

```lean
theorem goldbachS1_strictEndpoint_mainMass_lower (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let m : ℕ := ⌈(1 - ε) * (N : ℝ)⌉₊ - 1
      2 ≤ m ∧ m ≤ N ∧
        (1 - ε - η) * ((N : ℝ) / Real.log (N : ℝ)) ≤
          BombieriVinogradov.trueLogarithmicIntegral (m : ℝ)
```
