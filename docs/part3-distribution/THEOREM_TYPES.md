# Part 3 完整 source theorem types

以下逐字提取本 Part 六个证明候选模块的全部 theorem signatures，含 private 辅助定理。旧四个模块的命名空间为 `ImbalancedChen`；两个 rough SW 模块为 `ImbalancedChen.Part3`。每节保留所需的 open 声明。此清单是 SOURCE_EXTRACTED_NOT_ELABORATED，不是 Lean 的 `#print` 输出；编译器确认类型清单为空。正常环境的 audit 会另输出逐声明完整类型。

实际误差对象的定义应与相应模块一起阅读；最后一节附上全部未闭合分布目标的数据与定义。

## Part3PrimeAPDistribution

[完整证明候选](../../ImbalancedChen/Part3PrimeAPDistribution.lean)

```lean
import ImbalancedChen.Part3PrimeAPDistribution

namespace ImbalancedChen

open Filter Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

theorem part3_chenPrimeAPCount_eq_primesInAP (Y a d : ℕ) :
    chenPrimeAPCount Y a d = (primesInAP Y d a : ℝ)

theorem part3PrimeAPError_eq_standard (Y a d : ℕ) :
    part3PrimeAPError Y a d = standardPrimeAPError Y d (a % d)

theorem part3PrimeAPError_target_eq_chenQuotientPrimeAPError (N d : ℕ) :
    part3PrimeAPError N N d =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d

theorem part3_standardPrimeAPMaxError_le_prefix
    {N Y d : ℕ} (hY : Y ≤ N) :
    standardPrimeAPMaxError Y d ≤ standardPrimeAPPrefixMaxError N d

theorem part3_abs_primeAPError_le_prefix
    {N Y a d : ℕ} (hY : Y ≤ N) (hd : 0 < d) (ha : Nat.Coprime a d) :
    |part3PrimeAPError Y a d| ≤ standardPrimeAPPrefixMaxError N d

theorem part3_abs_chenQuotientPrimeAPError_le_prefix
    {N d : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d| ≤
      standardPrimeAPPrefixMaxError N d

theorem part3_sum_abs_primeAPError_le_prefix
    (N D : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (Y : ℕ) (hY : Y ≤ N) (a : ℕ → ℕ)
    (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
      ∑ d ∈ Finset.Icc 1 D, standardPrimeAPPrefixMaxError N d

theorem part3_abs_sum_mul_primeAPError_le_sum_abs
    (S : Finset ℕ) (Y : ℕ) (a : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
      ∑ d ∈ S, |part3PrimeAPError Y (a d) d|

theorem part3_sum_abs_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A

theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A

theorem part3PrimeAPIntervalError_eq_sub (L U a d : ℕ) :
    part3PrimeAPIntervalError L U a d =
      part3PrimeAPError U a d - part3PrimeAPError L a d

theorem part3_abs_sum_mul_primeAPIntervalError_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ L U : ℕ, L ≤ U → U ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPIntervalError L U (a d) d| ≤
              2 * (C * (N : ℝ) / Real.log (N : ℝ) ^ A)

theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A

end ImbalancedChen
```

## Part3CurrentLowerDistribution

[完整证明候选](../../ImbalancedChen/Part3CurrentLowerDistribution.lean)

```lean
import ImbalancedChen.Part3CurrentLowerDistribution

namespace ImbalancedChen

open Filter Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

theorem part3CurrentLowerAPError_le_four_pool (N Q : ℕ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerAPError N S3 S4 S5 S6 ≤
      4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|)

theorem part3_currentLowerAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerAPError N S3 S4 S5 S6 ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A

theorem part3_quotientRemainder_log_saving_add_centre
    {α : Type*} (accuracy : ℝ) (haccuracy : 0 < accuracy) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ A : ℝ, ∀ T : Finset α, ∀ b : α → ℕ, ∀ S : α → Finset ℕ,
          ∀ hN : Even N,
          ∀ hbpos : ∀ t ∈ T, 0 < b t,
          ∀ hbN : ∀ t ∈ T, Nat.Coprime (b t) N,
          ∀ hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)),
          Set.InjOn b (T : Set α) → ChenQuotientRows N A Q T b S →
          (∑ t ∈ T.attach, ∑ e ∈ S t.val,
            |(chenQuotientBoundingSieve N (b t.val) A hN (hb t.val t.property)).rem e|) ≤
            (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
              (C * (N : ℝ) / Real.log (N : ℝ) ^ accuracy) +
                chenSelectedCentreCost N T b S

theorem part3CurrentLowerRemainderSum_le_primitive_log_add_cost
    (N Q : ℕ) (hN : Even N) (M : ℝ)
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
      4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k|) +
            part3CurrentLowerCentreCost N S3 S4 S5 S6

theorem part3CurrentLowerCentreCost_le_sqrt_log_cube {N Q : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt (N : ℝ))
    (S3 S4 : ℕ → Finset ℕ) (S5 S6 : (ℕ × ℕ) → Finset ℕ)
    (hrows : Part3CurrentLowerRows N Q S3 S4 S5 S6) :
    part3CurrentLowerCentreCost N S3 S4 S5 S6 ≤
      (8 / (Real.log 2) ^ 3) * (N : ℝ) ^ (1 / 2 : ℝ) *
        (Real.log (N : ℝ)) ^ 3

private theorem part3_panModulusCutoff_le_sqrt (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (panModulusCutoff N B : ℝ) ≤ Real.sqrt (N : ℝ)

theorem part3_currentLowerRemainder_negligible :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ hN : Even N,
        ∀ S3 S4 : ℕ → Finset ℕ, ∀ S5 S6 : (ℕ × ℕ) → Finset ℕ,
          Part3CurrentLowerRows N Q S3 S4 S5 S6 →
          part3CurrentLowerRemainderSum N hN S3 S4 S5 S6 ≤
            epsilon * singularNormalization N

end ImbalancedChen
```

## Part3LongSlotDistribution

[完整证明候选](../../ImbalancedChen/Part3LongSlotDistribution.lean)

```lean
import ImbalancedChen.Part3LongSlotDistribution

namespace ImbalancedChen

open Filter Classical Finset
open scoped BigOperators

private theorem part3_prefix_count_le_add_one (U q a b : ℕ) (hq : 0 < q) :
    U.count (fun n => n ≡ a [MOD q]) ≤
      U.count (fun n => n ≡ b [MOD q]) + 1

private theorem part3_Ico_filter_card_sub (L U : ℕ) (hLU : L ≤ U)
    (P : ℕ → Prop) [DecidablePred P] :
    ((Ico L U).filter P).card = U.count P - L.count P

theorem part3IntervalAPCount_le_add_two (L U q a b : ℕ) (hq : 0 < q) :
    part3IntervalAPCount L U q a ≤ part3IntervalAPCount L U q b + 2

theorem part3IntervalAPCount_abs_sub_le_two (L U q a b : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) - part3IntervalAPCount L U q b| ≤ 2

theorem part3IntervalCoprimeCount_eq_sum (L U q : ℕ) (hq : 0 < q) :
    part3IntervalCoprimeCount L U q =
      ∑ a ∈ (range q).filter (fun a => q.Coprime a), part3IntervalAPCount L U q a

theorem part3IntervalAPCount_coprimeMean_error (L U q a : ℕ) (hq : 0 < q) :
    |(part3IntervalAPCount L U q a : ℝ) -
      (part3IntervalCoprimeCount L U q : ℝ) / q.totient| ≤ 2

theorem part3LongSlotRemainder_eq_zero_of_not_coprime (L U q a m : ℕ)
    (ha : a.Coprime q) (hm : ¬m.Coprime q) :
    part3LongSlotRemainder L U q a m = 0

theorem part3LongSlotRemainder_abs_le_two (L U q a m : ℕ)
    (hq : 0 < q) (ha : a.Coprime q) :
    |part3LongSlotRemainder L U q a m| ≤ 2

theorem part3LongSlotSignedError_norm_le (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (∑ m ∈ S, ‖α m‖) * (∑ q ∈ Q, ‖ρ q‖)

theorem part3LongSlotSignedError_norm_le_of_mass (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (M D : ℝ) (hq : ∀ q ∈ Q, 0 < q)
    (ha : ∀ q ∈ Q, a.Coprime q)
    (hM : (∑ m ∈ S, ‖α m‖) ≤ M) (hD : (∑ q ∈ Q, ‖ρ q‖) ≤ D) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤ 2 * M * D

theorem part3LongSlotSignedError_norm_le_card (S Q : Finset ℕ) (α ρ : ℕ → ℂ)
    (L U a : ℕ) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q)
    (hα : ∀ m ∈ S, ‖α m‖ ≤ 1) (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError S Q α ρ L U a‖ ≤
      2 * (S.card : ℝ) * (Q.card : ℝ)

theorem part3LongSlotSignedError_norm_le_box (M D L U a : ℕ) (α ρ : ℕ → ℂ)
    (hα : ∀ m ∈ Icc 1 M, ‖α m‖ ≤ 1)
    (hρ : ∀ q ∈ (Icc 1 D).filter (fun q => a.Coprime q), ‖ρ q‖ ≤ 1) :
    ‖part3LongSlotSignedError (Icc 1 M)
      ((Icc 1 D).filter (fun q => a.Coprime q)) α ρ L U a‖ ≤
      2 * (M : ℝ) * (D : ℝ)

end ImbalancedChen
```

## Part3LongSlotNormalization

[完整证明候选](../../ImbalancedChen/Part3LongSlotNormalization.lean)

```lean
import ImbalancedChen.Part3LongSlotNormalization

namespace ImbalancedChen

open Filter Classical Finset
open scoped BigOperators

theorem part3_eventually_longSlot_logAccuracy
    (theta : ℝ) (htheta : theta < 1) (K : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K

theorem part3_eventually_longSlot_singularNormalization
    (theta : ℝ) (htheta : theta < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ M D L U a : ℕ, ∀ alpha rho : ℕ → ℂ,
      (M : ℝ) * (D : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ m ∈ Finset.Icc 1 M, ‖alpha m‖ ≤ 1) →
      (∀ q ∈ (Finset.Icc 1 D).filter (fun q => a.Coprime q), ‖rho q‖ ≤ 1) →
      ‖part3LongSlotSignedError (Finset.Icc 1 M)
        ((Finset.Icc 1 D).filter (fun q => a.Coprime q)) alpha rho L U a‖ ≤
          epsilon * singularNormalization N

end ImbalancedChen
```

## Part3RoughAuxiliarySW

[完整证明候选](../../ImbalancedChen/Part3RoughAuxiliarySW.lean)

状态：SOURCE_EXTRACTED_NOT_ELABORATED。

```lean
import ImbalancedChen.Part3RoughAuxiliarySW

namespace ImbalancedChen.Part3

open Classical Finset
open scoped BigOperators

theorem MediumAtom.auxSWError_eq_auxiliarySWError (d : MediumAtom) (k q b : ℕ) :
    d.auxSWError k q b = auxiliarySWError d.alphaCarrier d.alpha k q b

private theorem norm_sum_ite_and_not_coprime_le
    (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ‖∑ n ∈ S, if P n ∧ ¬Nat.Coprime n k then α n else 0‖ ≤
      ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖

theorem auxiliarySWError_sub_one_norm_le_bad_mass
    (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) (hq : 0 < q) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖)

theorem sum_norm_not_coprime_le_rough
    (S : Finset ℕ) (α : ℕ → ℂ) (H k : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) ≤
      (k.primeFactors.card : ℝ) * (H : ℝ) / z

theorem auxiliarySWError_sub_one_norm_le_primeFactors
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.primeFactors.card : ℝ) * (H : ℝ) / z

theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z

theorem auxiliarySWError_norm_le_one_add
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b‖ ≤ ‖auxiliarySWError S α 1 q b‖ +
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z

theorem roughOneSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughOneSlot z n‖ ≤ 1

theorem roughOneSlot_support (z : ℝ) (n : ℕ) (hn : roughOneSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)

theorem roughMoebiusSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughMoebiusSlot z n‖ ≤ 1

theorem roughMoebiusSlot_support (z : ℝ) (n : ℕ) (hn : roughMoebiusSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)

theorem roughOneSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughOneSlot z) k q b -
      auxiliarySWError S (roughOneSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z

theorem roughMoebiusSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughMoebiusSlot z) k q b -
      auxiliarySWError S (roughMoebiusSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z

theorem auxiliarySWError_sub_one_norm_le_mellin
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z t : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) k q b -
      auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z

private theorem card_filter_modEq_le_prefix
    (S : Finset ℕ) (H q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H) (hq : 0 < q) :
    ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) ≤ (H : ℝ) / q + 2

theorem auxiliarySWError_norm_le_large_modulus
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 H) (hH : 3 ≤ H) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1) :
    ‖auxiliarySWError S α k q b‖ ≤ (H : ℝ) / q + 2 +
      (H : ℝ) * MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
        Real.log (H : ℝ) / (min q H : ℕ)

end ImbalancedChen.Part3
```

## Part3RoughAuxiliarySWNormalization

[完整证明候选](../../ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean)

状态：SOURCE_EXTRACTED_NOT_ELABORATED。

```lean
import ImbalancedChen.Part3RoughAuxiliarySWNormalization

namespace ImbalancedChen.Part3

open Filter Topology
open scoped BigOperators

theorem tendsto_logLog_four_div_log :
    Tendsto (fun x : ℝ => (Real.log (Real.log x)) ^ 4 / Real.log x)
      atTop (𝓝 0)

theorem eventually_log_rpow_le_roughCutoff (B : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ B ≤ x ^ (1 / (Real.log (Real.log x)) ^ 3)

theorem eventually_roughCutoff_inv_logAccuracy
    (A c epsilon : ℝ) (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      c / x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤
        epsilon / (Real.log x) ^ A

theorem MediumAtom.alphaCarrier_subset_Ioc (d : MediumAtom) (hU : 0 < d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U))

theorem MediumAtom.auxSWError_sub_one_norm_le
    (d : MediumAtom) (z : ℝ) (hU : 0 < d.U) (hz : 0 < z)
    (hα : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (hrough : ∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n → z < (p : ℝ))
    (k q b : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
      4 * d.U * (k.divisors.card : ℝ) / z

theorem exists_medium_auxSWError_sub_one_logAccuracy
    (A epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      0 < d.U →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
        Nat.Prime p → p ∣ n →
          d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) →
      ∀ k q b : ℕ, 1 ≤ k → 1 ≤ q →
        ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
          epsilon * d.U * (k.divisors.card : ℝ) / (Real.log d.scale) ^ A

theorem uniformAuxiliarySW_of_rough_one
    {ι : Type*} (F : ι → MediumAtom)
    (hU : ∀ i, 0 < (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1

theorem eventually_const_mul_log_rpow_le_rpow
    (c A xi : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, c * (Real.log x) ^ A ≤ x ^ xi

theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A

theorem exists_medium_auxSW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      d.scale ^ xi ≤ d.U → 1 ≤ d.V →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      ∀ k q b : ℕ, (Real.log d.scale) ^ (A + 2) ≤ (q : ℝ) →
        ‖d.auxSWError k q b‖ ≤ epsilon * d.U / (Real.log d.scale) ^ A

theorem uniformAuxiliarySW_of_rough_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (xi : ℝ) (hxi : 0 < xi)
    (hU : ∀ i, 1 ≤ (F i).U) (hV : ∀ i, 1 ≤ (F i).V)
    (hUlow : ∀ i, (F i).scale ^ xi ≤ (F i).U)
    (hα : ∀ i, ∀ n ∈ (F i).alphaCarrier, ‖(F i).alpha n‖ ≤ 1)
    (hrough : ∀ i, ∀ n ∈ (F i).alphaCarrier, (F i).alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n →
        (F i).scale ^ (1 / (Real.log (Real.log (F i).scale)) ^ 3) < (p : ℝ))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1

theorem MediumAdmissible.alphaScaleLower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma < d.U

theorem uniformAuxiliarySW_of_mediumAdmissible_small_moduli
    {ι : Type*} (F : ι → MediumAtom) (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ q b : ℕ,
        1 ≤ q → (q : ℝ) < (Real.log (F i).scale) ^ (A + 2) →
        Nat.Coprime b q →
        ‖(F i).auxSWError 1 q b‖ ≤
          C * (F i).U / (Real.log (F i).scale) ^ A) :
    UniformAuxiliarySW F 1

end ImbalancedChen.Part3
```

## 新增 rough SW 的实际算术定义

```lean
namespace ImbalancedChen.Part3

open scoped BigOperators

def auxiliarySWError (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) : ℂ :=
  (∑ n ∈ S, if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0) -
  (∑ n ∈ S, if Nat.Coprime n (k * q) then α n else 0) / (Nat.totient q : ℂ)

def roughOneSlot (z : ℝ) (n : ℕ) : ℂ := by
  classical
  exact if ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ) then 1 else 0

def roughMoebiusSlot (z : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) * roughOneSlot z n

end ImbalancedChen.Part3
```

这些是实际系数／误差定义，未包含待证的 SW 或 dispersion 字段。小模数剩余 SW 完整印在上述条件定理的 `hSW` 参数中。

## 未闭合目标与实际算术定义

以下是 `Part3DistributionTargets.lean` 的原样内容。`RestrictedMediumObligation` 与 `UniformPrimeProductTarget` 都仅是 `Prop` 的定义，不是存在其证明的断言。后者只固定实际误差结论；未为任意 `W` 宣称几何合法性。

```lean
import ImbalancedChen.RestrictedResidueScale
import Mathlib.Analysis.Complex.Exponential

/-!
# Literal, deliberately unproved Part 3 distribution obligations

The frozen source is `chen-imbalanced-semiprimes` at
`ba6ec11d800eccc54406490631895e174de85766`, Proposition
`prop:current-medium` and equation `eq:current-PP`.

These definitions record obligations; none is an axiom or a theorem asserting
the missing estimate.  In particular a proof for each fixed atom with its own
constant does not prove `RestrictedMediumTarget`.  Auxiliary SW constants and
the final threshold are chosen before the members of the family.

The interval and coefficient functions belong to one atom, before any modulus
is summed.  They cannot depend on a modulus or a spectral height.  The common
completed interval and additive phase in the spectral proof are a further
missing proof obligation, not a claimed consequence of the ordinary BV API.
The latter has no nonzero additive phase parameter.

The physical integer modulus is the product `q1*q2*q3`.  The three auxiliary
factor lengths are kept separately; their ranges cannot be substituted for a
physical square-root cutoff.  Signs stay inside the one final norm.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical

/-- One local convolution, with one interval and fixed coefficients shared
by every term of the modulus sum.  The residue may move with the atom. -/
structure MediumAtom where
  U V Q1 Q2 Q3 : ℝ
  residue : ℤ
  intervalLo intervalHi : ℝ
  alpha beta gamma1 gamma2 gamma3 : ℕ → ℂ

def MediumAtom.scale (d : MediumAtom) : ℝ := d.U * d.V

def MediumAtom.alphaCarrier (d : MediumAtom) : Finset ℕ :=
  (Finset.Icc (Nat.ceil d.U) (Nat.floor (2 * d.U))).filter
    (fun n => d.intervalLo < (n : ℝ) ∧ (n : ℝ) ≤ d.intervalHi)

def MediumAtom.betaCarrier (d : MediumAtom) : Finset ℕ :=
  Finset.Icc (Nat.ceil d.V) (Nat.floor (2 * d.V))

/-- Concrete dyadic support `Q ≤ q ≤ 2Q`, including the trivial factor
`q=1` at `Q=1`. The manuscript writes `q ≍ Q`; the compiler must assign
overlapping endpoints without multiplicity loss when it chooses its atoms. -/
def factorCarrier (Q : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.ceil Q) (Nat.floor (2 * Q))

/-- The returned variable has ONE interval and ONE phase, shared by all
levels. There is deliberately no level-indexed interval or phase field. -/
structure CommonCompletedVariable where
  intervalLo intervalHi : ℕ
  additivePhase : ℝ

def CommonCompletedVariable.weight (d : CommonCompletedVariable) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ico d.intervalLo d.intervalHi then
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d.additivePhase : ℂ) * (m : ℂ))
  else 0

/-- The ABL transformed coefficient has no spectral-height argument.
The coprimality of the packet level and moving residue remains required. -/
structure CoprimePacket where
  residue level multiplier : ℕ
  level_pos : 0 < level
  residue_coprime : Nat.Coprime residue level
  beta : ℕ → ℕ → ℂ

def CoprimePacket.transformedCoefficient (d : CoprimePacket) (n : ℕ) : ℂ :=
  if Nat.Coprime n d.residue then
    d.beta (d.multiplier * n) d.level *
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (d.level : ℂ))
  else 0

/-- Auxiliary-coprimality SW error on the *same* alpha interval. -/
def MediumAtom.auxSWError (d : MediumAtom) (k q b : ℕ) : ℂ :=
  (∑ n ∈ d.alphaCarrier,
    if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0) -
  (∑ n ∈ d.alphaCarrier,
    if Nat.Coprime n (k * q) then d.alpha n else 0) / (Nat.totient q : ℂ)

/-- Family constants precede the varying atom, interval, auxiliary factor,
modulus and reduced residue.  The divisor order `C0` is fixed once. -/
def UniformAuxiliarySW {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale → ∀ k q b : ℕ,
      1 ≤ k → 1 ≤ q → Nat.Coprime b q →
      ‖(F i).auxSWError k q b‖ ≤
        C * (F i).U * ((k.divisors.card : ℝ) ^ C0) /
          (Real.log (F i).scale) ^ A

/-- The literal primitive-coprime mean, without replacing it by total mass. -/
def MediumAtom.discrepancy (d : MediumAtom) (q : ℕ) : ℂ :=
  ∑ n ∈ d.alphaCarrier, ∑ m ∈ d.betaCarrier,
    d.alpha n * d.beta m *
      ((if (((n * m : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ))
          then (1 : ℂ) else 0) -
        (if Nat.Coprime (n * m) q then (1 : ℂ) else 0) / (Nat.totient q : ℂ))

def MediumAtom.signedError (d : MediumAtom) : ℂ :=
  ∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 * d.discrepancy (q1 * q2 * q3)

/-- Precisely the geometric and coefficient gates of the frozen restricted
medium proposition.  `scale` is the complete convolution product. -/
def MediumAdmissible (B : ℕ) (σ κ c0 : ℝ) (d : MediumAtom) : Prop :=
  1 ≤ d.U ∧ 1 ≤ d.V ∧ 1 ≤ d.Q1 ∧ 1 ≤ d.Q2 ∧ 1 ≤ d.Q3 ∧
  Real.exp (Real.exp 1) < d.scale ∧
  c0 * d.scale ≤ (d.residue.natAbs : ℝ) ∧
  (d.residue.natAbs : ℝ) ≤ d.scale ^ (1 + κ) ∧
  d.Q1 < d.U * d.scale ^ (-σ) ∧
  d.U ^ 2 * d.Q2 * d.Q3 ^ 2 < d.scale ^ (1 - 8 * σ) ∧
  (d.residue.natAbs : ℝ) ^ (7 / 32 : ℝ) * d.U * d.Q1 * d.Q2 ^ 5 * d.Q3 ^ 2 <
    d.scale ^ (2 - 15 * σ) ∧
  d.U ^ (1 + 2 * (7 / 32 : ℝ)) * d.Q1 *
      d.Q2 ^ (5 - 2 * (7 / 32 : ℝ)) * d.Q3 ^ (2 + 2 * (7 / 32 : ℝ)) <
    d.scale ^ (2 - 15 * σ) ∧
  (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) ∧
  (∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
    Nat.Prime p → p ∣ n →
      d.scale ^ (1 / (Real.log (Real.log d.scale)) ^ 3) < (p : ℝ)) ∧
  (∀ m ∈ d.betaCarrier, ‖d.beta m‖ ≤ (m.divisors.card : ℝ) ^ B) ∧
  (∀ q ∈ factorCarrier d.Q1, ‖d.gamma1 q‖ ≤ 1 ∧
    (d.gamma1 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q2, ‖d.gamma2 q‖ ≤ 1 ∧
    (d.gamma2 q ≠ 0 → Nat.Coprime q d.residue.natAbs)) ∧
  (∀ q ∈ factorCarrier d.Q3, ‖d.gamma3 q‖ ≤ 1 ∧
    (d.gamma3 q ≠ 0 → Nat.Coprime q d.residue.natAbs))

/-- Missing uniform signed medium estimate.  This proposition is not proved
by the low-rank BV or one-long integer-slot results in this Part. -/
def RestrictedMediumTarget {ι : Type*} (F : ι → MediumAtom) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ≤ C * (F i).scale / (Real.log (F i).scale) ^ A

/-- Exact unclosed theorem type, including the fixed family SW constants. -/
def RestrictedMediumObligation {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (σ κ c0 : ℝ) : Prop :=
  0 < σ → σ < 1 / 100 → 0 < c0 → 0 ≤ κ → κ ≤ σ / 100 →
  (∀ i : ι, MediumAdmissible B σ κ c0 (F i)) →
  UniformAuxiliarySW F C0 → RestrictedMediumTarget F

/-- Labelled prime tuples, retaining repeated primes and their slot order. -/
def labelledPrimeTuples (k P : ℕ) : Finset (Fin k → Fin (P + 1)) :=
  Finset.univ.filter (fun t => ∀ i : Fin k, Nat.Prime (t i).val)

def labelledProduct {k P : ℕ} (t : Fin k → Fin (P + 1)) : ℕ :=
  ∏ i : Fin k, (t i).val

/-- The exact `eq:current-PP` error for a finite labelled source.  Geometric
licensing is not asserted for arbitrary `W`.  There is no additive-prime
filter hidden in its source; that filter is recovered by the physical sieve. -/
def primeProductSignedError (k P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    (∑ t ∈ labelledPrimeTuples k P, W t *
      ((if Nat.ModEq q (labelledProduct t) N then (1 : ℝ) else 0) -
        (if Nat.Coprime (labelledProduct t) q then (1 : ℝ) else 0) /
          (Nat.totient q : ℝ)))

/-- The raw conclusion of the missing actual upper/lower source supplier.
This is NOT a claim that arbitrary `W` is a licensed geometric family.
A concrete caller fixes its
policy, prime rank and licensed geometric family before invoking this type.
One threshold covers every family member at each target. -/
def UniformPrimeProductTarget {ι : Type*} (k : ℕ) (cap : ℕ → ℕ)
    (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (W : (N : ℕ) → ι → (Fin k → Fin (cap N + 1)) → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → Even N → ∀ i : ι,
      |primeProductSignedError k (cap N) N (Q N) (rho N) (W N i)| ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ A

end

end ImbalancedChen.Part3
```
