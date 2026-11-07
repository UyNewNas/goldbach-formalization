# P3 7d70 rough SW 两模块源码定理头

固定源码 SHA：7d70a2545fd819706e473eb41e4d430ad19119d8。

SOURCE_EXTRACTED_NOT_COMPILER_CONFIRMED。共 29 个 theorem 声明头，其中两个 private；本清单不含 elaborator 生成声明，不是 Lean #print 或公理审计。

## MediumAtom.auxSWError_eq_auxiliarySWError

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 43。

```lean
theorem MediumAtom.auxSWError_eq_auxiliarySWError (d : MediumAtom) (k q b : ℕ) :
    d.auxSWError k q b = auxiliarySWError d.alphaCarrier d.alpha k q b
```

## norm_sum_ite_and_not_coprime_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 47。

```lean
private theorem norm_sum_ite_and_not_coprime_le
    (S : Finset ℕ) (α : ℕ → ℂ) (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ‖∑ n ∈ S, if P n ∧ ¬Nat.Coprime n k then α n else 0‖ ≤
      ∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖
```

## auxiliarySWError_sub_one_norm_le_bad_mass

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 60。

```lean
theorem auxiliarySWError_sub_one_norm_le_bad_mass
    (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) (hq : 0 < q) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖)
```

## sum_norm_not_coprime_le_rough

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 111。

```lean
theorem sum_norm_not_coprime_le_rough
    (S : Finset ℕ) (α : ℕ → ℂ) (H k : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    (∑ n ∈ S with ¬Nat.Coprime n k, ‖α n‖) ≤
      (k.primeFactors.card : ℝ) * (H : ℝ) / z
```

## auxiliarySWError_sub_one_norm_le_primeFactors

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 168。

```lean
theorem auxiliarySWError_sub_one_norm_le_primeFactors
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.primeFactors.card : ℝ) * (H : ℝ) / z
```

## auxiliarySWError_sub_one_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 186。

```lean
theorem auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b - auxiliarySWError S α 1 q b‖ ≤
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## auxiliarySWError_norm_le_one_add

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 206。

```lean
theorem auxiliarySWError_norm_le_one_add
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S α k q b‖ ≤ ‖auxiliarySWError S α 1 q b‖ +
      2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## roughOneSlot_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 233。

```lean
theorem roughOneSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughOneSlot z n‖ ≤ 1
```

## roughOneSlot_support

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 237。

```lean
theorem roughOneSlot_support (z : ℝ) (n : ℕ) (hn : roughOneSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)
```

## roughMoebiusSlot_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 242。

```lean
theorem roughMoebiusSlot_norm_le (z : ℝ) (n : ℕ) : ‖roughMoebiusSlot z n‖ ≤ 1
```

## roughMoebiusSlot_support

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 251。

```lean
theorem roughMoebiusSlot_support (z : ℝ) (n : ℕ) (hn : roughMoebiusSlot z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)
```

## roughOneSlot_auxiliarySWError_sub_one_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 258。

```lean
theorem roughOneSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughOneSlot z) k q b -
      auxiliarySWError S (roughOneSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## roughMoebiusSlot_auxiliarySWError_sub_one_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 267。

```lean
theorem roughMoebiusSlot_auxiliarySWError_sub_one_norm_le
    (S : Finset ℕ) (H k q b : ℕ) (z : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q) :
    ‖auxiliarySWError S (roughMoebiusSlot z) k q b -
      auxiliarySWError S (roughMoebiusSlot z) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## auxiliarySWError_sub_one_norm_le_mellin

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 280。

```lean
theorem auxiliarySWError_sub_one_norm_le_mellin
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ) (z t : ℝ)
    (hS : S ⊆ Finset.Ioc 0 H) (hz : 0 < z) (hk : 0 < k) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1)
    (hrough : ∀ n ∈ S, α n ≠ 0 → ∀ p : ℕ,
      p.Prime → p ∣ n → z < (p : ℝ)) :
    ‖auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) k q b -
      auxiliarySWError S (fun n => α n * (n : ℂ) ^ (Complex.I * (t : ℂ))) 1 q b‖ ≤
        2 * (k.divisors.card : ℝ) * (H : ℝ) / z
```

## card_filter_modEq_le_prefix

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 301。

```lean
private theorem card_filter_modEq_le_prefix
    (S : Finset ℕ) (H q b : ℕ) (hS : S ⊆ Finset.Ioc 0 H) (hq : 0 < q) :
    ((S.filter (fun n => Nat.ModEq q n b)).card : ℝ) ≤ (H : ℝ) / q + 2
```

## auxiliarySWError_norm_le_large_modulus

来源：p3/ImbalancedChen/Part3RoughAuxiliarySW.lean，源码行 332。

```lean
theorem auxiliarySWError_norm_le_large_modulus
    (S : Finset ℕ) (α : ℕ → ℂ) (H k q b : ℕ)
    (hS : S ⊆ Finset.Ioc 0 H) (hH : 3 ≤ H) (hq : 0 < q)
    (hα : ∀ n ∈ S, ‖α n‖ ≤ 1) :
    ‖auxiliarySWError S α k q b‖ ≤ (H : ℝ) / q + 2 +
      (H : ℝ) * MathlibNt.SieveTheory.Richert1969.richertReciprocalTotientConstant *
        Real.log (H : ℝ) / (min q H : ℕ)
```

## tendsto_logLog_four_div_log

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 31。

```lean
theorem tendsto_logLog_four_div_log :
    Tendsto (fun x : ℝ => (Real.log (Real.log x)) ^ 4 / Real.log x)
      atTop (𝓝 0)
```

## eventually_log_rpow_le_roughCutoff

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 41。

```lean
theorem eventually_log_rpow_le_roughCutoff (B : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ B ≤ x ^ (1 / (Real.log (Real.log x)) ^ 3)
```

## eventually_roughCutoff_inv_logAccuracy

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 72。

```lean
theorem eventually_roughCutoff_inv_logAccuracy
    (A c epsilon : ℝ) (hc : 0 ≤ c) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      c / x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤
        epsilon / (Real.log x) ^ A
```

## MediumAtom.alphaCarrier_subset_Ioc

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 100。

```lean
theorem MediumAtom.alphaCarrier_subset_Ioc (d : MediumAtom) (hU : 0 < d.U) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U))
```

## MediumAtom.auxSWError_sub_one_norm_le

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 109。

```lean
theorem MediumAtom.auxSWError_sub_one_norm_le
    (d : MediumAtom) (z : ℝ) (hU : 0 < d.U) (hz : 0 < z)
    (hα : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1)
    (hrough : ∀ n ∈ d.alphaCarrier, d.alpha n ≠ 0 → ∀ p : ℕ,
      Nat.Prime p → p ∣ n → z < (p : ℝ))
    (k q b : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    ‖d.auxSWError k q b - d.auxSWError 1 q b‖ ≤
      4 * d.U * (k.divisors.card : ℝ) / z
```

## exists_medium_auxSWError_sub_one_logAccuracy

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 133。

```lean
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
```

## uniformAuxiliarySW_of_rough_one

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 168。

```lean
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
```

## eventually_const_mul_log_rpow_le_rpow

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 221。

```lean
theorem eventually_const_mul_log_rpow_le_rpow
    (c A xi : ℝ) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, c * (Real.log x) ^ A ≤ x ^ xi
```

## eventually_auxiliarySW_large_modulus_logAccuracy

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 241。

```lean
theorem eventually_auxiliarySW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∀ᶠ x : ℝ in atTop, ∀ H k q b : ℕ, ∀ S : Finset ℕ, ∀ α : ℕ → ℂ,
      S ⊆ Finset.Ioc 0 H → x ^ xi ≤ (H : ℝ) → (H : ℝ) ≤ 2 * x →
      (Real.log x) ^ (A + 2) ≤ (q : ℝ) →
      (∀ n ∈ S, ‖α n‖ ≤ 1) →
      ‖auxiliarySWError S α k q b‖ ≤
        epsilon * (H : ℝ) / (Real.log x) ^ A
```

## exists_medium_auxSW_large_modulus_logAccuracy

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 324。

```lean
theorem exists_medium_auxSW_large_modulus_logAccuracy
    (A epsilon xi : ℝ) (hepsilon : 0 < epsilon) (hxi : 0 < xi) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom, x0 ≤ d.scale →
      d.scale ^ xi ≤ d.U → 1 ≤ d.V →
      (∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1) →
      ∀ k q b : ℕ, (Real.log d.scale) ^ (A + 2) ≤ (q : ℝ) →
        ‖d.auxSWError k q b‖ ≤ epsilon * d.U / (Real.log d.scale) ^ A
```

## uniformAuxiliarySW_of_rough_small_moduli

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 365。

```lean
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
```

## MediumAdmissible.alphaScaleLower

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 407。

```lean
theorem MediumAdmissible.alphaScaleLower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.scale ^ sigma < d.U
```

## uniformAuxiliarySW_of_mediumAdmissible_small_moduli

来源：p3/ImbalancedChen/Part3RoughAuxiliarySWNormalization.lean，源码行 424。

```lean
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
```
