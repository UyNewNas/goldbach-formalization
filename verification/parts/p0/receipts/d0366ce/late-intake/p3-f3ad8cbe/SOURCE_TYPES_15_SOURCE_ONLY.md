# P3 固定候选的 15 个完整源码声明头

**SOURCE_HEADERS_ONLY_NOT_COMPILER_TYPES。** 13 个 theorem、2 个 def；编译器确认类型 0。没有私有/自动生成声明审计，因此 15 不是完整所属声明数的上限。

交接 `f3ad8cbe43c61c903857c7411626ee8c56f4f2f9`；源码 `ImbalancedChen/Part3PrimeAPDistribution.lean`；SHA256 `55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`。

原源码名称解析上下文：

```lean
namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
```

## ImbalancedChen.part3_chenPrimeAPCount_eq_primesInAP

源码第 30 行，源码提取。

```lean
theorem part3_chenPrimeAPCount_eq_primesInAP (Y a d : ℕ) :
    chenPrimeAPCount Y a d = (primesInAP Y d a : ℝ)
```

## ImbalancedChen.part3PrimeAPError

源码第 36 行，源码提取。

```lean
def part3PrimeAPError (Y a d : ℕ) : ℝ
```

## ImbalancedChen.part3PrimeAPError_eq_standard

源码第 39 行，源码提取。

```lean
theorem part3PrimeAPError_eq_standard (Y a d : ℕ) :
    part3PrimeAPError Y a d = standardPrimeAPError Y d (a % d)
```

## ImbalancedChen.part3PrimeAPError_target_eq_chenQuotientPrimeAPError

源码第 44 行，源码提取。

```lean
theorem part3PrimeAPError_target_eq_chenQuotientPrimeAPError (N d : ℕ) :
    part3PrimeAPError N N d =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d
```

## ImbalancedChen.part3_standardPrimeAPMaxError_le_prefix

源码第 50 行，源码提取。

```lean
theorem part3_standardPrimeAPMaxError_le_prefix
    {N Y d : ℕ} (hY : Y ≤ N) :
    standardPrimeAPMaxError Y d ≤ standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_primeAPError_le_prefix

源码第 60 行，源码提取。

```lean
theorem part3_abs_primeAPError_le_prefix
    {N Y a d : ℕ} (hY : Y ≤ N) (hd : 0 < d) (ha : Nat.Coprime a d) :
    |part3PrimeAPError Y a d| ≤ standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_chenQuotientPrimeAPError_le_prefix

源码第 72 行，源码提取。

```lean
theorem part3_abs_chenQuotientPrimeAPError_le_prefix
    {N d : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d| ≤
      standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_sum_abs_primeAPError_le_prefix

源码第 81 行，源码提取。

```lean
theorem part3_sum_abs_primeAPError_le_prefix
    (N D : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (Y : ℕ) (hY : Y ≤ N) (a : ℕ → ℕ)
    (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
      ∑ d ∈ Finset.Icc 1 D, standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_sum_mul_primeAPError_le_sum_abs

源码第 98 行，源码提取。

```lean
theorem part3_abs_sum_mul_primeAPError_le_sum_abs
    (S : Finset ℕ) (Y : ℕ) (a : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
      ∑ d ∈ S, |part3PrimeAPError Y (a d) d|
```

## ImbalancedChen.part3_sum_abs_primeAPError_log_saving

源码第 113 行，源码提取。

```lean
theorem part3_sum_abs_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## ImbalancedChen.part3_abs_sum_mul_primeAPError_log_saving

源码第 136 行，源码提取。

```lean
theorem part3_abs_sum_mul_primeAPError_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Q →
          ∀ Y : ℕ, Y ≤ N → ∀ a : ℕ → ℕ,
            (∀ d ∈ S, Nat.Coprime (a d) d) →
            ∀ w : ℕ → ℝ, (∀ d ∈ S, |w d| ≤ 1) →
            |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
              C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

## ImbalancedChen.part3PrimeAPIntervalError

源码第 154 行，源码提取。

```lean
def part3PrimeAPIntervalError (L U a d : ℕ) : ℝ
```

## ImbalancedChen.part3PrimeAPIntervalError_eq_sub

源码第 158 行，源码提取。

```lean
theorem part3PrimeAPIntervalError_eq_sub (L U a d : ℕ) :
    part3PrimeAPIntervalError L U a d =
      part3PrimeAPError U a d - part3PrimeAPError L a d
```

## ImbalancedChen.part3_abs_sum_mul_primeAPIntervalError_log_saving

源码第 166 行，源码提取。

```lean
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
```

## ImbalancedChen.part3_chenQuotientPrimeAPError_pool_log_saving

源码第 188 行，源码提取。

```lean
theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A
```
