# Part3PrimeAPDistribution：源码声明头

**状态：SOURCE_EXTRACTION_NOT_COMPILER_TYPES。** 严格编译被第一个缺失导入对象阻塞，以下是固定生产源码的完整声明头，不是编译器 `#print` 输出。没有完成任何本模块声明的公理审计；13 个 theorem 和 2 个 def 的源码计数不是未来 private/generated 审计的上限。

源码 SHA256：`55319b7e1150799a5bd2ed4bcc0ef3dd486de57409d9b859f678c068bcb8c7fc`。

这些声明位于 `namespace ImbalancedChen`，依赖原模块中的 `open Filter`、`open scoped BigOperators`、`open MathlibNt.SieveTheory.BombieriVinogradov` 和 `open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)`。生产源码保持字节不变。

## ImbalancedChen.part3_chenPrimeAPCount_eq_primesInAP

源码第 30 行。

```lean
theorem part3_chenPrimeAPCount_eq_primesInAP (Y a d : ℕ) :
    chenPrimeAPCount Y a d = (primesInAP Y d a : ℝ)
```

## ImbalancedChen.part3PrimeAPError

源码第 36 行。

```lean
def part3PrimeAPError (Y a d : ℕ) : ℝ
```

## ImbalancedChen.part3PrimeAPError_eq_standard

源码第 39 行。

```lean
theorem part3PrimeAPError_eq_standard (Y a d : ℕ) :
    part3PrimeAPError Y a d = standardPrimeAPError Y d (a % d)
```

## ImbalancedChen.part3PrimeAPError_target_eq_chenQuotientPrimeAPError

源码第 44 行。

```lean
theorem part3PrimeAPError_target_eq_chenQuotientPrimeAPError (N d : ℕ) :
    part3PrimeAPError N N d =
      chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d
```

## ImbalancedChen.part3_standardPrimeAPMaxError_le_prefix

源码第 50 行。

```lean
theorem part3_standardPrimeAPMaxError_le_prefix
    {N Y d : ℕ} (hY : Y ≤ N) :
    standardPrimeAPMaxError Y d ≤ standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_primeAPError_le_prefix

源码第 60 行。

```lean
theorem part3_abs_primeAPError_le_prefix
    {N Y a d : ℕ} (hY : Y ≤ N) (hd : 0 < d) (ha : Nat.Coprime a d) :
    |part3PrimeAPError Y a d| ≤ standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_chenQuotientPrimeAPError_le_prefix

源码第 72 行。

```lean
theorem part3_abs_chenQuotientPrimeAPError_le_prefix
    {N d : ℕ} (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) d| ≤
      standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_sum_abs_primeAPError_le_prefix

源码第 81 行。

```lean
theorem part3_sum_abs_primeAPError_le_prefix
    (N D : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D)
    (Y : ℕ) (hY : Y ≤ N) (a : ℕ → ℕ)
    (ha : ∀ d ∈ S, Nat.Coprime (a d) d) :
    (∑ d ∈ S, |part3PrimeAPError Y (a d) d|) ≤
      ∑ d ∈ Finset.Icc 1 D, standardPrimeAPPrefixMaxError N d
```

## ImbalancedChen.part3_abs_sum_mul_primeAPError_le_sum_abs

源码第 98 行。

```lean
theorem part3_abs_sum_mul_primeAPError_le_sum_abs
    (S : Finset ℕ) (Y : ℕ) (a : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ S, |w d| ≤ 1) :
    |∑ d ∈ S, w d * part3PrimeAPError Y (a d) d| ≤
      ∑ d ∈ S, |part3PrimeAPError Y (a d) d|
```

## ImbalancedChen.part3_sum_abs_primeAPError_log_saving

源码第 113 行。

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

源码第 136 行。

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

源码第 154 行。

```lean
def part3PrimeAPIntervalError (L U a d : ℕ) : ℝ
```

## ImbalancedChen.part3PrimeAPIntervalError_eq_sub

源码第 158 行。

```lean
theorem part3PrimeAPIntervalError_eq_sub (L U a d : ℕ) :
    part3PrimeAPIntervalError L U a d =
      part3PrimeAPError U a d - part3PrimeAPError L a d
```

## ImbalancedChen.part3_abs_sum_mul_primeAPIntervalError_log_saving

源码第 166 行。

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

源码第 188 行。

```lean
theorem part3_chenQuotientPrimeAPError_pool_log_saving
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ A
```

