import ImbalancedChen.SingularSeries
import ImbalancedChen.BadSourceLocalization
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The actual logarithmic cutoff has negligible localization cost

The manuscript's fixed cutoff is `T(N) = N / (log N)^10`. Its ratio to
`N / (log N)^2` is the reciprocal eighth power of the logarithm, which tends
to zero by mathlib's logarithm, power, and reciprocal limit theorems.

The genuine singular series is uniformly bounded below by the strictly
positive `twinPrimeConstant`. Consequently `T(N)` is eventually smaller
than any positive multiple of `singularNormalization N`. The already proved
divergence of that normalization absorbs the additional ceiling error `1`.

Composing this analytic estimate with the exact finite source localization
bounds the original `B`, with its additive-prime restriction intact. The
retained receiver cutoff is exactly `Nat.ceil (logCutoff N)`, equivalently
the literal real inequality `logCutoff N ≤ m`. No prime-counting estimate,
distribution hypothesis, assumed growth statement, or sieve bound is used.

The limit APIs used here were checked against mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`:
`Real.tendsto_log_atTop`, `Filter.tendsto_pow_atTop`, and
`Filter.Tendsto.const_div_atTop`.
-/

namespace ImbalancedChen

open Filter Topology

/-- The manuscript's fixed tenth-logarithm cutoff, as a real number. -/
noncomputable def logCutoff (N : ℕ) : ℝ :=
  (N : ℝ) / (Real.log (N : ℝ)) ^ 10

/-- The totalized cutoff is nonnegative, including at `N = 0` and `N = 1`. -/
theorem logCutoff_nonneg (N : ℕ) : 0 ≤ logCutoff N := by
  unfold logCutoff
  apply div_nonneg (Nat.cast_nonneg N)
  calc
    0 ≤ ((Real.log (N : ℝ)) ^ 5) ^ 2 := sq_nonneg _
    _ = (Real.log (N : ℝ)) ^ 10 := by ring

/-- Genuine logarithmic decay on natural arguments; no counting premise. -/
theorem tendsto_one_div_nat_log_pow_eight :
    Tendsto (fun N : ℕ => 1 / (Real.log (N : ℝ)) ^ 8) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 8) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).comp hlog
  exact hpow.const_div_atTop 1

/-- The actual cutoff is negligible relative to the actual singular-series
normalization. The positive lower constant is proved in `SingularSeries`. -/
theorem eventually_logCutoff_le_singularNormalization :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, logCutoff N ≤ epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hsmall : ∀ᶠ N : ℕ in atTop,
      1 / (Real.log (N : ℝ)) ^ 8 < epsilon * twinPrimeConstant :=
    tendsto_one_div_nat_log_pow_eight.eventually
      (gt_mem_nhds (mul_pos hepsilon twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNreal)
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  calc
    logCutoff N = (1 / (Real.log (N : ℝ)) ^ 8) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      unfold logCutoff
      field_simp [hlog] <;> ring
    _ ≤ (epsilon * twinPrimeConstant) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon *
        (twinPrimeConstant * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
    _ ≤ epsilon * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) hepsilon.le

/-- The exact localization cost `T(N) + 1` is absorbed by any positive
multiple of `H(N)`. The unit is absorbed using the proved divergence of `H`. -/
theorem eventually_logCutoff_add_one_le_singularNormalization :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        logCutoff N + 1 ≤ epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_logCutoff_le_singularNormalization (epsilon / 2) (half_pos hepsilon),
      eventually_singularNormalization_unit_absorption (epsilon / 2) (half_pos hepsilon)]
    with N hcut hunit
  linarith

/-- At the literal real cutoff, the discarded actual-source count has
arbitrarily small normalized cost, including the exact ceiling correction. -/
theorem eventually_smallBadReceivers_logCutoff_card_le
    (num den : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        ((smallBadReceiversReal num den N (logCutoff N)).card : ℝ) ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_logCutoff_add_one_le_singularNormalization epsilon hepsilon]
    with N herror
  exact (smallBadReceiversReal_card_lt num den N (logCutoff_nonneg N)).le.trans herror

/-- Analytic localization of the manuscript's original bad count. The retained
source still imposes that the original additive partner `N - m` is prime. -/
theorem eventually_B_cast_le_retained_logCutoff_add_error
    (num den : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (B num den N : ℝ) ≤
          (retainedBadReceiversReal num den N (logCutoff N)).card +
            epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_logCutoff_add_one_le_singularNormalization epsilon hepsilon]
    with N herror
  exact (B_cast_le_retainedBadReceiversReal_card_add_cutoff num den N
    (logCutoff_nonneg N)).trans (add_le_add le_rfl herror)

/-- The same bound with the precise natural ceiling and the literal formula
for `T(N)` displayed, so the retained source cannot be rounded down. -/
theorem eventually_B_cast_le_retained_logCutoff_ceil_add_error
    (num den : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (B num den N : ℝ) ≤
          (retainedBadReceivers num den N
            (Nat.ceil ((N : ℝ) / (Real.log (N : ℝ)) ^ 10))).card +
            epsilon * singularNormalization N :=
  eventually_B_cast_le_retained_logCutoff_add_error num den

end ImbalancedChen
