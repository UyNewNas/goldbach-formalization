import ImbalancedChen.SingularSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Fixed sublinear power errors are negligible in the actual normalization

For every fixed real `theta < 1`, fixed real coefficient `c`, and natural
logarithm exponent `k`, the error `c * N^theta * (log N)^k + 1` is eventually
at most any prescribed positive multiple of `singularNormalization N`.
In particular, this applies to every nonnegative finite real coefficient.

The proof derives the needed decay from mathlib's proved log-power versus
positive-real-power asymptotic. It then uses the genuine, uniformly positive
singular-series lower constant and the already proved divergence of the
normalization. No asymptotic estimate or count bound is assumed.

Ceiling and floor corollaries require `c ≥ 0` and prove the needed sign on
large natural arguments. The final specializations cover the literal cap
`N^(1/5)` and its precise natural ceiling.

The log-power asymptotic and real-power algebra APIs were checked against
mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, in
`Analysis/SpecialFunctions/Pow/Asymptotics.lean` and `Pow/Real.lean`.
-/

namespace ImbalancedChen

open Filter Topology

/-- Any fixed natural power of the logarithm is negligible relative to a
positive real power of the natural argument. This is a proved limit. -/
theorem tendsto_nat_log_pow_div_rpow (k : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ k / (N : ℝ) ^ delta)
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => (Real.log x) ^ k / x ^ delta)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hdelta).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- A fixed sublinear real power times a fixed logarithm power has
arbitrarily small normalized upper cost. No sign hypothesis on `c` or
lower bound on `theta` is needed for this upper estimate. -/
theorem eventually_powerLog_le_singularNormalization
    (c theta : ℝ) (k : ℕ) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hdecay : Tendsto (fun N : ℕ =>
      c * ((Real.log (N : ℝ)) ^ (k + 2) / (N : ℝ) ^ (1 - theta)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow (k + 2) (sub_pos.mpr htheta)).const_mul c
  have hsmall : ∀ᶠ N : ℕ in atTop,
      c * ((Real.log (N : ℝ)) ^ (k + 2) / (N : ℝ) ^ (1 - theta)) <
        epsilon * twinPrimeConstant :=
    hdecay.eventually (gt_mem_nhds (mul_pos hepsilon twinPrimeConstant_pos))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans zero_lt_one hNreal
  have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hNreal)
  have hpow : (N : ℝ) ^ theta ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNpos theta)
  have hbase : 0 ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  calc
    c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k =
        (c * ((Real.log (N : ℝ)) ^ (k + 2) / (N : ℝ) ^ (1 - theta))) *
          ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by
      rw [Real.rpow_sub hNpos, Real.rpow_one, pow_add]
      field_simp [ne_of_gt hNpos, hlog, hpow] <;> ring
    _ ≤ (epsilon * twinPrimeConstant) *
        ((N : ℝ) / (Real.log (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_right hsmallN.le hbase
    _ = epsilon *
        (twinPrimeConstant * (N : ℝ) / (Real.log (N : ℝ)) ^ 2) := by ring
    _ ≤ epsilon * singularNormalization N :=
      mul_le_mul_of_nonneg_left (singularNormalization_lower N) hepsilon.le

/-- The same power-logarithm error with its additive unit. The unit is
absorbed using the proved divergence of the actual normalization. -/
theorem eventually_powerLog_add_one_le_singularNormalization
    (c theta : ℝ) (k : ℕ) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k + 1 ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_powerLog_le_singularNormalization c theta k htheta
      (epsilon / 2) (half_pos hepsilon),
      eventually_singularNormalization_unit_absorption (epsilon / 2) (half_pos hepsilon)]
    with N hpower hunit
  linarith

/-- The sign needed for natural floor and ceiling estimates is proved
explicitly once the natural argument is at least one. -/
theorem powerLog_nonneg {c theta : ℝ} (hc : 0 ≤ c) (k N : ℕ) (hN : 1 ≤ N) :
    0 ≤ c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact mul_nonneg
    (mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg N) theta))
    (pow_nonneg (Real.log_nonneg hNreal) k)

/-- Exact natural ceilings of nonnegative power-logarithm errors have
arbitrarily small normalized cost. The ceiling loss is at most one. -/
theorem eventually_ceil_powerLog_le_singularNormalization
    (c theta : ℝ) (k : ℕ) (hc : 0 ≤ c) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (Nat.ceil (c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k) : ℝ) ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_powerLog_add_one_le_singularNormalization c theta k htheta
      epsilon hepsilon, eventually_ge_atTop (1 : ℕ)] with N herror hN
  exact (Nat.ceil_lt_add_one (powerLog_nonneg hc k N hN)).le.trans herror

/-- Natural floors plus one satisfy the same proved error budget. -/
theorem eventually_floor_powerLog_add_one_le_singularNormalization
    (c theta : ℝ) (k : ℕ) (hc : 0 ≤ c) (htheta : theta < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (Nat.floor (c * (N : ℝ) ^ theta * (Real.log (N : ℝ)) ^ k) : ℝ) + 1 ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_powerLog_add_one_le_singularNormalization c theta k htheta
      epsilon hepsilon, eventually_ge_atTop (1 : ℕ)] with N herror hN
  exact (add_le_add (Nat.floor_le (powerLog_nonneg hc k N hN)) le_rfl).trans herror

/-- The literal fifth-root small-prime cap, with an additive unit, is
negligible relative to the actual manuscript normalization. -/
theorem eventually_fifthRoot_add_one_le_singularNormalization :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ (1 / 5 : ℝ) + 1 ≤ epsilon * singularNormalization N := by
  simpa only [one_mul, pow_zero, mul_one] using
    eventually_powerLog_add_one_le_singularNormalization 1 (1 / 5) 0 (by norm_num)

/-- The same literal fifth-root cap rounded up to a natural number. -/
theorem eventually_ceil_fifthRoot_le_singularNormalization :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
          epsilon * singularNormalization N := by
  simpa only [one_mul, pow_zero, mul_one] using
    eventually_ceil_powerLog_le_singularNormalization 1 (1 / 5) 0
      (by norm_num) (by norm_num)

end ImbalancedChen
