import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Logarithmic and power bounds for the growing Brun rank

The exponential series pays the factorial error using only a linear bound
on the reciprocal-prime mass in `log log x`. The rank support is paid with
a fixed power reserve, uniformly in the natural cutoff.
-/

namespace ImbalancedChen.Part3

open Filter

noncomputable section

/-- The manuscript's even truncation rank. -/
def brunRank (x : ℝ) : ℕ := 2 * ⌊(Real.log (Real.log x)) ^ 2⌋₊

theorem brunRank_even (x : ℝ) : Even (brunRank x) :=
  ⟨⌊(Real.log (Real.log x)) ^ 2⌋₊, by simp [brunRank, two_mul]⟩

private theorem brunRank_succ_bounds {x : ℝ} (hx : 1 ≤ Real.log (Real.log x)) :
    (Real.log (Real.log x)) ^ 2 ≤ (brunRank x + 1 : ℕ) ∧
    ((brunRank x + 1 : ℕ) : ℝ) ≤ 3 * (Real.log (Real.log x)) ^ 2 := by
  let L := Real.log (Real.log x)
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hx
  have hF := Nat.floor_le (sq_nonneg L)
  have hF' : L ^ 2 < (⌊L ^ 2⌋₊ : ℝ) + 1 := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using Nat.lt_succ_floor (L ^ 2)
  change L ^ 2 ≤ ((2 * ⌊L ^ 2⌋₊ + 1 : ℕ) : ℝ) ∧
    ((2 * ⌊L ^ 2⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L ^ 2
  push_cast
  constructor <;> linarith

/-- Any fixed log saving is available for the reciprocal mass of the
next-rank divisors when the prime harmonic mass grows at most linearly in
`log log x`. -/
theorem eventually_brun_factorial_logAccuracy (A C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ C * Real.log (Real.log x) →
      W ^ (brunRank x + 1) / (brunRank x + 1).factorial ≤ (Real.log x) ^ (-A) := by
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hdouble := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hdouble.eventually_ge_atTop 1,
    hdouble.eventually_ge_atTop ((2 * C + A) / Real.log 2),
    eventually_gt_atTop (1 : ℝ)] with x hL hlarge hx
  intro W hW hWC
  let L := Real.log (Real.log x)
  let k := brunRank x + 1
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hk : L ^ 2 ≤ (k : ℝ) := (brunRank_succ_bounds hL).1
  have hbound : 2 * C + A ≤ L * Real.log 2 := (div_le_iff₀ hlog2).mp hlarge
  have hlin : (2 * C + A) * L ≤ (k : ℝ) * Real.log 2 := by
    calc
      _ ≤ (L * Real.log 2) * L := mul_le_mul_of_nonneg_right hbound hL0
      _ = L ^ 2 * Real.log 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hk hlog2.le
  have hexp : 2 * W - (k : ℝ) * Real.log 2 ≤ -A * L := by
    nlinarith only [hWC, hlin]
  have htwo : 0 < (2 : ℝ) ^ k := by positivity
  have hpow := Real.pow_div_factorial_le_exp (x := 2 * W) (by positivity) k
  rw [mul_pow] at hpow
  calc
    W ^ k / k.factorial ≤ Real.exp (2 * W) / (2 : ℝ) ^ k := by
      apply (le_div_iff₀ htwo).mpr
      calc
        _ = (2 : ℝ) ^ k * W ^ k / k.factorial := by ring
        _ ≤ _ := hpow
    _ = Real.exp (2 * W - (k : ℝ) * Real.log 2) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (-A * L) := Real.exp_le_exp.mpr hexp
    _ = Real.log x ^ (-A) := by
      rw [Real.rpow_def_of_pos (Real.log_pos hx), mul_comm]

/-- The full next-rank divisor support grows more slowly than every fixed
positive power at the permitted chart cutoff. -/
theorem eventually_brun_support_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ℕ,
      (z : ℝ) ≤ x ^ (2 / (Real.log (Real.log x)) ^ 3) →
      ((z ^ (brunRank x + 1) : ℕ) : ℝ) ≤ x ^ δ := by
  have hdouble := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hdouble.eventually_ge_atTop 1,
    hdouble.eventually_ge_atTop (6 / δ), eventually_gt_atTop (1 : ℝ)] with x hL hlarge hx
  intro z hz
  let L := Real.log (Real.log x)
  let k := brunRank x + 1
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hk : (k : ℝ) ≤ 3 * L ^ 2 := (brunRank_succ_bounds hL).2
  have hδL : 6 ≤ δ * L := by
    change 6 / δ ≤ L at hlarge
    exact ((div_le_iff₀ hδ).mp hlarge).trans_eq (mul_comm _ _)
  have hδL3 : 6 * L ^ 2 ≤ δ * L ^ 3 := by
    calc
      _ ≤ (δ * L) * L ^ 2 := mul_le_mul_of_nonneg_right hδL (sq_nonneg L)
      _ = _ := by ring
  have hexponent : (2 / L ^ 3) * (k : ℝ) ≤ δ := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (pow_pos hLpos 3)).mpr (by linarith only [hk, hδL3])
  rw [Nat.cast_pow]
  calc
    _ ≤ (x ^ (2 / L ^ 3)) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg z) hz k
    _ = x ^ ((2 / L ^ 3) * (k : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_mul (zero_lt_one.trans hx).le]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le hexponent

end

end ImbalancedChen.Part3
