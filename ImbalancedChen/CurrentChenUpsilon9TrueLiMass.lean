import ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget
import ImbalancedChen.CurrentChenTrueLiNormalization

/-!
# Leading-one transport on the actual ninth true-li mass

Every actual product a is below N^(309/500), so every moving true-li
argument N/a is at least N^(191/500).  The genuine real-variable
integration-by-parts remainder therefore gives one leading coefficient
uniformly on the entire actual product image.  Its normalized mass is
bounded by the reciprocal-totient logarithmic mass on that same image.
No density, harmonic limit or Upsilon mean is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The existing exact real remainder also gives the real-variable
leading-one limit, before choosing any moving quotient argument. -/
theorem tendsto_currentChenUpsilon9_trueLi_normalized_real :
    Tendsto (fun x : ℝ => trueLogarithmicIntegral x * Real.log x / x)
      atTop (𝓝 1) := by
  have hsmall : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have herror : Tendsto (fun x : ℝ =>
      1 + (1 / Real.log 2 ^ 2) * (Real.log x / Real.sqrt x) + 4 / Real.log x)
      atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hsmall.const_mul (1 / Real.log 2 ^ 2))).add
        (Real.tendsto_log_atTop.const_div_atTop (4 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    exact (currentChen_trueLi_normalized_bounds hx).1
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    exact (currentChen_trueLi_normalized_bounds hx).2

theorem eventually_currentChenUpsilon9_trueLi_real_le (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      trueLogarithmicIntegral x ≤ (1 + η) * x / Real.log x := by
  have hnorm : ∀ᶠ x : ℝ in atTop,
      trueLogarithmicIntegral x * Real.log x / x < 1 + η :=
    tendsto_currentChenUpsilon9_trueLi_normalized_real.eventually
      (eventually_lt_nhds (by linarith))
  filter_upwards [hnorm, eventually_ge_atTop (4 : ℝ)] with x hnorm hx
  have hxp : 0 < x := by linarith only [hx]
  have hlog : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  apply (le_div_iff₀ hlog).mpr
  have h := (div_lt_iff₀ hxp).mp hnorm
  linarith only [h]

/-- A power lower bound holds for every actual moving li argument. -/
theorem currentChenUpsilon9_li_argument_power_lower {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    (N : ℝ) ^ (191 / 500 : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hap : (0 : ℝ) < a := by
    exact_mod_cast (currentChenUpsilon9PrefixProducts_data ha).1
  apply (le_div_iff₀ hap).mpr
  calc
    _ ≤ (N : ℝ) ^ (191 / 500 : ℝ) * (N : ℝ) ^ (309 / 500 : ℝ) :=
      mul_le_mul_of_nonneg_left (currentChenUpsilon9PrefixProducts_power_bounds hN ha).2.le
        (Real.rpow_nonneg hNp.le _)
    _ = _ := by
      rw [← Real.rpow_add hNp, show (191 / 500 : ℝ) + 309 / 500 = 1 by norm_num,
        Real.rpow_one]

/-- The actual support keeps the denominator of the logarithmic profile
uniformly positive, without any assumed product-window condition. -/
theorem currentChenUpsilon9_log_gap_pos {N a : ℕ} (hN : 2 ≤ N)
    (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    0 < 1 - Real.log (a : ℝ) / Real.log (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hap : (0 : ℝ) < a := by
    exact_mod_cast (currentChenUpsilon9PrefixProducts_data ha).1
  have hlog := Real.log_pos hNr
  have hupper := Real.log_le_log hap
    (currentChenUpsilon9PrefixProducts_power_bounds hNr.le ha).2.le
  rw [Real.log_rpow (zero_lt_one.trans hNr)] at hupper
  have hquot : Real.log (a : ℝ) / Real.log (N : ℝ) ≤ (309 / 500 : ℝ) :=
    (div_le_iff₀ hlog).mpr (by nlinarith only [hupper])
  linarith only [hquot]

/-- The literal product-image harmonic mass that remains after the true-li
transport.  Its coefficient and support have no sieve-modulus argument. -/
def currentChenUpsilon9LogTotientMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    (1 / (Nat.totient a : ℝ)) *
      (1 / (1 - Real.log (a : ℝ) / Real.log (N : ℝ)))

theorem currentChenUpsilon9LogTotientMass_nonneg {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ currentChenUpsilon9LogTotientMass N := by
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg _))
    (one_div_nonneg.mpr (currentChenUpsilon9_log_gap_pos hN ha).le)

/-- The real leading-one bound is transported uniformly to every actual
product, and `phi a <= a` gives an upper bound on the same positive profile.
There is no asymptotic prime-sum or true-li hypothesis. -/
theorem eventually_currentChenUpsilon9_liMainMass_le_logTotientMass
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      currentChenUpsilon9LiMainMass N * Real.log (N : ℝ) / (N : ℝ) ≤
        (1 + η) * currentChenUpsilon9LogTotientMass N := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (eventually_currentChenUpsilon9_trueLi_real_le η hη)
  have hlarge : ∀ᶠ N : ℕ in atTop, X ≤ (N : ℝ) ^ (191 / 500 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 191 / 500)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop X)
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlarge hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlog := Real.log_pos hNr
  rw [currentChenUpsilon9LiMainMass, Finset.sum_mul, Finset.sum_div,
    currentChenUpsilon9LogTotientMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hap : (0 : ℝ) < a := by
    exact_mod_cast (currentChenUpsilon9PrefixProducts_data ha).1
  have hgap := currentChenUpsilon9_log_gap_pos hN ha
  have hquot := currentChenUpsilon9_li_argument_power_lower hNr.le ha
  have hli := hX ((N : ℝ) / (a : ℝ)) (hlarge.trans hquot)
  have hφ : (0 : ℝ) < Nat.totient a := by
    exact_mod_cast Nat.totient_pos.mpr (currentChenUpsilon9PrefixProducts_data ha).1
  have hweight : 1 / (a : ℝ) ≤ 1 / (Nat.totient a : ℝ) :=
    one_div_le_one_div_of_le hφ (by exact_mod_cast Nat.totient_le a)
  have hlogquot : Real.log ((N : ℝ) / (a : ℝ)) =
      Real.log (N : ℝ) * (1 - Real.log (a : ℝ) / Real.log (N : ℝ)) := by
    rw [Real.log_div hNp.ne' hap.ne']
    field_simp [hlog.ne']
  calc
    _ ≤ ((1 + η) * ((N : ℝ) / (a : ℝ)) / Real.log ((N : ℝ) / (a : ℝ))) *
        (Real.log (N : ℝ) / (N : ℝ)) := by
      simpa only [trueLogarithmicIntegral, mul_div_assoc] using mul_le_mul_of_nonneg_right hli
        (div_nonneg hlog.le hNp.le)
    _ = (1 + η) * ((1 / (a : ℝ)) *
        (1 / (1 - Real.log (a : ℝ) / Real.log (N : ℝ)))) := by
      rw [hlogquot]
      field_simp [hNp.ne', hap.ne', hlog.ne', hgap.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweight (one_div_nonneg.mpr hgap.le)) (by linarith only [hη])

end

end ImbalancedChen
