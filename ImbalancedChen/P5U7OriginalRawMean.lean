import ImbalancedChen.P5U7OriginalMainNormalization
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The exact denominator correction tends to zero on the SAME marked-pair
selector. In particular eta=0 is allowed: the original strict square-root
wall is already a proper affine gate. This proves the original Buchstab
main mean, before identifying its Fin-2 Lebesgue integral with the nested
manuscript integral. No desired arithmetic or analytic mean is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators
open Classical

theorem tendsto_p5U7InteriorLabelledTestSum_nonneg {eta : ℝ}
    (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7InteriorLabelledTestSum N eta) atTop
      (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  apply (tendsto_p5U7InteriorDoubleTestSum eta).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (p5U7InteriorLabelledTestSum_eq_box hN heta).symm

/-- This error is the actual difference between shifted and unshifted
prime denominators, rather than a generic error supplier. -/
theorem tendsto_p5U7Interior_denominator_difference {eta : ℝ}
    (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7InteriorLabelledTestSum N eta -
      p5U7InteriorRawTestSum N eta) atTop (𝓝 0) := by
  have hpower : Tendsto (fun N : ℕ =>
      2 / (N : ℝ) ^ (59 / 250 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_nat_log_pow_div_rpow 0
      (by norm_num : (0 : ℝ) < 59 / 250)).const_mul (2 : ℝ)
    simpa only [pow_zero, mul_div_assoc, mul_one, mul_zero] using h
  have hmajor := hpower.mul (tendsto_p5U7InteriorLabelledTestSum_nonneg heta)
  apply squeeze_zero' ?_ ?_ (by simpa only [zero_mul] using hmajor)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (p5U7Interior_raw_to_shifted_bound hN heta).1
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (p5U7Interior_raw_to_shifted_bound hN heta).2

/-- Leading-one prime-box transport with the original `1/(p₁*p₂)`
denominator, including the untruncated original strict gate eta=0. -/
theorem tendsto_p5U7InteriorRawTestSum {eta : ℝ} (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7InteriorRawTestSum N eta) atTop
      (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  have h := (tendsto_p5U7InteriorLabelledTestSum_nonneg heta).sub
    (tendsto_p5U7Interior_denominator_difference heta)
  simpa only [sub_sub_cancel, sub_zero] using h

theorem p5U7InteriorSelector_zero {N : ℕ} (hN : 2 ≤ N) :
    p5U7InteriorSelector N 0 =
      chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)) := by
  apply Finset.filter_eq_self.mpr
  intro t ht
  obtain ⟨hc, _hD, horder, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
  have hp := (mem_chenAdditivePrimeCarrier.mp hc1).2.1
  have hq := (mem_chenAdditivePrimeCarrier.mp hc2).2.1
  have hpR : (0 : ℝ) < t.1 := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < t.2 := by exact_mod_cast hq.pos
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  apply (p5U7InteriorRegion_iff 0 _).mpr
  constructor
  · change Real.log (t.1 : ℝ) / Real.log (N : ℝ) <
      Real.log (t.2 : ℝ) / Real.log (N : ℝ)
    apply (div_lt_div_iff_of_pos_right hNlog).mpr
    exact Real.log_lt_log hpR (by exact_mod_cast horder)
  · have h := (currentChenUpsilon9_sqrt_log_iff hN hp.pos hq.pos).mp hcap
    simpa only [add_zero] using h

theorem p5U7MassRawFullTestSum_eq_zero_interior {N : ℕ} (hN : 2 ≤ N) :
    p5U7MassRawFullTestSum N = p5U7InteriorRawTestSum N 0 := by
  simp only [p5U7MassRawFullTestSum, p5U7InteriorRawTestSum,
    p5U7InteriorSelector_zero hN]

/-- The literal full original Buchstab main has the original leading-one
double-prime limit. The remaining integral dictionary is independent. -/
theorem tendsto_p5U7MassBuchstabMain_normalized :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      p5U7MassBuchstabMain N) atTop (𝓝 (p5U7InteriorOmegaIntegral 0)) := by
  apply (tendsto_p5U7InteriorRawTestSum (eta := 0) le_rfl).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [p5U7MassBuchstabMain_normalized_eq_raw_full hN,
    p5U7MassRawFullTestSum_eq_zero_interior hN]

theorem tendsto_p5U7MassBuchstabInteriorMain_normalized {eta : ℝ}
    (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
      p5U7MassBuchstabInteriorMain N eta) atTop
      (𝓝 (p5U7InteriorOmegaIntegral eta)) := by
  apply (tendsto_p5U7InteriorRawTestSum heta).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (p5U7MassBuchstabInteriorMain_normalized_eq_raw hN eta).symm

end

end ImbalancedChen
