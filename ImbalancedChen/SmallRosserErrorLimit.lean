import ImbalancedChen.ActualSmallRosserDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Scalar limits for the actual small-Rosser density error

For fixed positive epsilon the error tends to its positive exponential
floor, rather than to zero. Choosing epsilon before the large parameter
absorbs this floor even after multiplication by the quadratic reciprocal
epsilon cost. The extra logarithmic rough-density factor tends to one.
These are proved scalar limits, without sieve-density hypotheses.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- The fixed-epsilon error has the literal exponential floor as its limit. -/
theorem tendsto_actualSmallRosserDensityError
    (C K epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun D : ℝ => actualSmallRosserDensityError C K D epsilon)
      atTop (𝓝 (C * Real.exp (-(1 / epsilon)))) := by
  have hlog : Tendsto (fun D : ℝ => epsilon * Real.log D) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hepsilon
  have hdecay : Tendsto
      (fun D : ℝ => (epsilon * Real.log D) ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hlog
  have hscaled := hdecay.const_mul (Real.exp (Real.sqrt K - 1 / epsilon))
  have hsum := hscaled.const_add (Real.exp (-(1 / epsilon)))
  simpa only [actualSmallRosserDensityError, mul_zero, add_zero] using hsum.const_mul C

/-- Exponential decay beats the reciprocal-square epsilon cost. This holds
for every real C; in particular it supplies the required nonnegative-C case. -/
theorem exists_smallRosser_epsilon_absorbing
    (C r eta : ℝ) (hr : 0 < r) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon ^ 2 ≤ r ∧
      (C * Real.exp (-(1 / epsilon))) * (r / epsilon ^ 2) < eta := by
  have hlimit : Tendsto (fun t : ℝ => (C * r) * (t ^ 2 * Real.exp (-t)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (C * r)
  have hsmall : ∀ᶠ t : ℝ in atTop, (C * r) * (t ^ 2 * Real.exp (-t)) < eta :=
    (tendsto_order.1 hlimit).2 eta heta
  obtain ⟨t, htSmall, htEight, htR⟩ :=
    (hsmall.and ((eventually_gt_atTop (8 : ℝ)).and
      (eventually_ge_atTop (1 / r)))).exists
  have ht : 0 < t := by linarith
  have hepsilon : 0 < 1 / t := one_div_pos.mpr ht
  have hepsilonEight : 1 / t < (1 / 8 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8) htEight
  have hepsilonR : 1 / t ≤ r := by
    apply (div_le_iff₀ ht).mpr
    have hrt : 1 ≤ t * r := (div_le_iff₀ hr).mp htR
    nlinarith
  refine ⟨1 / t, hepsilon, hepsilonEight, ?_, ?_⟩
  · nlinarith
  · have heq : (C * Real.exp (-(1 / (1 / t)))) * (r / (1 / t) ^ 2) =
        (C * r) * (t ^ 2 * Real.exp (-t)) := by
      rw [one_div_one_div]
      field_simp
    rw [heq]
    exact htSmall

/-- After epsilon is fixed, the actual error times the rough-density
envelope converges to the same exponential floor times its constant mass.
The rough-product constant is independent of the small-density constant K. -/
theorem tendsto_actualSmallRosserDensityError_mul_roughMassEnvelope
    (C K Krough r epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto
      (fun D : ℝ => actualSmallRosserDensityError C K D epsilon *
        (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))
      atTop (𝓝 ((C * Real.exp (-(1 / epsilon))) * (r / epsilon ^ 2))) := by
  have hlog : Tendsto (fun D : ℝ => epsilon ^ 2 * Real.log D) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (sq_pos_of_pos hepsilon)
  have hcorrection : Tendsto
      (fun D : ℝ => 1 + Krough / (epsilon ^ 2 * Real.log D)) atTop (𝓝 1) := by
    simpa only [add_zero] using (hlog.const_div_atTop Krough).const_add 1
  have herror := (tendsto_actualSmallRosserDensityError C K epsilon hepsilon).mul_const
    (r / epsilon ^ 2)
  simpa only [mul_one] using herror.mul hcorrection

end

end ImbalancedChen
