import ImbalancedChen.Part3ActualJCompactRealOrderContinuity
import ImbalancedChen.Part3ActualRealOrderJLargeQ
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

One actual large-q constant and one actual near-zero constant for every
real order nu in [-r,r], 0<r<1/2. Initial energy continuity comes from the
valid joint Poisson/core J and q-jet continuity. The near-zero constant
comes from one weight of order -r and a compact reciprocal-Gamma factor.
No pointwise constants, spectral caps, or uniform suppliers are assumed.
-/

namespace ImbalancedChen.Part3.ActualJUniformCompactRealOrderBounds20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a ActualJPoissonQDerivatives20261025a
open ActualJCompactRealOrderContinuity20261026b
open ActualRealOrderJRadialJet20261026b ActualRealOrderJLargeQ20261026b

private theorem generalJ_at_one_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun nu : ℝ => generalJ (nu : ℂ) 1) (Icc (-r) r) := by
  exact (generalJ_joint_continuousOn hr).comp
    (by fun_prop : ContinuousOn (fun nu : ℝ => (nu, (1 : ℝ))) (Icc (-r) r))
    (fun nu hnu => ⟨hnu, by norm_num⟩)

private theorem generalJFirst_at_one_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun nu : ℝ => generalJFirst (nu : ℂ) 1) (Icc (-r) r) := by
  exact (generalJFirst_joint_continuousOn hr).comp
    (by fun_prop : ContinuousOn (fun nu : ℝ => (nu, (1 : ℝ))) (Icc (-r) r))
    (fun nu hnu => ⟨hnu, by norm_num⟩)

theorem realLargeQAmplitude_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn realLargeQAmplitude (Icc (-r) r) := by
  have hJ := generalJ_at_one_continuousOn hr
  have hF := generalJFirst_at_one_continuousOn hr
  have hU : ContinuousOn (fun nu : ℝ => realRadialJ nu 1) (Icc (-r) r) := continuousOn_const.mul hJ
  have hUF : ContinuousOn (fun nu : ℝ => realRadialJFirst nu 1) (Icc (-r) r) :=
    (continuousOn_const.mul hF).add (continuousOn_const.mul hJ)
  have hV : ContinuousOn (fun nu : ℝ => realRadialPotential nu 1) (Icc (-r) r) := by
    unfold realRadialPotential realRadialCoefficient
    fun_prop
  exact ((hUF.norm.pow 2).add (hV.mul (hU.norm.pow 2))).sqrt

/-- ONE large-q constant for the whole real-order compact interval. -/
theorem exists_generalJ_uniform_real_large_q_bound {r : ℝ} (hr : r < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ nu ∈ Icc (-r) r, ∀ q : ℝ, 1 ≤ q →
      ‖generalJ (nu : ℂ) q‖ ≤ C / Real.sqrt q := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-r) r))
    .exists_bound_of_continuousOn (realLargeQAmplitude_continuousOn hr)
  refine ⟨|A| + 1, by positivity, ?_⟩
  intro nu hnu q hq
  have habs : |nu| ≤ 1 / 2 := (abs_le.mpr hnu).trans hr.le
  have hb : realLargeQAmplitude nu ≤ |A| + 1 := by
    have h := hA nu hnu
    rw [Real.norm_eq_abs] at h
    have hh := le_abs_self (realLargeQAmplitude nu)
    have hAA := le_abs_self A
    linarith
  exact (generalJ_real_large_q_bound habs hq).trans (div_le_div_of_nonneg_right hb (Real.sqrt_nonneg q))

private def orderMass (r : ℝ) : ℝ := ∫ u in Ioo (-1 : ℝ) 1, ‖jSymmetricPoissonWeight ((-r : ℝ) : ℂ) u‖

private theorem orderMass_nonneg (r : ℝ) : 0 ≤ orderMass r := integral_nonneg (fun _ => norm_nonneg _)

private theorem moment_uniform_norm {r : ℝ} (hr : r < 1 / 2) {nu : ℝ}
    (hnu : nu ∈ Icc (-r) r) (q : ℝ) : ‖jPoissonMoment 0 (nu : ℂ) q‖ ≤ orderMass r := by
  have hn : -(1 / 2 : ℝ) < ((-r : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hi : IntegrableOn (fun u => ‖jSymmetricPoissonWeight ((-r : ℝ) : ℂ) u‖) (Ioo (-1 : ℝ) 1) := by
    simpa only [jSymmetricPoissonWeight, poissonWeight, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (poissonWeight_integrable hn).norm
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact (jPoissonMomentIntegrand_norm_le 0 (nu : ℂ) q hu).trans (realPoissonWeight_norm_antitone hnu.1 hu)

private theorem reciprocalGamma_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun nu : ℝ => (((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))⁻¹)) (Icc (-r) r) := by
  have h := (jPoissonPrefactor_joint_continuousOn hr).comp
    (by fun_prop : ContinuousOn (fun nu : ℝ => (nu, (2 : ℝ))) (Icc (-r) r))
    (fun nu hnu => ⟨hnu, by norm_num⟩)
  simpa only [jPoissonPrefactor, div_self (by norm_num : (2 : ℝ) ≠ 0), Complex.ofReal_one,
    Complex.one_cpow, one_div] using h

/-- ONE near-zero bound for all real orders in [-r,r]. This bound retains
the genuine q^(-r) singularity; no finite value at q=0 is asserted. -/
theorem exists_generalJ_uniform_real_small_q_bound {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ nu ∈ Icc (-r) r, ∀ q ∈ Ioc (0 : ℝ) 1,
      ‖generalJ (nu : ℂ) q‖ ≤ D * q ^ (-r) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-r) r)).exists_bound_of_continuousOn
    (reciprocalGamma_continuousOn hr)
  let A' : ℝ := |A| + 1
  let D : ℝ := A' * (orderMass r + 1) * (2 : ℝ) ^ r
  have hAp : 0 < A' := by dsimp [A']; positivity
  have hM : 0 ≤ orderMass r := orderMass_nonneg r
  have h2 : 0 < (2 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) r
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro nu hnu q hq
  have hn : -(1 / 2 : ℝ) < (nu : ℂ).re := by simp only [Complex.ofReal_re]; linarith [hnu.1]
  have hGamma : ‖((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))⁻¹‖ ≤ A' := by
    have h := hA nu hnu
    have hh := le_abs_self A
    dsimp [A']
    linarith
  have hPower : (q / 2) ^ nu ≤ (q / 2) ^ (-r) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith [hq.2]) hnu.1
  have hJ : generalJ (nu : ℂ) q = jPoissonPrefactor (nu : ℂ) q * jPoissonMoment 0 (nu : ℂ) q := by
    rw [jPoissonMoment_zero]
    exact generalJ_eq_symmetric_poisson_integral hn hq.1
  rw [hJ, norm_mul, jPoissonPrefactor, div_eq_mul_inv, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
  simp only [Complex.ofReal_re]
  calc
    (q / 2) ^ nu * ‖((Real.sqrt Real.pi : ℂ) * Gamma ((nu : ℂ) + 1 / 2))⁻¹‖ *
        ‖jPoissonMoment 0 (nu : ℂ) q‖ ≤ (q / 2) ^ (-r) * A' * (orderMass r + 1) := by
      apply mul_le_mul
      · exact mul_le_mul hPower hGamma (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      · exact (moment_uniform_norm hr hnu q).trans (by linarith)
      · exact norm_nonneg _
      · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hAp.le
    _ = D * q ^ (-r) := by
      rw [Real.div_rpow hq.1.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) r,
        div_inv_eq_mul]
      dsimp [D]
      ring

end
end ImbalancedChen.Part3.ActualJUniformCompactRealOrderBounds20261026b
