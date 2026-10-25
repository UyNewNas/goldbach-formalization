import ImbalancedChen.Part3ActualRadialGreenFiniteMass
import ImbalancedChen.Part3GeneralIRealPositiveEndpoint
import ImbalancedChen.Part3GeneralKRightEndpoint

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Actual positive general-order I/K Green mass on the logarithmic line, for
real 0<nu<1. The complete weighted mass is exactly one, hence the unweighted
row mass is at most 1/nu². Both endpoint derivative limits come from actual
proved I/K estimates, and integrability is derived from positive improper
integrals. There is no boundary-flux, integrability, or Schur-bound premise.
The kernel is symmetric, so the same bound holds for its column mass.
-/

namespace ImbalancedChen.Part3.ActualRadialGreenMassBound20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ComplexCompactGreenGluingSourceOnly ActualRadialGreenFiniteMass20261025a
open GeneralIRealPositiveEndpoint20261025a GeneralKRightEndpoint20261025a

def realGreen (nu s r : ℝ) : ℝ := (actualRadialGreen (nu : ℂ) s r).re

def realPotential (nu r : ℝ) : ℝ := Real.exp (2 * r) + nu^2

def weightedGreen (nu s r : ℝ) : ℝ :=
  (potential (nu : ℂ) r * actualRadialGreen (nu : ℂ) s r).re

theorem realGreen_pos {nu : ℝ} (hnu : 0 < nu) (s r : ℝ) :
    0 < realGreen nu s r := by
  have hi := generalI_real_positive (by linarith : -1 < nu)
    (Real.exp_pos (min r s))
  have hk := radialK_real_re_pos nu (max r s)
  change 0 < (radialI (nu : ℂ) (min r s) * radialK (nu : ℂ) (max r s)).re
  rw [Complex.mul_re]
  have him : (radialI (nu : ℂ) (min r s)).im = 0 := hi.1
  rw [him, zero_mul, sub_zero]
  exact mul_pos hi.2 hk

theorem actualGreen_real_im_zero {nu : ℝ} (hnu : 0 < nu) (s r : ℝ) :
    (actualRadialGreen (nu : ℂ) s r).im = 0 := by
  have hi := generalI_real_positive (by linarith : -1 < nu)
    (Real.exp_pos (min r s))
  change (radialI (nu : ℂ) (min r s) * radialK (nu : ℂ) (max r s)).im = 0
  rw [Complex.mul_im, radialK_real_im_zero, mul_zero,
    show (radialI (nu : ℂ) (min r s)).im = 0 from hi.1, zero_mul, add_zero]

theorem realPotential_cast (nu r : ℝ) :
    potential (nu : ℂ) r = (realPotential nu r : ℂ) := by
  simp only [potential, realPotential, Complex.ofReal_add, Complex.ofReal_pow]

theorem weightedGreen_eq (nu s r : ℝ) :
    weightedGreen nu s r = realPotential nu r * realGreen nu s r := by
  rw [weightedGreen, realPotential_cast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, realGreen]

theorem weightedGreen_nonneg {nu : ℝ} (hnu : 0 < nu) (s r : ℝ) :
    0 ≤ weightedGreen nu s r := by
  rw [weightedGreen_eq]
  exact mul_nonneg (by unfold realPotential; positivity) (realGreen_pos hnu s r).le

theorem realGreen_continuous {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Continuous (realGreen nu s) :=
  (actualRadialGreen_continuous (by simpa using (show -1 < nu by linarith)) s).re

theorem weightedGreen_continuous {nu : ℝ} (hnu : 0 < nu) (s : ℝ) :
    Continuous (weightedGreen nu s) :=
  ((potential_continuous (nu : ℂ)).mul
    (actualRadialGreen_continuous (by simpa using (show -1 < nu by linarith)) s)).re

private theorem actual_radialI_deriv_tendsto_zero {nu : ℝ} (hnu : 0 < nu) :
    Tendsto (deriv (radialI (nu : ℂ))) atBot (nhds 0) := by
  obtain ⟨C, R, _, hb⟩ := exists_left_exponential_bound hnu
  have hlinear : Tendsto (fun r : ℝ => nu * r) atBot atBot :=
    tendsto_id.const_mul_atBot_of_pos hnu
  have he : Tendsto (fun r : ℝ => C * Real.exp (nu * r)) atBot (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hlinear))
  change Tendsto (deriv (realILogMode nu)) atBot (nhds 0)
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_le_atBot R] with r hr
    exact (hb r hr).2) he

/-- Both literal remote fluxes vanish; the source normalization is actual. -/
theorem tendsto_finite_weighted_mass {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (s : ℝ) :
    Tendsto (fun t : ℝ => ∫ r in (-t)..t,
      potential (nu : ℂ) r * actualRadialGreen (nu : ℂ) s r) atTop (nhds 1) := by
  have hI := (actual_radialI_deriv_tendsto_zero hnu).comp tendsto_neg_atTop_atBot
  have hK := radialK_deriv_tendsto_zero (nu : ℂ)
  have hflux : Tendsto (fun t : ℝ =>
      1 + radialI (nu : ℂ) s * deriv (radialK (nu : ℂ)) t -
        radialK (nu : ℂ) s * deriv (radialI (nu : ℂ)) (-t)) atTop (nhds 1) := by
    simpa only [mul_zero, add_zero, sub_zero] using
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hK)).sub
        (tendsto_const_nhds.mul hI))
  apply hflux.congr'
  filter_upwards [eventually_ge_atTop s, eventually_ge_atTop (-s)] with t hst hnst
  exact (actualGreen_finite_weighted_mass (by simpa using hnu)
    (by simpa using hnuUpper) (by linarith : -t ≤ s) hst).symm

private theorem weighted_interval_eq_real_part {nu : ℝ} (hnu : 0 < nu)
    (s a b : ℝ) :
    (∫ r in a..b, weightedGreen nu s r) =
      (∫ r in a..b, potential (nu : ℂ) r * actualRadialGreen (nu : ℂ) s r).re := by
  change (∫ r in a..b, Complex.reCLM
    (potential (nu : ℂ) r * actualRadialGreen (nu : ℂ) s r)) = _
  exact Complex.reCLM.intervalIntegral_comp_comm
    (((potential_continuous (nu : ℂ)).mul
      (actualRadialGreen_continuous (by simpa using (show -1 < nu by linarith)) s)).intervalIntegrable a b)

/-- Positivity and the exact finite flux formula imply integrability;
there is no integrability hypothesis on the actual weighted Green row. -/
theorem weightedGreen_integrable_and_mass {nu : ℝ} (hnu : 0 < nu)
    (hnuUpper : nu < 1) (s : ℝ) :
    Integrable (weightedGreen nu s) ∧ (∫ r : ℝ, weightedGreen nu s r) = 1 := by
  have hc := weightedGreen_continuous hnu s
  have hlim : Tendsto (fun t : ℝ => ∫ r in (-t)..t, weightedGreen nu s r)
      atTop (nhds 1) := by
    have h := Complex.continuous_re.tendsto (1 : ℂ) |>.comp
      (tendsto_finite_weighted_mass hnu hnuUpper s)
    simpa only [← weighted_interval_eq_real_part hnu s, Complex.one_re] using h
  have hnorm : Tendsto (fun t : ℝ => ∫ r in (-t)..t, ‖weightedGreen nu s r‖)
      atTop (nhds 1) := by
    have hn : (fun r : ℝ => ‖weightedGreen nu s r‖) = weightedGreen nu s := by
      funext r
      exact Real.norm_of_nonneg (weightedGreen_nonneg hnu s r)
    simpa only [hn] using hlim
  have hint : Integrable (weightedGreen nu s) :=
    integrable_of_intervalIntegral_norm_tendsto 1
      (fun _ => hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      tendsto_neg_atTop_atBot tendsto_id hnorm
  refine ⟨hint, ?_⟩
  exact tendsto_nhds_unique
    (intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id) hlim

theorem realGreen_le_weighted_div {nu : ℝ} (hnu : 0 < nu) (s r : ℝ) :
    realGreen nu s r ≤ weightedGreen nu s r / nu^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hnu)).2
  rw [weightedGreen_eq]
  have hg := (realGreen_pos hnu s r).le
  have he := (Real.exp_pos (2*r)).le
  unfold realPotential
  nlinarith

/-- The actual positive Green row is integrable and satisfies its Schur
mass bound. All facts about this literal kernel are proved internally. -/
theorem actualGreen_row_mass_bound {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (s : ℝ) :
    Integrable (realGreen nu s) ∧ (∫ r : ℝ, realGreen nu s r) ≤ 1 / nu^2 := by
  obtain ⟨hw, hmass⟩ := weightedGreen_integrable_and_mass hnu hnuUpper s
  have hmajor : Integrable (fun r : ℝ => weightedGreen nu s r / nu^2) := hw.div_const _
  have hg : Integrable (realGreen nu s) := hmajor.mono'
    (realGreen_continuous hnu s).aestronglyMeasurable
    (Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (realGreen_pos hnu s r).le]
      exact realGreen_le_weighted_div hnu s r)
  refine ⟨hg, ?_⟩
  calc
    _ ≤ ∫ r : ℝ, weightedGreen nu s r / nu^2 :=
      integral_mono hg hmajor (realGreen_le_weighted_div hnu s)
    _ = _ := by rw [integral_div_const, hmass]

theorem realGreen_symmetric (nu s r : ℝ) : realGreen nu s r = realGreen nu r s := by
  unfold realGreen actualRadialGreen kernel
  rw [min_comm r s, max_comm r s]

theorem actualGreen_column_mass_bound {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (r : ℝ) :
    Integrable (fun s : ℝ => realGreen nu s r) ∧
      (∫ s : ℝ, realGreen nu s r) ≤ 1 / nu^2 := by
  have hs : (fun s : ℝ => realGreen nu s r) = realGreen nu r :=
    funext (fun s => realGreen_symmetric nu s r)
  rw [hs]
  exact actualGreen_row_mass_bound hnu hnuUpper r

end
end ImbalancedChen.Part3.ActualRadialGreenMassBound20261025a
