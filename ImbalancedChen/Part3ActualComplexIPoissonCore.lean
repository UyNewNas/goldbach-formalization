import ImbalancedChen.Part3GeneralJSymmetricPoissonIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual compact exponential Poisson integral at a COMPLEX argument.
Endpoint L1 follows from the supplied genuine symmetric Beta weight for
Re(nu)>-1/2. Its exponential and derivative are dominated on local argument
discs, proving actual entire argument holomorphy and the growth factor
exp(|Re(z)|). The already evaluated genuine ordinary-J Poisson integral
gives the literal reciprocal-Gamma core on a positive imaginary-axis
sequence. The analytic identity theorem then proves the complex I-core
evaluation everywhere. No complex-I representation or growth estimate
is an input. Primary normalization/domain: DLMF 10.32.2.
-/

namespace ImbalancedChen.Part3.ActualComplexIPoissonCore20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open GeneralComplexISeriesSourceOnly
open GeneralJBetaPoissonIntegralSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly

def complexIPoissonDensity (nu z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (z * (t : ℂ)) * jSymmetricPoissonWeight nu t

def complexIPoissonIntegral (nu z : ℂ) : ℂ :=
  ∫ t in Ioo (-1 : ℝ) 1, complexIPoissonDensity nu z t

def poissonGammaNormalization (nu : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)

def complexIPoissonNormMass (nu : ℂ) : ℝ :=
  ∫ t in Ioo (-1 : ℝ) 1, ‖jSymmetricPoissonWeight nu t‖

theorem symmetricPoissonWeight_integrableOn {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) :
    IntegrableOn (jSymmetricPoissonWeight nu) (Ioo (-1 : ℝ) 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    (jSymmetricPoissonWeight_integrable hnu)

theorem complexIPoissonNormMass_nonneg (nu : ℂ) : 0 ≤ complexIPoissonNormMass nu :=
  integral_nonneg fun _ => norm_nonneg _

theorem poissonGammaNormalization_ne_zero {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) : poissonGammaNormalization nu ≠ 0 := by
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hg : Complex.Gamma (nu + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      have hre : (nu + 1 / 2).re = nu.re + 1 / 2 := by norm_num
      rw [hre]
      linarith)
  exact mul_ne_zero hp hg

theorem poisson_coordinate_abs_le_one {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : |t| ≤ 1 :=
  abs_le.mpr ⟨ht.1.le, ht.2.le⟩

theorem complexIPoissonDensity_norm_le (nu z : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖complexIPoissonDensity nu z t‖ ≤
      Real.exp |z.re| * ‖jSymmetricPoissonWeight nu t‖ := by
  have hexp : z.re * t ≤ |z.re| := by
    calc
      _ ≤ |z.re * t| := le_abs_self _
      _ = |z.re| * |t| := abs_mul _ _
      _ ≤ |z.re| * 1 :=
        mul_le_mul_of_nonneg_left (poisson_coordinate_abs_le_one ht) (abs_nonneg _)
      _ = _ := mul_one _
  rw [complexIPoissonDensity, norm_mul, Complex.norm_exp]
  have hre : (z * (t : ℂ)).re = z.re * t := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (norm_nonneg _)

theorem complexIPoissonDensity_integrable {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (z : ℂ) :
    IntegrableOn (complexIPoissonDensity nu z) (Ioo (-1 : ℝ) 1) := by
  have hm : Measurable (complexIPoissonDensity nu z) := by
    unfold complexIPoissonDensity jSymmetricPoissonWeight
    fun_prop
  apply ((symmetricPoissonWeight_integrableOn hnu).norm.const_mul
    (Real.exp |z.re|)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact complexIPoissonDensity_norm_le nu z ht

/-- The factor exp(|Re(z)|) is derived from the actual compact
exponential integral, not from an assumed Bessel asymptotic. -/
theorem complexIPoissonIntegral_norm_le {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (z : ℂ) :
    ‖complexIPoissonIntegral nu z‖ ≤ Real.exp |z.re| * complexIPoissonNormMass nu := by
  have h := norm_integral_le_of_norm_le
    ((symmetricPoissonWeight_integrableOn hnu).norm.const_mul (Real.exp |z.re|))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact complexIPoissonDensity_norm_le nu z ht)
  simpa only [complexIPoissonIntegral, integral_const_mul, complexIPoissonNormMass] using h

theorem complexIPoissonDensity_hasDerivAt (nu z : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => complexIPoissonDensity nu w t)
      ((t : ℂ) * complexIPoissonDensity nu z t) z := by
  convert (((hasDerivAt_id z).mul_const (t : ℂ)).cexp).mul_const
    (jSymmetricPoissonWeight nu t) using 1 <;>
    unfold complexIPoissonDensity <;> ring

theorem complexIPoissonIntegral_hasDerivAt {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (z : ℂ) :
    HasDerivAt (complexIPoissonIntegral nu)
      (∫ t in Ioo (-1 : ℝ) 1, (t : ℂ) * complexIPoissonDensity nu z t) z := by
  let bound : ℝ → ℝ := fun t =>
    Real.exp (‖z‖ + 1) * ‖jSymmetricPoissonWeight nu t‖
  have hboundInt : IntegrableOn bound (Ioo (-1 : ℝ) 1) :=
    (symmetricPoissonWeight_integrableOn hnu).norm.const_mul _
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (complexIPoissonDensity nu w)
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    Eventually.of_forall fun w => (complexIPoissonDensity_integrable hnu w).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) * complexIPoissonDensity nu z t)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have hm : Measurable (fun t : ℝ => (t : ℂ) * complexIPoissonDensity nu z t) := by
      unfold complexIPoissonDensity jSymmetricPoissonWeight
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ w ∈ ball z 1,
      ‖(t : ℂ) * complexIPoissonDensity nu w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    intro w hw
    have ht1 := poisson_coordinate_abs_le_one ht
    have hdist : ‖w - z‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hw
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    have hre : |w.re| ≤ ‖z‖ + 1 := by
      linarith [Complex.abs_re_le_norm w]
    calc
      _ = |t| * ‖complexIPoissonDensity nu w t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * ‖complexIPoissonDensity nu w t‖ :=
        mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
      _ ≤ Real.exp |w.re| * ‖jSymmetricPoissonWeight nu t‖ := by
        simpa only [one_mul] using complexIPoissonDensity_norm_le nu w ht
      _ ≤ bound t :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) (norm_nonneg _)
  have hdiff : ∀ᵐ t : ℝ ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ w ∈ ball z 1,
      HasDerivAt (fun x : ℂ => complexIPoissonDensity nu x t)
        ((t : ℂ) * complexIPoissonDensity nu w t) w :=
    Eventually.of_forall fun t w _ => complexIPoissonDensity_hasDerivAt nu w t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun w t => complexIPoissonDensity nu w t)
    (F' := fun w t => (t : ℂ) * complexIPoissonDensity nu w t)
    (bound := bound) (ball_mem_nhds z (by norm_num : (0 : ℝ) < 1)) hFmeas
    (complexIPoissonDensity_integrable hnu z) hF'meas hbound hboundInt hdiff).2

theorem complexIPoissonIntegral_analyticOnNhd {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) :
    AnalyticOnNhd ℂ (complexIPoissonIntegral nu) univ := by
  have hd : Differentiable ℂ (complexIPoissonIntegral nu) :=
    fun z => (complexIPoissonIntegral_hasDerivAt hnu z).differentiableAt
  exact fun z _ => hd.analyticAt z

theorem complexIPoissonIntegral_imaginary {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) {q : ℝ} (hq : 0 < q) :
    complexIPoissonIntegral nu (Complex.I * (q : ℂ)) =
      poissonGammaNormalization nu * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hconvert : complexIPoissonIntegral nu (Complex.I * (q : ℂ)) =
      jSymmetricPoissonIntegral nu q := by
    unfold complexIPoissonIntegral jSymmetricPoissonIntegral
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    rfl
  calc
    _ = jSymmetricPoissonIntegral nu q := hconvert
    _ = jBetaPoissonIntegral nu q := jSymmetricPoissonIntegral_eq_beta hnu q
    _ = _ := by
      simpa only [poissonGammaNormalization] using jBetaPoissonIntegral_eq_core hnu hq

theorem imaginary_half_sq (q : ℝ) :
    ((Complex.I * (q : ℂ)) / 2) ^ (2 : ℕ) = -(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
  calc
    _ = Complex.I ^ (2 : ℕ) * ((q : ℂ) / 2) ^ (2 : ℕ) := by ring
    _ = _ := by
      simp only [Complex.I_sq, neg_one_mul, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- Actual complex-I core Poisson evaluation, from the literal integral
and the genuine ordinary-J supplier through the analytic identity theorem. -/
theorem complexIPoissonIntegral_eq_core {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (z : ℂ) :
    complexIPoissonIntegral nu z =
      poissonGammaNormalization nu * generalICore nu ((z / 2) ^ (2 : ℕ)) := by
  have hF := complexIPoissonIntegral_analyticOnNhd hnu
  have hG : AnalyticOnNhd ℂ
      (fun w : ℂ => poissonGammaNormalization nu * generalICore nu ((w / 2) ^ (2 : ℕ)))
      univ := by
    intro w _
    have hc : AnalyticAt ℂ (fun x : ℂ => (x / 2) ^ (2 : ℕ)) w :=
      (analyticAt_id.div_const).pow 2
    exact analyticAt_const.mul
      ((analyticAt_generalICore (by linarith : -1 < nu.re) ((w / 2) ^ (2 : ℕ))).comp hc)
  let sequence : ℕ → ℂ := fun n => Complex.I * ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop.add_const 1).const_div_atTop 1
  have hr : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hinv
  have hc : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
      atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hlim : Tendsto sequence atTop (𝓝 Complex.I) := by
    simpa only [sequence, mul_one] using hc.const_mul Complex.I
  have hpunctured : Tendsto sequence atTop (𝓝[≠] Complex.I) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, Eventually.of_forall fun n => ?_⟩
    change sequence n ≠ Complex.I
    intro heq
    have him := congrArg Complex.im heq
    have he : 1 + 1 / ((n : ℝ) + 1) = 1 := by
      simpa only [sequence, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] using him
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hseqEq : ∃ᶠ n : ℕ in atTop,
      complexIPoissonIntegral nu (sequence n) =
        poissonGammaNormalization nu * generalICore nu ((sequence n / 2) ^ (2 : ℕ)) := by
    apply Filter.Eventually.frequently
    exact Eventually.of_forall fun n => by
      simpa only [sequence, imaginary_half_sq] using
        complexIPoissonIntegral_imaginary hnu (by positivity : 0 < 1 + 1 / ((n : ℝ) + 1))
  exact congrFun (hF.eq_of_frequently_eq hG (hpunctured.frequently hseqEq)) z

end
end ImbalancedChen.Part3.ActualComplexIPoissonCore20261026b
