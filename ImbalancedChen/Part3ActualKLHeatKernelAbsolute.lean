import ImbalancedChen.Part3ActualKLHeatTransport
import ImbalancedChen.Part3ImaginaryOrderKZeroOrderPositivity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.
Positive-time absolute convergence for the literal radial KL heat kernel.
The Gaussian pays the exponential growth of the ORIGINAL tauMeasure.
No individual imaginary-order K-function is assumed to belong to radial L2.
-/
namespace ImbalancedChen.Part3.ActualKLHeatKernelAbsolute20261026a
noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ImaginaryOrderKBesselSourceOnly ImaginaryOrderKZeroOrderPositivitySourceOnly
open ActualKLCoordinateMeasures20261025a ActualKLResolventCoordinate20261025a
open ActualKLCompactTestIntegrationByParts20261025a

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

/-- Literal radial kernel, with the original order tau (not 2 tau). -/
def K (τ r : ℝ) : ℂ := radialK ((τ : ℂ) * Complex.I) r

def Kzero (r : ℝ) : ℝ := imaginaryOrderK 0 (Real.exp r)

theorem K_eq_imaginary (τ r : ℝ) :
    K τ r = (imaginaryOrderK (τ / 2) (Real.exp r) : ℂ) := by
  simpa [K, radialK] using complexOrderK_imaginary (τ / 2) (Real.exp r)

theorem Kzero_pos (r : ℝ) : 0 < Kzero r :=
  imaginaryOrderK_zero_pos (Real.exp_pos r)

theorem K_norm_le (τ r : ℝ) : ‖K τ r‖ ≤ Kzero r := by
  rw [K_eq_imaginary, Complex.norm_real, Real.norm_eq_abs]
  exact imaginaryOrderK_abs_le_zero _ (Real.exp_pos r)

theorem Kzero_continuous : Continuous Kzero := by
  have heq : Kzero = fun r => (radialK 0 r).re := by
    funext r
    have h := K_eq_imaginary 0 r
    simpa [K, Kzero] using (congrArg Complex.re h).symm
  rw [heq]
  exact Complex.continuous_re.comp (radialK_C2 0).continuous

/-- Joint measurability follows directly from the defining absolutely
convergent u-integral; no global-in-r square integrability is used. -/
theorem K_joint_measurable : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
  have hc : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      complexOrderIntegrand ((p.1.1 : ℂ) * Complex.I)
        (Real.exp p.1.2) p.2) := by
    unfold complexOrderIntegrand
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'.measurable

theorem K_measurable_order (r : ℝ) : Measurable (fun τ => K τ r) :=
  K_joint_measurable.comp (measurable_id.prodMk measurable_const)

/-- Completing the square explicitly absorbs sinh(pi tau) in a Gaussian. -/
theorem gaussian_density_bound {t : ℝ} (ht : 0 < t) {τ : ℝ} (hτ : 0 ≤ τ) :
    tauDensity τ * Real.exp (-t * τ^2) ≤
      ((2 / Real.pi^2) * Real.exp (Real.pi^2 / (2*t))) *
        (τ * Real.exp (-(t/2) * τ^2)) := by
  have hy : Real.pi * τ - (t/2) * τ^2 ≤ Real.pi^2 / (2*t) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).2
    nlinarith [sq_nonneg (t*τ - Real.pi)]
  have hs : Real.sinh (Real.pi * τ) ≤ Real.exp (Real.pi * τ) := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (Real.pi*τ), Real.exp_pos (-(Real.pi*τ))]
  have he : Real.exp (Real.pi*τ) * Real.exp (-t*τ^2) ≤
      Real.exp (Real.pi^2/(2*t)) * Real.exp (-(t/2)*τ^2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  unfold tauDensity
  calc
    (2 / Real.pi^2) * τ * Real.sinh (Real.pi*τ) * Real.exp (-t*τ^2)
        ≤ (2 / Real.pi^2) * τ * Real.exp (Real.pi*τ) * Real.exp (-t*τ^2) := by
          gcongr
    _ = ((2 / Real.pi^2) * τ) *
          (Real.exp (Real.pi*τ) * Real.exp (-t*τ^2)) := by ring
    _ ≤ ((2 / Real.pi^2) * τ) *
          (Real.exp (Real.pi^2/(2*t)) * Real.exp (-(t/2)*τ^2)) := by
          exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The actual raw spectral measure has finite Gaussian moments at every
strictly positive time. The factor 2/pi^2 is not renormalized away. -/
theorem gaussian_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun τ : ℝ => Real.exp (-t*τ^2)) tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (by unfold tauDensity; fun_prop)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2
  have hg := (integrable_mul_exp_neg_mul_sq (by positivity : 0 < t/2)).norm.integrableOn
  have hmajor := hg.const_mul ((2 / Real.pi^2) * Real.exp (Real.pi^2/(2*t)))
  apply hmajor.mono'
  · exact (by unfold tauDensity; fun_prop : Measurable
      (fun τ : ℝ => (ENNReal.ofReal (tauDensity τ)).toReal • Real.exp (-t*τ^2))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hd : 0 ≤ tauDensity τ := by
      unfold tauDensity
      exact mul_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr (by positivity))
    simpa only [ENNReal.toReal_ofReal hd, smul_eq_mul, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg hd, abs_of_pos (Real.exp_pos _), abs_of_pos hτ]
      using gaussian_density_bound ht hτ.le

def gaussianMass (t : ℝ) : ℝ := ∫ τ, Real.exp (-t*τ^2) ∂tauMeasure

theorem gaussianMass_nonneg (t : ℝ) : 0 ≤ gaussianMass t :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- The literal positive-time raw KL kernel. -/
def heatKernel (t r s : ℝ) : ℂ :=
  ∫ τ, (Real.exp (-t*τ^2) : ℂ) * K τ r * K τ s ∂tauMeasure

theorem heatKernel_integrable {t : ℝ} (ht : 0 < t) (r s : ℝ) :
    Integrable (fun τ => (Real.exp (-t*τ^2) : ℂ) * K τ r * K τ s) tauMeasure := by
  have hr := (Kzero_pos r).le
  have hs := (Kzero_pos s).le
  apply ((gaussian_integrable ht).mul_const (Kzero r * Kzero s)).mono'
  · exact ((by fun_prop : Measurable (fun τ : ℝ =>
      (Real.exp (-t*τ^2) : ℂ))).mul (K_measurable_order r) |>.mul
      (K_measurable_order s)).aestronglyMeasurable
  · exact Eventually.of_forall fun τ => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-t*τ^2) * ‖K τ r‖ * ‖K τ s‖
            ≤ Real.exp (-t*τ^2) * Kzero r * Kzero s := by
              gcongr <;> exact K_norm_le _ _
        _ = Real.exp (-t*τ^2) * (Kzero r*Kzero s) := by ring

theorem heatKernel_norm_le {t : ℝ} (ht : 0 < t) (r s : ℝ) :
    ‖heatKernel t r s‖ ≤ gaussianMass t * (Kzero r*Kzero s) := by
  have hr := (Kzero_pos r).le
  have hs := (Kzero_pos s).le
  calc
    ‖heatKernel t r s‖ ≤ ∫ τ, Real.exp (-t*τ^2) * (Kzero r*Kzero s) ∂tauMeasure := by
      apply norm_integral_le_of_norm_le ((gaussian_integrable ht).mul_const _)
      exact Eventually.of_forall fun τ => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-t*τ^2)*‖K τ r‖*‖K τ s‖
              ≤ Real.exp (-t*τ^2)*Kzero r*Kzero s := by
                gcongr <;> exact K_norm_le _ _
          _ = _ := by ring
    _ = gaussianMass t * (Kzero r*Kzero s) := integral_mul_const _ _

theorem heatKernel_measurable (t : ℝ) :
    Measurable (fun p : ℝ × ℝ => heatKernel t p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      (Real.exp (-t*p.2^2) : ℂ) * K p.2 p.1.1 * K p.2 p.1.2) := by
    apply Measurable.mul
    · exact (by fun_prop).mul (K_joint_measurable.comp (by fun_prop))
    · exact K_joint_measurable.comp (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Local absolute integrability on every compact spatial set. -/
theorem heatKernel_integrableOn_compact {t : ℝ} (ht : 0 < t)
    {C : Set (ℝ × ℝ)} (hC : IsCompact C) :
    IntegrableOn (fun p : ℝ × ℝ => heatKernel t p.1 p.2) C := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      gaussianMass t * (Kzero p.1*Kzero p.2)) :=
    continuous_const.mul ((Kzero_continuous.comp continuous_fst).mul
      (Kzero_continuous.comp continuous_snd))
  apply (hc.continuousOn.integrableOn_compact hC).mono'
  · exact (heatKernel_measurable t).aestronglyMeasurable
  · exact Eventually.of_forall fun p => heatKernel_norm_le ht p.1 p.2

/-- Absolute Fubini for each compact continuous input, at every radial point. -/
theorem compact_input_joint_integrable {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => (Real.exp (-t*p.1^2) : ℂ) *
      K p.1 r * K p.1 p.2 * f p.2) (tauMeasure.prod volume) := by
  have hr := (Kzero_pos r).le
  have hs : ∀ s, 0 ≤ Kzero s := fun s => (Kzero_pos s).le
  have hspace : Integrable (fun s => Kzero s * ‖f s‖) :=
    (Kzero_continuous.mul hf.norm).integrable_of_hasCompactSupport
      (hc.norm.mul_left)
  apply (((gaussian_integrable ht).mul_const (Kzero r)).mul_prod hspace).mono'
  · exact (by
      apply Measurable.mul
      · apply Measurable.mul
        · exact (by fun_prop).mul ((K_measurable_order r).comp measurable_fst)
        · exact K_joint_measurable
      · exact hf.measurable.comp measurable_snd).aestronglyMeasurable
  · exact Eventually.of_forall fun p => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-t*p.1^2)*‖K p.1 r‖*‖K p.1 p.2‖*‖f p.2‖
            ≤ Real.exp (-t*p.1^2)*Kzero r*Kzero p.2*‖f p.2‖ := by
              gcongr <;> exact K_norm_le _ _
        _ = _ := by ring

/-- The literal compact-input heat-kernel integral equals the damped inverse
KL integral, with exactly the original raw measure and constants. -/
theorem compact_input_fubini {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    (∫ s, heatKernel t r s * f s) =
      ∫ τ, (Real.exp (-t*τ^2) : ℂ) * K τ r * actualKtransform f τ ∂tauMeasure := by
  calc
    (∫ s, heatKernel t r s * f s) =
        ∫ s, ∫ τ, (Real.exp (-t*τ^2) : ℂ) * K τ r * K τ s * f s ∂tauMeasure := by
      congr 1
      funext s
      exact (integral_mul_const _ _).symm
    _ = ∫ τ, ∫ s, (Real.exp (-t*τ^2) : ℂ) * K τ r * K τ s * f s ∂tauMeasure :=
      integral_integral_swap (compact_input_joint_integrable ht f hf hc r).swap
    _ = _ := by
      congr 1
      funext τ
      unfold actualKtransform
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by dsimp [actualKtransform, K]; ring

end
end ImbalancedChen.Part3.ActualKLHeatKernelAbsolute20261026a
