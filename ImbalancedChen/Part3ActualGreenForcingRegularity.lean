import ImbalancedChen.Part3ActualGreenCompactForcing
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Explicit cumulative-integral formula for the literal I/K convolution,
its actual first and second derivatives, and smoothness for smooth compact
forcing. No differentiability-under-the-integral hypothesis is imposed:
the min/max integral is split and the ordinary fundamental theorem of
calculus is applied to its two continuous compact densities.
-/
namespace ImbalancedChen.Part3.ActualGreenForcingRegularity20261025a
noncomputable section
open Set MeasureTheory
open scoped Topology
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ActualGreenCompactForcing20261025a

def leftAmplitude (nu : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in Iic r, radialI nu s * f s

def rightAmplitude (nu : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in Ioi r, radialK nu s * f s

private theorem cumulative_left_hasDerivAt {g : ℝ → ℂ}
    (hg : Continuous g) (hgi : Integrable g) (r : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in Iic x, g s) (g r) r := by
  have he : (fun x : ℝ => ∫ s in Iic x, g s) =
      (fun x : ℝ => (∫ s in (0 : ℝ)..x, g s) + ∫ s in Iic (0 : ℝ), g s) := by
    funext x
    exact (sub_eq_iff_eq_add.mp
      (intervalIntegral.integral_Iic_sub_Iic hgi.integrableOn hgi.integrableOn))
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).add_const _

private theorem cumulative_right_hasDerivAt {g : ℝ → ℂ}
    (hg : Continuous g) (hgi : Integrable g) (r : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ s in Ioi x, g s) (-g r) r := by
  have he : (fun x : ℝ => ∫ s in Ioi x, g s) =
      (fun x : ℝ => (∫ s : ℝ, g s) - ∫ s in Iic x, g s) := by
    funext x
    have h := integral_add_compl (s := Iic x) measurableSet_Iic hgi
    rw [compl_Iic] at h
    linear_combination h
  rw [he]
  exact (cumulative_left_hasDerivAt hg hgi r).const_sub _

theorem leftAmplitude_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    HasDerivAt (leftAmplitude nu f) (radialI nu r * f r) r := by
  have hd := (radialI_C2 hnu).continuous.mul hf
  exact cumulative_left_hasDerivAt hd (hd.integrable_of_hasCompactSupport hc.mul_left) r

theorem rightAmplitude_hasDerivAt (nu : ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    HasDerivAt (rightAmplitude nu f) (-(radialK nu r * f r)) r := by
  have hd := (radialK_C2 nu).continuous.mul hf
  exact cumulative_right_hasDerivAt hd (hd.integrable_of_hasCompactSupport hc.mul_left) r

theorem greenForcing_eq_amplitudes {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    greenForcing nu f r = radialK nu r * leftAmplitude nu f r +
      radialI nu r * rightAmplitude nu f r := by
  unfold greenForcing
  rw [← integral_add_compl (s := Iic r) measurableSet_Iic
    (greenForcing_integrand_integrable hnu hf hc r), compl_Iic]
  congr 1
  · unfold leftAmplitude
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
    simp only [actualRadialGreen, kernel, min_eq_right hs, max_eq_left hs]
    ring
  · unfold rightAmplitude
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp only [actualRadialGreen, kernel, min_eq_left hs.le, max_eq_right hs.le]
    ring

def greenForcingFirst (nu : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv (radialK nu) r * leftAmplitude nu f r +
    deriv (radialI nu) r * rightAmplitude nu f r

theorem greenForcing_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    HasDerivAt (greenForcing nu f) (greenForcingFirst nu f r) r := by
  have hk := ((radialK_C2 nu).differentiable (by norm_num) r).hasDerivAt
  have hi := ((radialI_C2 hnu).differentiable (by norm_num) r).hasDerivAt
  have ha := leftAmplitude_hasDerivAt hnu hf hc r
  have hb := rightAmplitude_hasDerivAt nu hf hc r
  have he := (hk.mul ha).add (hi.mul hb)
  have hu : greenForcing nu f = fun x => radialK nu x * leftAmplitude nu f x +
      radialI nu x * rightAmplitude nu f x :=
    funext (greenForcing_eq_amplitudes hnu hf hc)
  rw [hu]
  convert he using 1 <;> dsimp [greenForcingFirst] <;> ring

private theorem derivative_C1 {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (deriv u) := by
  have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) u := by simpa using hu
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem greenForcingFirst_hasDerivAt {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (r : ℝ) :
    HasDerivAt (greenForcingFirst nu f)
      (potential nu r * greenForcing nu f r - f r) r := by
  have hn : -1 < nu.re := by linarith
  have hk := ((derivative_C1 (radialK_C2 nu)).differentiable_one r).hasDerivAt
  have hi := ((derivative_C1 (radialI_C2 hn)).differentiable_one r).hasDerivAt
  have he := (hk.mul (leftAmplitude_hasDerivAt hn hf hc r)).add
    (hi.mul (rightAmplitude_hasDerivAt nu hf hc r))
  have hK : deriv (deriv (radialK nu)) r = potential nu r * radialK nu r := by
    have h := actual_radialK_homogeneous nu r
    unfold operator at h
    linear_combination -h
  have hI : deriv (deriv (radialI nu)) r = potential nu r * radialI nu r := by
    have h := actual_radialI_homogeneous hn r
    unfold operator at h
    linear_combination -h
  have hw := actual_radial_source_wronskian hnu hnuUpper r
  convert he using 1
  rw [hK, hI, greenForcing_eq_amplitudes hn hf hc]
  linear_combination (f r) * hw

theorem greenForcing_C2 {nu : ℂ} (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (greenForcing nu f) := by
  have hn : -1 < nu.re := by linarith
  have hd : Differentiable ℝ (greenForcing nu f) :=
    fun r => (greenForcing_hasDerivAt hn hf hc r).differentiableAt
  have he : deriv (greenForcing nu f) = greenForcingFirst nu f :=
    funext (fun r => (greenForcing_hasDerivAt hn hf hc r).deriv)
  have hD : Differentiable ℝ (greenForcingFirst nu f) :=
    fun r => (greenForcingFirst_hasDerivAt hnu hnuUpper hf hc r).differentiableAt
  have hDD : deriv (greenForcingFirst nu f) =
      fun r => potential nu r * greenForcing nu f r - f r :=
    funext (fun r => (greenForcingFirst_hasDerivAt hnu hnuUpper hf hc r).deriv)
  have hV : Continuous (potential nu) := by unfold potential; fun_prop
  have hD1 : ContDiff ℝ 1 (greenForcingFirst nu f) :=
    contDiff_one_iff_deriv.mpr ⟨hD, by rw [hDD]; exact (hV.mul hd.continuous).sub hf⟩
  have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) (greenForcing nu f) :=
    contDiff_succ_iff_deriv.mpr ⟨hd, by simp, by rw [he]; exact hD1⟩
  simpa using h

theorem greenForcing_second_deriv {nu : ℂ} (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    deriv (deriv (greenForcing nu f)) =
      fun r => potential nu r * greenForcing nu f r - f r := by
  have hn : -1 < nu.re := by linarith
  have he : deriv (greenForcing nu f) = greenForcingFirst nu f :=
    funext (fun r => (greenForcing_hasDerivAt hn hf hc r).deriv)
  rw [he]
  exact funext (fun r => (greenForcingFirst_hasDerivAt hnu hnuUpper hf hc r).deriv)

/-- Smooth forcing yields an actual smooth convolution by bootstrapping
its proved second-order equation, rather than assuming kernel smoothness
across the source diagonal. -/
theorem greenForcing_smooth {nu : ℂ} (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (greenForcing nu f) := by
  have hU := greenForcing_C2 hnu hnuUpper hf.continuous hc
  have hD := derivative_C1 hU
  have hV : ContDiff ℝ ∞ (potential nu) := by unfold potential; fun_prop
  have hpair : ∀ n : ℕ,
      ContDiff ℝ (n : ℕ∞ω) (greenForcing nu f) ∧
        ContDiff ℝ (n : ℕ∞ω) (deriv (greenForcing nu f)) := by
    intro n
    induction n with
    | zero => exact ⟨contDiff_zero.mpr hU.continuous, contDiff_zero.mpr hD.continuous⟩
    | succ n ih =>
      have hUn : ContDiff ℝ ((n : ℕ∞ω) + 1) (greenForcing nu f) :=
        contDiff_succ_iff_deriv.mpr
          ⟨hU.differentiable (by norm_num), by simp, ih.2⟩
      have hDn : ContDiff ℝ ((n : ℕ∞ω) + 1) (deriv (greenForcing nu f)) := by
        apply contDiff_succ_iff_deriv.mpr
        refine ⟨hD.differentiable_one, by simp, ?_⟩
        rw [greenForcing_second_deriv hnu hnuUpper hf.continuous hc]
        exact ((hV.of_le (by simp)).mul ih.1).sub (hf.of_le (by simp))
      exact ⟨by simpa using hUn, by simpa using hDn⟩
  exact contDiff_infty.mpr (fun n => (hpair n).1)

end
end ImbalancedChen.Part3.ActualGreenForcingRegularity20261025a
