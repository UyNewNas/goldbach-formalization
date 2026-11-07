import ImbalancedChen.Part3GeneralActualRadialGreen
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The literal general-order I/K Green integral applied to continuous compact
forcing. Joint integrability and the interchange of the two whole-line
integrals are proved, not assumed. The resulting distributional inverse
uses the actual normalized Green identity on 0 < Re nu < 1.

This module does not assert an L2 bound, a closed form-domain membership,
or identification with a Hilbert-space Riesz inverse.
-/
namespace ImbalancedChen.Part3.ActualGreenCompactForcing20261025a
noncomputable section
open Set MeasureTheory
open scoped Topology
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKRadialRegularitySourceOnly

/-- Actual Green convolution; no abstract solution or inverse is selected. -/
def greenForcing (nu : ℂ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s : ℝ, actualRadialGreen nu s r * f s

theorem actualGreen_symmetric (nu : ℂ) (s r : ℝ) :
    actualRadialGreen nu s r = actualRadialGreen nu r s := by
  unfold actualRadialGreen kernel
  rw [min_comm r s, max_comm r s]

theorem actualGreen_joint_continuous {nu : ℂ} (hnu : -1 < nu.re) :
    Continuous (fun p : ℝ × ℝ => actualRadialGreen nu p.1 p.2) := by
  exact ((radialI_C2 hnu).continuous.comp (continuous_snd.min continuous_fst)).mul
    ((radialK_C2 nu).continuous.comp (continuous_snd.max continuous_fst))

theorem greenForcing_integrand_integrable {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun s : ℝ => actualRadialGreen nu s r * f s) := by
  have hk : Continuous (fun s : ℝ => actualRadialGreen nu s r) := by
    simpa only [actualGreen_symmetric nu r] using actualRadialGreen_continuous hnu r
  exact (hk.mul hf).integrable_of_hasCompactSupport hfc.mul_left

/-- Compact support in each of the two distinct variables supplies genuine
compact support on the product, even though the Green kernel itself is not compact. -/
theorem jointGreen_compact (nu : ℂ) {f g : ℝ → ℂ}
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun p : ℝ × ℝ =>
      actualRadialGreen nu p.1 p.2 * f p.1 * g p.2) := by
  apply HasCompactSupport.intro (hfc.isCompact.prod hgc.isCompact)
  intro p hp
  by_cases hf : p.1 ∈ tsupport f
  · have hg : p.2 ∉ tsupport g := fun hg => hp ⟨hf, hg⟩
    rw [image_eq_zero_of_notMem_tsupport hg, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hf, mul_zero, zero_mul]

theorem jointGreen_integrable {nu : ℂ} (hnu : -1 < nu.re)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ =>
      actualRadialGreen nu p.1 p.2 * f p.1 * g p.2)
      ((volume : Measure ℝ).prod volume) := by
  exact (((actualGreen_joint_continuous hnu).mul (hf.comp continuous_fst)).mul
    (hg.comp continuous_snd)).integrable_of_hasCompactSupport
      (jointGreen_compact nu hfc hgc)

/-- The product of the actual solution with any continuous compact test
is integrable; this is derived from product-measure integrability. -/
theorem greenForcing_test_integrable {nu : ℂ} (hnu : -1 < nu.re)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun r : ℝ => greenForcing nu f r * g r) := by
  have h := (jointGreen_integrable hnu hf hg hfc hgc).integral_prod_right
  simpa only [greenForcing, integral_mul_const] using h

/-- Actual Fubini pairing, with all absolute integrability supplied above. -/
theorem greenForcing_pairing {nu : ℂ} (hnu : -1 < nu.re)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    (∫ r : ℝ, greenForcing nu f r * g r) =
      ∫ s : ℝ, f s * (∫ r : ℝ, actualRadialGreen nu s r * g r) := by
  calc
    _ = ∫ r : ℝ, ∫ s : ℝ, actualRadialGreen nu s r * f s * g r := by
      simp only [greenForcing, integral_mul_const]
    _ = ∫ s : ℝ, ∫ r : ℝ, actualRadialGreen nu s r * f s * g r :=
      (integral_integral_swap (jointGreen_integrable hnu hf hg hfc hgc)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with r
      ring

theorem actual_operator_continuous (nu : ℂ) {phi : ℝ → ℂ}
    (hphi : ContDiff ℝ 2 phi) : Continuous (operator (potential nu) phi) := by
  have hd : ContDiff ℝ 1 (deriv phi) := by
    have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) phi := by simpa using hphi
    exact (contDiff_succ_iff_deriv.mp h).2.2
  have hV : Continuous (potential nu) := by unfold potential; fun_prop
  exact hd.continuous_deriv_one.neg.add (hV.mul hphi.continuous)

theorem actual_operator_compact (nu : ℂ) {phi : ℝ → ℂ}
    (hc : HasCompactSupport phi) : HasCompactSupport (operator (potential nu) phi) := by
  exact hc.deriv.deriv.neg.add hc.mul_left

/-- The literal Green convolution solves the actual radial equation in
distributions for continuous compact complex forcing. There is no assumed
inverse identity, Fubini condition, ODE, Wronskian, or spectral premise. -/
theorem greenForcing_weak_equation {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (phi : ℝ → ℂ) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, greenForcing nu f r * operator (potential nu) phi r) =
      ∫ s : ℝ, f s * phi s := by
  have hi : -1 < nu.re := by linarith
  rw [greenForcing_pairing hi hf (actual_operator_continuous nu hphi)
    hfc (actual_operator_compact nu hc)]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [show (∫ r : ℝ, actualRadialGreen nu s r * operator (potential nu) phi r) =
    phi s from actualRadialGreen_weak_identity hnu hnuUpper s phi hphi hc]

/-- The other inverse relation holds pointwise on the actual compact C2
operator core. Symmetry is algebraic and valid also for complex order. -/
theorem greenForcing_of_operator {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1)
    (phi : ℝ → ℂ) (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) (r : ℝ) :
    greenForcing nu (operator (potential nu) phi) r = phi r := by
  unfold greenForcing
  simp only [actualGreen_symmetric nu _ r]
  exact actualRadialGreen_weak_identity hnu hnuUpper r phi hphi hc

theorem greenForcing_add {nu : ℂ} (hnu : -1 < nu.re)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (r : ℝ) :
    greenForcing nu (f + g) r = greenForcing nu f r + greenForcing nu g r := by
  simp only [greenForcing, Pi.add_apply, mul_add]
  exact integral_add (greenForcing_integrand_integrable hnu hf hfc r)
    (greenForcing_integrand_integrable hnu hg hgc r)

theorem greenForcing_smul (nu c : ℂ) (f : ℝ → ℂ) (r : ℝ) :
    greenForcing nu (c • f) r = c * greenForcing nu f r := by
  simp only [greenForcing, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  ring

end
end ImbalancedChen.Part3.ActualGreenCompactForcing20261025a
