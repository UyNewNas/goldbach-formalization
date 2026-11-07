import ImbalancedChen.Part3ScalarStieltjesPoissonInversion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The actual finite-measure Cauchy resolvent F(z)=integral (x-z)^(-1) dmu
has an integrable kernel above the real axis. Its literal imaginary part
is the positive Poisson kernel integral. The proved scalar interval
inversion therefore applies directly to F(t+i*epsilon), with both endpoint
half-atoms and with a separate atom-free endpoint corollary.

There is no operator spectral measure or operator Stone theorem premise.
Constructing an actual spectral measure remains a separate obligation.
-/

namespace ImbalancedChen.Part3.ScalarCauchyResolventInversion20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ScalarStieltjesPoissonInversion20261025a

def cauchyResolvent (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂μ

private def upperKernel (ε t x : ℝ) : ℂ :=
  ((x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))⁻¹

private theorem upper_den_im (ε t x : ℝ) :
    ((x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I)).im = -ε := by simp

private theorem upper_den_ne_zero {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    (x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I) ≠ 0 := by
  intro hz
  have h := congrArg Complex.im hz
  rw [upper_den_im] at h
  simp only [Complex.zero_im] at h
  linarith

private theorem upperKernel_continuous {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Continuous (upperKernel ε t) := by
  have hc : Continuous (fun x : ℝ => (x : ℂ) -
      ((t : ℂ) + (ε : ℂ) * Complex.I)) := by fun_prop
  exact hc.inv₀ (upper_den_ne_zero hε t)

/-- A true finite-measure domination bound for the actual resolvent kernel. -/
private theorem upperKernel_norm_le {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    ‖upperKernel ε t x‖ ≤ ε⁻¹ := by
  have hnorm : ε ≤ ‖(x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I)‖ := by
    have h := Complex.abs_im_le_norm ((x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I))
    simpa only [upper_den_im, abs_neg, abs_of_pos hε] using h
  rw [upperKernel, norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le hε hnorm) hε).2 hnorm

theorem cauchyResolvent_upper_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x : ℝ => ((x : ℂ) -
      ((t : ℂ) + (ε : ℂ) * Complex.I))⁻¹) μ := by
  exact (integrable_const ε⁻¹).mono' (upperKernel_continuous hε t).aestronglyMeasurable
    (ae_of_all _ (upperKernel_norm_le hε t))

private theorem upperKernel_im (ε t x : ℝ) :
    (upperKernel ε t x).im = ε / ((x - t) ^ 2 + ε ^ 2) := by
  have hnorm : Complex.normSq ((x : ℂ) - ((t : ℂ) + (ε : ℂ) * Complex.I)) =
      (x - t) ^ 2 + ε ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
    ring
  rw [upperKernel, Complex.inv_im, upper_den_im, hnorm]
  simp

/-- Literal imaginary part of the actual Cauchy resolvent above the real line. -/
theorem cauchyResolvent_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (cauchyResolvent μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im =
      ∫ x : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂μ := by
  rw [cauchyResolvent, ← integral_im (cauchyResolvent_upper_integrable μ hε t)]
  apply integral_congr_ae
  exact ae_of_all _ (upperKernel_im ε t)

theorem cauchyResolvent_im_div_pi (μ : Measure ℝ) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (1 / Real.pi) * (cauchyResolvent μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im =
      ∫ x : ℝ, poissonKernel ε t x ∂μ := by
  rw [cauchyResolvent_im μ hε t, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only [poissonKernel]; ring)

def cauchyIntervalMass (μ : Measure ℝ) (a b ε : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in a..b,
    (cauchyResolvent μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im

theorem cauchyIntervalMass_eq_poisson (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    cauchyIntervalMass μ a b ε = poissonIntervalMass μ a b ε := by
  unfold cauchyIntervalMass poissonIntervalMass
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  exact cauchyResolvent_im_div_pi μ hε t

/-- Actual finite-measure Stieltjes inversion of the Cauchy resolvent,
retaining its two endpoint half-atoms. -/
theorem cauchyResolvent_interval_inversion (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) :
    Tendsto (cauchyIntervalMass μ a b) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  apply (poissonIntervalMass_tendsto μ hab).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (cauchyIntervalMass_eq_poisson μ a b hε).symm

/-- At atom-free endpoints this is exactly the open-interval measure. -/
theorem cauchyResolvent_interval_inversion_no_endpoint_atoms (μ : Measure ℝ)
    [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b)
    (ha : μ {a} = 0) (hb : μ {b} = 0) :
    Tendsto (cauchyIntervalMass μ a b) (𝓝[>] 0) (𝓝 (μ.real (Ioo a b))) := by
  simpa [measureReal_def, ha, hb] using cauchyResolvent_interval_inversion μ hab

end
end ImbalancedChen.Part3.ScalarCauchyResolventInversion20261025a
