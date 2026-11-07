import ImbalancedChen.Part3ActualJRadialEnergyDerivative
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual fixed-imaginary-order large-q J bound from decreasing native radial
energy. It also supplies genuine absolute Mellin integrability at infinity
for Re s<1/2. No near-zero convergence theorem is imported or bypassed.
No Mellin evaluation or automorphic normalization is asserted.
-/

namespace ImbalancedChen.Part3.ActualJLargeQEnergyBound20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly ActualJImaginaryRadialJet20261026b
open ActualJRadialEnergyDerivative20261026b

def largeQAmplitude (t : ℝ) : ℝ := Real.sqrt (radialEnergy t 1)

theorem largeQAmplitude_nonneg (t : ℝ) : 0 ≤ largeQAmplitude t :=
  Real.sqrt_nonneg _

theorem radialEnergy_antitoneOn (t : ℝ) : AntitoneOn (radialEnergy t) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
  · intro q hq
    exact (radialEnergy_hasDerivAt t hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (radialEnergy_hasDerivAt t (interior_subset hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    exact radialEnergy_deriv_nonpos t (interior_subset hq)

theorem radialJ_norm_le_amplitude (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ‖radialJ t q‖ ≤ largeQAmplitude t := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hE : radialEnergy t q ≤ radialEnergy t 1 :=
    radialEnergy_antitoneOn t (by norm_num) hq0 hq
  exact Real.le_sqrt_of_sq_le ((radialJ_norm_sq_le_energy t hq0).trans hE)

/-- Actual O(q^(-1/2)) bound. Its constant is explicit actual initial
energy at q=1, not a supplied asymptotic or boundedness hypothesis. -/
theorem generalJ_large_q_bound (t : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    ‖generalJ (2 * I * (t : ℂ)) q‖ ≤ largeQAmplitude t / Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have h := radialJ_norm_le_amplitude t hq
  rw [radialJ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q)] at h
  apply (le_div_iff₀ (Real.sqrt_pos.2 hq0)).2
  simpa only [mul_comm] using h

theorem exists_generalJ_large_q_bound (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 1 ≤ q →
      ‖generalJ (2 * I * (t : ℂ)) q‖ ≤ C / Real.sqrt q := by
  exact ⟨largeQAmplitude t, largeQAmplitude_nonneg t, fun _ hq => generalJ_large_q_bound t hq⟩

/-- This is a tail-only result. It requires no convergence statement at
q=0, and hence does not consume any held small-q Mellin source. -/
theorem integrableOn_generalJ_Mellin_tail {s : ℂ} (hs : s.re < 1 / 2) (t : ℝ) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (s - 1) *
      generalJ (2 * I * (t : ℂ)) q) (Ioi 1) := by
  have hnu : -1 < (2 * I * (t : ℂ)).re := by simp
  have hc : ContinuousOn (fun q : ℝ => (q : ℂ) ^ (s - 1) *
      generalJ (2 * I * (t : ℂ)) q) (Ioi 1) := by
    intro q hq
    have hq0 : 0 < q := lt_trans (by norm_num) hq
    have hp : ContinuousAt (fun q : ℝ => (q : ℂ) ^ (s - 1)) q := by
      exact Complex.continuousAt_ofReal_cpow_const q (s - 1) (Or.inr hq0.ne')
    exact (hp.mul (generalJ_differentiableAt hnu hq0).continuousAt).continuousWithinAt
  have hi : IntegrableOn (fun q : ℝ => largeQAmplitude t * q ^ (s.re - 3 / 2))
      (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 3 / 2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (largeQAmplitude t)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    q ^ (s.re - 1) * ‖generalJ (2 * I * (t : ℂ)) q‖ ≤
        q ^ (s.re - 1) * (largeQAmplitude t / Real.sqrt q) :=
      mul_le_mul_of_nonneg_left (generalJ_large_q_bound t hq.le) (Real.rpow_nonneg hq0.le _)
    _ = largeQAmplitude t * (q ^ (s.re - 1) / q ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = largeQAmplitude t * q ^ (s.re - 3 / 2) := by
      rw [← Real.rpow_sub hq0]
      congr 1
      congr 1
      ring

end
end ImbalancedChen.Part3.ActualJLargeQEnergyBound20261026b
