import ImbalancedChen.Part3ActualKUnequalPositiveShear
import ImbalancedChen.Part3ComplexOrderKMellinGamma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The genuine positive dilation of the actual K_0 Mellin integral. Its
complex power coefficient and real Jacobian are proved pointwise. The
existing actual one-K Mellin supplier then gives both absolute
convergence and the Gamma value. A separate exact norm-integral scaling
identity is retained for the unequal-distance two-variable L1 argument.
-/

namespace ImbalancedChen.Part3.ActualKZeroScaledMellin20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ComplexOrderKMellinReduction20261025a ComplexOrderKMellinGamma20261025a

/-- Measurability follows from the literal parameter integral, even at
parameters where its Bochner integral is defined to be zero. -/
theorem actualK_measurable (nu : ℂ) : Measurable (complexOrderK nu) := by
  have hcont : Continuous (fun p : ℝ × ℝ => complexOrderIntegrand nu p.1 p.2) := by
    unfold complexOrderIntegrand
    fun_prop
  have hm : StronglyMeasurable (fun q : ℝ =>
      ∫ u in Ioi (0 : ℝ), complexOrderIntegrand nu q u) :=
    hcont.stronglyMeasurable.integral_prod_right'
  exact hm.measurable

def baseZeroMellin (s : ℂ) (q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * complexOrderK 0 q

def scaledZeroMellin (s : ℂ) (c q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * complexOrderK 0 (c * q)

def zeroMellinGamma (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2

theorem baseZeroMellin_integrable {s : ℂ} (hs : 0 < s.re) :
    Integrable (baseZeroMellin s) positiveMeasure := by
  exact complexOrderK_mellin_integrable (ν := 0) (by simpa using hs)

theorem baseZeroMellin_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ q in Ioi (0 : ℝ), baseZeroMellin s q) = zeroMellinGamma s := by
  have h := complexOrderK_mellin_eq_gamma (ν := 0) (s := s) (by simpa using hs)
  simpa [baseZeroMellin, zeroMellinGamma, pow_two, mul_assoc] using h

/-- The complex Mellin scale and actual real Jacobian agree exactly. -/
theorem scaledZeroMellin_jacobian (s : ℂ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    scaledZeroMellin s c q =
      (c : ℂ) ^ (-s) * ((c : ℂ) * baseZeroMellin s (c * q)) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcstep : (c : ℂ) * (c : ℂ) ^ (s - 1) = (c : ℂ) ^ s := by
    calc
      _ = (c : ℂ) ^ (1 : ℂ) * (c : ℂ) ^ (s - 1) := by rw [Complex.cpow_one]
      _ = (c : ℂ) ^ ((1 : ℂ) + (s - 1)) := (Complex.cpow_add _ _ hcC).symm
      _ = _ := by congr 1; ring
  have hcancel : (c : ℂ) ^ (-s) * (c : ℂ) * (c : ℂ) ^ (s - 1) = 1 := by
    rw [mul_assoc, hcstep, ← Complex.cpow_add _ _ hcC]
    simp only [neg_add_cancel, Complex.cpow_zero]
  unfold scaledZeroMellin baseZeroMellin
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hq.le]
  calc
    _ = 1 * ((q : ℂ) ^ (s - 1) * complexOrderK 0 (c * q)) := by ring
    _ = ((c : ℂ) ^ (-s) * (c : ℂ) * (c : ℂ) ^ (s - 1)) *
        ((q : ℂ) ^ (s - 1) * complexOrderK 0 (c * q)) := by rw [hcancel]
    _ = _ := by ring

theorem scaledZeroMellin_integrable {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    Integrable (scaledZeroMellin s c) positiveMeasure := by
  have hcomp : Integrable (fun q => baseZeroMellin s (c * q)) positiveMeasure := by
    apply (integrableOn_Ioi_comp_mul_left_iff (baseZeroMellin s) 0 hc).mpr
    simpa only [mul_zero] using baseZeroMellin_integrable hs
  apply ((hcomp.const_mul (c : ℂ)).const_mul ((c : ℂ) ^ (-s))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact (scaledZeroMellin_jacobian s hc hq).symm

/-- Exact absolute-integral scaling; this equality is independent of the
Gamma evaluation and exposes the power c^(-Re s) needed by joint L1. -/
theorem scaledZeroMellin_norm_integral (s : ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ q in Ioi (0 : ℝ), ‖scaledZeroMellin s c q‖) =
      c ^ (-s.re) * ∫ u in Ioi (0 : ℝ), ‖baseZeroMellin s u‖ := by
  have hscale := integral_comp_mul_left_Ioi' (fun u => ‖baseZeroMellin s u‖) 0 hc
  rw [mul_zero, smul_eq_mul] at hscale
  calc
    _ = ∫ q in Ioi (0 : ℝ), ‖(c : ℂ) ^ (-s)‖ * (c * ‖baseZeroMellin s (c * q)‖) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      rw [scaledZeroMellin_jacobian s hc hq, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    _ = ‖(c : ℂ) ^ (-s)‖ *
        (c * ∫ q in Ioi (0 : ℝ), ‖baseZeroMellin s (c * q)‖) := by
      rw [integral_const_mul, integral_const_mul]
    _ = ‖(c : ℂ) ^ (-s)‖ * ∫ u in Ioi (0 : ℝ), ‖baseZeroMellin s u‖ := by rw [hscale]
    _ = _ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hc, Complex.neg_re]

/-- The actual scaled K_0 Mellin integral, with arbitrary complex s in
the full convergence half-plane Re s>0. -/
theorem scaledZeroMellin_integral {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    (∫ q in Ioi (0 : ℝ), scaledZeroMellin s c q) =
      zeroMellinGamma s * (c : ℂ) ^ (-s) := by
  have hscale := integral_comp_mul_left_Ioi' (baseZeroMellin s) 0 hc
  rw [mul_zero, Complex.real_smul] at hscale
  calc
    _ = ∫ q in Ioi (0 : ℝ), (c : ℂ) ^ (-s) * ((c : ℂ) * baseZeroMellin s (c * q)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      exact scaledZeroMellin_jacobian s hc hq
    _ = (c : ℂ) ^ (-s) * ((c : ℂ) *
        ∫ q in Ioi (0 : ℝ), baseZeroMellin s (c * q)) := by
      rw [integral_const_mul, integral_const_mul]
    _ = _ := by rw [hscale, baseZeroMellin_integral hs]; ring

end
end ImbalancedChen.Part3.ActualKZeroScaledMellin20261026b
