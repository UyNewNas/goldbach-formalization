import ImbalancedChen.Part3RealOrderKMellinReduction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Absolute Mellin integrability and exact Fubini reduction for the literal
imaginaryOrderK t q = integral exp(-q*cosh u)*cos(2*t*u).
The Mellin exponent is every real s>0, uniformly for all real t. The proof
uses a positive product majorant and |cos|<=1, not an assumed spectral or
Mellin identity. The factor 2 in the actual order convention is retained.

The complex Beta/Gamma evaluation is a separate step. Its parameters
must be s/2 + I*t and s/2 - I*t for this actual K_{2it} definition.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKMellinReduction20261025a

noncomputable section
open Set MeasureTheory Filter
open ImaginaryOrderKBesselSourceOnly
open RealOrderKMellinReduction20261025a

def imaginaryMellinDensity (t s u : ℝ) : ℝ :=
  Real.cos (2 * t * u) * (1 / Real.cosh u) ^ s

private def positiveFiber (s u q : ℝ) : ℝ :=
  Real.exp (Real.log q * (s - 1)) * Real.exp (-(Real.cosh u * q))

private def cosineFiber (t s u q : ℝ) : ℝ :=
  positiveFiber s u q * Real.cos (2 * t * u)

private theorem positiveFiber_nonneg (s u q : ℝ) : 0 ≤ positiveFiber s u q := by
  unfold positiveFiber
  positivity

private theorem positiveFiber_integrable (s u : ℝ) (hs : 0 < s) :
    IntegrableOn (positiveFiber s u) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun q : ℝ => q ^ (s - 1) * Real.exp (-(Real.cosh u * q))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := s - 1) (b := Real.cosh u)
        (by linarith) le_rfl (Real.cosh_pos u))
  apply hbase.congr_fun _ measurableSet_Ioi
  intro q hq
  dsimp only [positiveFiber]
  rw [Real.rpow_def_of_pos hq]

private theorem positiveFiber_q_integral (s u : ℝ) (hs : 0 < s) :
    (∫ q in Ioi (0 : ℝ), positiveFiber s u q) =
      Real.Gamma s * (1 / Real.cosh u) ^ s := by
  calc
    (∫ q in Ioi (0 : ℝ), positiveFiber s u q) =
      ∫ q in Ioi (0 : ℝ), q ^ (s - 1) * Real.exp (-(Real.cosh u * q)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      dsimp only [positiveFiber]
      rw [Real.rpow_def_of_pos hq]
    _ = Real.Gamma s * (1 / Real.cosh u) ^ s := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos u), mul_comm]

private theorem positiveFiber_joint_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => positiveFiber s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => positiveFiber s p.1 p.2) := by
    unfold positiveFiber
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun u => positiveFiber_integrable s u hs)
  · have he : (fun u : ℝ => ∫ q in Ioi (0 : ℝ), ‖positiveFiber s u q‖) =
        fun u : ℝ => Real.Gamma s * mellinDensity 0 s u := by
      funext u
      simp only [mellinDensity, zero_mul, Real.cosh_zero, one_mul]
      rw [← positiveFiber_q_integral s u hs]
      apply integral_congr_ae
      exact ae_of_all _ (fun q => by
        rw [Real.norm_eq_abs, abs_of_nonneg (positiveFiber_nonneg s u q)])
    have hden := (mellinDensity_integrable (α := (0 : ℝ)) (s := s)
      (by simpa using hs)).const_mul (Real.Gamma s)
    simpa only [he] using hden

private theorem cosineFiber_norm_le (t s u q : ℝ) :
    ‖cosineFiber t s u q‖ ≤ positiveFiber s u q := by
  calc
    ‖cosineFiber t s u q‖ = positiveFiber s u q * |Real.cos (2 * t * u)| := by
      simp only [cosineFiber, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (positiveFiber_nonneg s u q)]
    _ ≤ positiveFiber s u q * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (positiveFiber_nonneg s u q)
    _ = positiveFiber s u q := mul_one _

private theorem cosineFiber_joint_integrable (t : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => cosineFiber t s p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => cosineFiber t s p.1 p.2) := by
    unfold cosineFiber positiveFiber
    fun_prop
  exact (positiveFiber_joint_integrable hs).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun p => cosineFiber_norm_le t s p.1 p.2))

private theorem cosineFiber_q_integral (t s u : ℝ) (hs : 0 < s) :
    (∫ q in Ioi (0 : ℝ), cosineFiber t s u q) =
      Real.Gamma s * imaginaryMellinDensity t s u := by
  change (∫ q in Ioi (0 : ℝ), positiveFiber s u q * Real.cos (2 * t * u)) = _
  rw [integral_mul_const, positiveFiber_q_integral s u hs]
  dsimp only [imaginaryMellinDensity]
  ring

private theorem cosineFiber_u_integral (t s : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), cosineFiber t s u q) =
      q ^ (s - 1) * imaginaryOrderK t q := by
  change (∫ u in Ioi (0 : ℝ), cosineFiber t s u q) =
    q ^ (s - 1) * ∫ u in Ioi (0 : ℝ), kIntegrand t q u
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    dsimp only [cosineFiber, positiveFiber, kIntegrand]
    rw [Real.rpow_def_of_pos hq, mul_comm (Real.cosh u) q]
    ring)

/-- Actual K_{2it} Mellin integrability for every real s>0 and t. -/
theorem imaginaryOrderK_mellin_integrable (t : ℝ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun q : ℝ => q ^ (s - 1) * imaginaryOrderK t q) (Ioi 0) := by
  have h := (cosineFiber_joint_integrable t hs).integral_prod_right
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact cosineFiber_u_integral t s hq

/-- Literal imaginary-order Mellin reduction with its actual factor 2t. -/
theorem imaginaryOrderK_mellin_reduction (t : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * imaginaryOrderK t q) =
      Real.Gamma s * ∫ u in Ioi (0 : ℝ), imaginaryMellinDensity t s u := by
  calc
    (∫ q in Ioi (0 : ℝ), q ^ (s - 1) * imaginaryOrderK t q) =
        ∫ q in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), cosineFiber t s u q := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact (cosineFiber_u_integral t s hq).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ q in Ioi (0 : ℝ), cosineFiber t s u q :=
      (integral_integral_swap (cosineFiber_joint_integrable t hs)).symm
    _ = Real.Gamma s * ∫ u in Ioi (0 : ℝ), imaginaryMellinDensity t s u := by
      simp only [cosineFiber_q_integral t s _ hs, integral_const_mul]

end
end ImbalancedChen.Part3.ImaginaryOrderKMellinReduction20261025a
