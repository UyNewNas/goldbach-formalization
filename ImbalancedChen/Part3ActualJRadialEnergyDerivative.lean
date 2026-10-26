import ImbalancedChen.Part3ActualJImaginaryRadialJet
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Genuine derivative of the energy of the literal transformed J_(2it).
All real/imaginary norm-square derivatives are computed here and the
actual transformed ODE is consumed from its actual-J supplier. There is
no hEnergy, hODE, monotonicity, or large-q estimate hypothesis.
-/

namespace ImbalancedChen.Part3.ActualJRadialEnergyDerivative20261026b

noncomputable section
open Complex Set
open ActualJImaginaryRadialJet20261026b

def radialEnergy (t q : ℝ) : ℝ :=
  Complex.normSq (radialJFirst t q) + radialPotential t q * Complex.normSq (radialJ t q)

private theorem normSq_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {q : ℝ}
    (hf : HasDerivAt f f' q) :
    HasDerivAt (fun x => Complex.normSq (f x))
      (2 * ((f q).re * f'.re + (f q).im * f'.im)) q := by
  have hr : HasDerivAt (fun x => (f x).re) f'.re q := by
    simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt q hf
  have hi : HasDerivAt (fun x => (f x).im) f'.im q := by
    simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt q hf
  convert (hr.pow 2).add (hi.pow 2) using 1
  · funext x
    simp [Complex.normSq_apply, pow_two]
  · ring

theorem radialPotential_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialPotential t)
      (-(2 * radialCoefficient t / q ^ 3)) q := by
  have h := ((hasDerivAt_const q (radialCoefficient t)).div
    ((hasDerivAt_id q).pow 2) (pow_ne_zero 2 hq.ne')).const_add 1
  convert h using 1
  · rfl
  · field_simp [hq.ne'] <;> ring

/-- The strictly positive inverse-square potential has decreasing energy.
The exact right-hand side is -2*a*|u|^2/q^3. -/
theorem radialEnergy_hasDerivAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (radialEnergy t)
      (-(2 * radialCoefficient t * Complex.normSq (radialJ t q) / q ^ 3)) q := by
  have hu := radialJ_hasDerivAt t hq
  have hv := radialJFirst_hasDerivAt t hq
  have h := (normSq_hasDerivAt hv).add
    ((radialPotential_hasDerivAt t hq).mul (normSq_hasDerivAt hu))
  convert h using 1
  · rfl
  · simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    ring

theorem radialEnergy_deriv_nonpos (t : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (radialEnergy t) q ≤ 0 := by
  rw [(radialEnergy_hasDerivAt t hq).deriv]
  apply neg_nonpos.mpr
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) (radialCoefficient_pos t).le)
      (Complex.normSq_nonneg _)
  · positivity

theorem radialEnergy_nonneg (t : ℝ) {q : ℝ} (hq : 0 < q) :
    0 ≤ radialEnergy t q := by
  unfold radialEnergy
  exact add_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (radialPotential_ge_one t hq))
      (Complex.normSq_nonneg _))

theorem radialJ_norm_sq_le_energy (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖radialJ t q‖ ^ 2 ≤ radialEnergy t q := by
  have hV := mul_le_mul_of_nonneg_right (radialPotential_ge_one t hq)
    (Complex.normSq_nonneg (radialJ t q))
  rw [one_mul] at hV
  rw [← Complex.normSq_eq_norm_sq]
  exact hV.trans (le_add_of_nonneg_left (Complex.normSq_nonneg _))

end
end ImbalancedChen.Part3.ActualJRadialEnergyDerivative20261026b
