import ImbalancedChen.Part3ActualRealOrderJRadialJet
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual real-order ordinary J energy is decreasing when |nu|<=1/2.
The native energy derivative is -2*(1/4-nu^2)*|u|^2/q^3. Thus actual J_nu
has an explicit q^(-1/2) bound from initial energy and a genuine absolute
Mellin tail for Re(s)<1/2. This is local special-function analysis, not a
complementary-series completeness, spectral gap, or 7/32 theorem.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJLargeQ20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly ActualRealOrderJRadialJet20261026b

def realRadialEnergy (nu q : ℝ) : ℝ :=
  ‖realRadialJFirst nu q‖ ^ 2 + realRadialPotential nu q * ‖realRadialJ nu q‖ ^ 2
def realLargeQAmplitude (nu : ℝ) : ℝ := Real.sqrt (realRadialEnergy nu 1)

theorem realRadialPotential_hasDerivAt (nu : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (realRadialPotential nu) (-(2 * realRadialCoefficient nu / q ^ 3)) q := by
  have h := ((hasDerivAt_const q (realRadialCoefficient nu)).div
    ((hasDerivAt_id q).pow 2) (pow_ne_zero 2 hq.ne')).const_add 1
  convert h using 1 <;> unfold realRadialPotential <;> field_simp [hq.ne'] <;> ring

theorem realRadialEnergy_hasDerivAt {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (realRadialEnergy nu)
      (-(2 * realRadialCoefficient nu * ‖realRadialJ nu q‖ ^ 2 / q ^ 3)) q := by
  have h := ((realRadialJFirst_hasDerivAt hnu hq).norm_sq).add
    ((realRadialPotential_hasDerivAt nu hq).mul ((realRadialJ_hasDerivAt hnu hq).norm_sq))
  convert h using 1
  · rfl
  · simp only [inner_smul_right]
    rw [real_inner_comm (realRadialJ nu q) (realRadialJFirst nu q)]
    ring

theorem realRadialEnergy_nonneg {nu : ℝ} (hnu : |nu| ≤ 1 / 2) (q : ℝ) :
    0 ≤ realRadialEnergy nu q := by
  unfold realRadialEnergy
  exact add_nonneg (sq_nonneg _) (mul_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (realRadialPotential_ge_one hnu q)) (sq_nonneg _))

theorem realRadialJ_norm_sq_le_energy {nu : ℝ} (hnu : |nu| ≤ 1 / 2) (q : ℝ) :
    ‖realRadialJ nu q‖ ^ 2 ≤ realRadialEnergy nu q := by
  have h := mul_le_mul_of_nonneg_right (realRadialPotential_ge_one hnu q) (sq_nonneg ‖realRadialJ nu q‖)
  unfold realRadialEnergy
  nlinarith [sq_nonneg ‖realRadialJFirst nu q‖]

theorem realRadialEnergy_antitoneOn {nu : ℝ} (hnu : |nu| ≤ 1 / 2) :
    AntitoneOn (realRadialEnergy nu) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (0 : ℝ))
  · intro q hq
    exact (realRadialEnergy_hasDerivAt hnu hq).continuousAt.continuousWithinAt
  · intro q hq
    exact (realRadialEnergy_hasDerivAt hnu (interior_subset hq)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq0 : 0 < q := interior_subset hq
    rw [(realRadialEnergy_hasDerivAt hnu hq0).deriv]
    apply neg_nonpos.mpr
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (realRadialCoefficient_nonneg hnu))
      (sq_nonneg _)) (by positivity)

theorem generalJ_real_large_q_bound {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 1 ≤ q) :
    ‖generalJ (nu : ℂ) q‖ ≤ realLargeQAmplitude nu / Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hE := realRadialEnergy_antitoneOn hnu (show (1 : ℝ) ∈ Ioi 0 by norm_num) hq0 hq
  have hn : ‖realRadialJ nu q‖ ≤ realLargeQAmplitude nu :=
    Real.le_sqrt_of_sq_le ((realRadialJ_norm_sq_le_energy hnu q).trans hE)
  rw [realRadialJ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg q)] at hn
  apply (le_div_iff₀ (Real.sqrt_pos.2 hq0)).2
  simpa only [mul_comm] using hn

theorem integrableOn_generalJ_real_Mellin_tail {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hs : s.re < 1 / 2) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (s - 1) * generalJ (nu : ℂ) q) (Ioi 1) := by
  have hc : ContinuousOn (fun q : ℝ => (q : ℂ) ^ (s - 1) * generalJ (nu : ℂ) q) (Ioi 1) := by
    intro q hq
    have hq0 : 0 < q := lt_trans (by norm_num) hq
    exact ((Complex.continuousAt_ofReal_cpow_const q (s - 1) (Or.inr hq0.ne')).mul
      (generalJ_differentiableAt (real_order_lower hnu) hq0).continuousAt).continuousWithinAt
  have hi : IntegrableOn (fun q : ℝ => realLargeQAmplitude nu * q ^ (s.re - 3 / 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 3 / 2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (realLargeQAmplitude nu)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    q ^ (s.re - 1) * ‖generalJ (nu : ℂ) q‖ ≤ q ^ (s.re - 1) * (realLargeQAmplitude nu / Real.sqrt q) :=
      mul_le_mul_of_nonneg_left (generalJ_real_large_q_bound hnu hq.le) (Real.rpow_nonneg hq0.le _)
    _ = realLargeQAmplitude nu * (q ^ (s.re - 1) / q ^ (1 / 2 : ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
    _ = realLargeQAmplitude nu * q ^ (s.re - 3 / 2) := by
      rw [← Real.rpow_sub hq0]
      congr 1
      congr 1
      ring

end
end ImbalancedChen.Part3.ActualRealOrderJLargeQ20261026b
