import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import ImbalancedChen.Part3ModularFundamentalFiniteMeasure
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual integral SL2 bottom-row bounds for a reduced source point whose
image enters a shrinking positive-height band. The matrix denominator
and the integral nonzero lower-left entry give the bounds, rather than
an assumed lattice count or compact-transporter asymptotic. The final
statement constructs the modular reduction for every original H point.
No quotient norm growth, mean admissibility, or deficiency conclusion is
inferred here.
-/
namespace ImbalancedChen.Part3.SmallHeightReducedMatrixBounds20261026b

noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane
open Gamma0ActualHighCuspTail20261025a
open Gamma0ParabolicBottomRow20261025a
open ModularFundamentalFiniteMeasure20261024z

def smallHeightBand (t : ℝ) : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 ∧ t ≤ z.im ∧ z.im ≤ 2*t}

/-- Determinant one pays the exceptional c=0 row exactly. -/
theorem zero_lowerLeft_abs_lowerRight (g : SL(2, ℤ)) (hc : g 1 0 = 0) :
    |(g 1 1 : ℝ)| = 1 := by
  have had : g 0 0 * g 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using g.det_coe
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨_, hd⟩ | ⟨_, hd⟩ <;>
    simp only [hd, Int.cast_one, Int.cast_neg, abs_one, abs_neg]

/-- The actual physical image-height identity in a form useful for
quantitative counting; its denominator is not an extra input. -/
theorem integral_image_height_denominator (g : SL(2, ℤ)) (w : UpperHalfPlane) :
    (g • w).im *
      (((g 1 0 : ℝ)*w.im)^2 + ((g 1 0 : ℝ)*w.re + (g 1 1 : ℝ))^2) = w.im := by
  let G := SpecialLinearGroup.mapGL ℝ g
  have hD : 0 < Complex.normSq (UpperHalfPlane.denom G w) :=
    UpperHalfPlane.normSq_denom_pos G w.im_ne_zero
  have him : (g • w).im = w.im / Complex.normSq (UpperHalfPlane.denom G w) := by
    change (G • w).im = _
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp only [G, SpecialLinearGroup.det_mapGL, Units.val_one, abs_one, one_mul]
  have heq := (eq_div_iff hD.ne').mp him
  convert heq using 1 <;>
    simp [G, UpperHalfPlane.denom, Complex.normSq] <;> ring

/-- A reduced source point has a genuinely finite quantitative bottom-row
box. Only the lower target height is needed for the nonparabolic bound. -/
theorem reduced_nonzero_lowerLeft_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (g : SL(2, ℤ)) (hc : g 1 0 ≠ 0) (w : UpperHalfPlane)
    (hw : w ∈ ModularGroup.fd) (himage : t ≤ (g • w).im) :
    w.im ≤ 1/t ∧ |(g 1 0 : ℝ)| ≤ 2/t ∧ |(g 1 1 : ℝ)| ≤ 2/t := by
  let c : ℝ := g 1 0
  let d : ℝ := g 1 1
  let D : ℝ := (c*w.im)^2 + (c*w.re+d)^2
  have hwY : (1 : ℝ)/2 ≤ w.im := (modularFD_half_lt_im hw).le
  have hwX : |w.re| ≤ (1 : ℝ)/2 := hw.2
  have hD : 0 ≤ D := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hheight : (g • w).im * D = w.im := integral_image_height_denominator g w
  have htD : t*D ≤ w.im :=
    (mul_le_mul_of_nonneg_right himage hD).trans_eq hheight
  have hty : t*w.im ≤ 1 :=
    (mul_le_mul_of_nonneg_right himage w.im_pos.le).trans (im_smul_mul_im_le_one g hc w)
  have hy : w.im ≤ 1/t := (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hty)
  have hcy : t*c^2*w.im ≤ 1 := by
    apply (mul_le_mul_right w.im_pos).mp
    have hmain : t*(c*w.im)^2 ≤ w.im := by
      dsimp [D] at htD
      nlinarith [mul_nonneg ht.le (sq_nonneg (c*w.re+d))]
    nlinarith
  have htc2 : t*c^2 ≤ 2 := by
    have hmul := mul_nonneg (mul_nonneg ht.le (sq_nonneg c)) (sub_nonneg.mpr hwY)
    nlinarith
  have hct2 : (|c|*t)^2 ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_right htc2 ht.le
    nlinarith [sq_abs c]
  have hcBound : |c| ≤ 2/t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [abs_nonneg c, mul_nonneg (abs_nonneg c) ht.le]
  have hDt2 : t^2*D ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left htD ht.le
    nlinarith
  have hreal2 : (|c*w.re+d|*t)^2 ≤ 1 := by
    have hmul := mul_nonneg (sq_nonneg t) (sq_nonneg (c*w.im))
    dsimp [D] at hDt2
    nlinarith [sq_abs (c*w.re+d)]
  have hreal : |c*w.re+d| ≤ 1/t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [mul_nonneg (abs_nonneg (c*w.re+d)) ht.le]
  have hdTriangle : |d| ≤ |c*w.re+d| + |c|*|w.re| := by
    calc
      |d| = |(c*w.re+d)-(c*w.re)| := by congr 1 <;> ring
      _ ≤ |c*w.re+d| + |c*w.re| := abs_sub _ _
      _ = _ := by rw [abs_mul]
  refine ⟨hy, hcBound, ?_⟩
  calc
    |d| ≤ |c*w.re+d| + |c|*|w.re| := hdTriangle
    _ ≤ 1/t + (2/t)*((1 : ℝ)/2) :=
      add_le_add hreal (mul_le_mul hcBound hwX (abs_nonneg _) (by positivity))
    _ = 2/t := by ring

theorem reduced_smallHeight_bottomRow_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (g : SL(2, ℤ)) (w : UpperHalfPlane) (hw : w ∈ ModularGroup.fd)
    (himage : g • w ∈ smallHeightBand t) :
    |(g 1 0 : ℝ)| ≤ 2/t ∧ |(g 1 1 : ℝ)| ≤ 2/t ∧
      (g 1 0 = 0 ∨ w.im ≤ 1/t) := by
  by_cases hc : g 1 0 = 0
  · have htwo : (1 : ℝ) ≤ 2/t := (le_div_iff₀ ht).mpr (by linarith)
    exact ⟨by simp only [hc, Int.cast_zero, abs_zero]; positivity,
      by rw [zero_lowerLeft_abs_lowerRight g hc]; exact htwo, Or.inl hc⟩
  · obtain ⟨hy, hcb, hdb⟩ := reduced_nonzero_lowerLeft_bounds ht ht1 g hc w hw himage.2.1
    exact ⟨hcb, hdb, Or.inr hy⟩

/-- Every original point has an ACTUAL modular reduction, and the
right-composed matrices act on it exactly as the original matrices act
on the original point. No abstract reduction field is supplied. -/
theorem exists_actual_reduction_with_row_bounds (z : UpperHalfPlane)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ h : SL(2, ℤ), h • z ∈ ModularGroup.fd ∧
      ∀ g : SL(2, ℤ), g • z ∈ smallHeightBand t →
        |((g*h⁻¹) 1 0 : ℝ)| ≤ 2/t ∧ |((g*h⁻¹) 1 1 : ℝ)| ≤ 2/t := by
  obtain ⟨h, hh⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨h, hh, ?_⟩
  intro g hg
  have ha : (g*h⁻¹) • (h • z) = g • z := by simp only [mul_smul, inv_smul_smul]
  have hb := reduced_smallHeight_bottomRow_bounds ht ht1 (g*h⁻¹) (h • z) hh (ha.symm ▸ hg)
  exact ⟨hb.1, hb.2.1⟩

end
end ImbalancedChen.Part3.SmallHeightReducedMatrixBounds20261026b
