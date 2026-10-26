import ImbalancedChen.Part3RationalCuspHoroballDisks

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Quantitative actual column bounds for a high cusp image meeting a fixed
coordinate rectangle.  A point z in g{Im>=H} satisfies
  H*c^2*Im(z)<=1 and H*(a-c*Re(z))^2<=Im(z).
If |Re(z)|<=X and eps<=Im(z)<=M, then
 c^2<=1/(H*eps), a^2<=2*X^2/(H*eps)+2*M/H.
This retains the literal column a,c, unlike qualitative parabolic local
finiteness.  It imports no held normalized frame or quotient transport.
-/
namespace ImbalancedChen.Part3.CuspColumnRectangleBudget20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b

theorem inverse_height_weighted_denominator (g : SL(2, ℝ)) (H : ℝ)
    {z : UpperHalfPlane} (hz : z ∈ g • heightHalfSpace H) :
    H*inverseHeightDenominator g z ≤ z.im := by
  have hcoord := (mem_smul_set_iff_inv_smul_mem).mp hz
  change H ≤ (g⁻¹ • z).im at hcoord
  rw [inverse_mobius_height] at hcoord
  exact (le_div_iff₀ (inverseHeightDenominator_pos g z)).mp hcoord

/-- Literal denominator-column budget at any actual high image point. -/
theorem high_image_denominator_column_bound (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    {z : UpperHalfPlane} (hz : z ∈ g • heightHalfSpace H) :
    H*(g 1 0)^2*z.im ≤ 1 := by
  have hden := inverse_height_weighted_denominator g H hz
  unfold inverseHeightDenominator at hden
  have hs : (H*(g 1 0)^2*z.im)*z.im ≤ 1*z.im := by
    nlinarith [mul_nonneg hH.le (sq_nonneg (g 0 0-g 1 0*z.re))]
  exact (mul_le_mul_right z.im_pos).mp hs

/-- The residual numerator column is controlled at the same actual point. -/
theorem high_image_residual_column_bound (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    {z : UpperHalfPlane} (hz : z ∈ g • heightHalfSpace H) :
    H*(g 0 0-g 1 0*z.re)^2 ≤ z.im := by
  have hden := inverse_height_weighted_denominator g H hz
  unfold inverseHeightDenominator at hden
  nlinarith [mul_nonneg hH.le (sq_nonneg (g 1 0*z.im))]

/-- Exact explicit column-square box from a bounded physical rectangle,
including c=0 without a separate primitive-column assumption. -/
theorem rectangle_column_square_bounds (g : SL(2, ℝ)) {H eps X M : ℝ}
    (hH : 0 < H) (heps : 0 < eps) (hX : 0 ≤ X)
    {z : UpperHalfPlane} (hz : z ∈ g • heightHalfSpace H)
    (hx : |z.re| ≤ X) (hylo : eps ≤ z.im) (hyhi : z.im ≤ M) :
    (g 1 0)^2 ≤ 1/(H*eps) ∧
      (g 0 0)^2 ≤ 2*X^2/(H*eps)+2*M/H := by
  have hcpoint := high_image_denominator_column_bound g hH hz
  have hrpoint := high_image_residual_column_bound g hH hz
  have hcprod : (g 1 0)^2*(H*eps) ≤ 1 := by
    have hmono := mul_le_mul_of_nonneg_left hylo (mul_nonneg hH.le (sq_nonneg (g 1 0)))
    nlinarith [hmono]
  have hc : (g 1 0)^2 ≤ 1/(H*eps) := (le_div_iff₀ (mul_pos hH heps)).mpr hcprod
  have hres : (g 0 0-g 1 0*z.re)^2 ≤ M/H := by
    apply (le_div_iff₀ hH).mpr
    nlinarith [hrpoint]
  have hxSq : z.re^2 ≤ X^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg z.re) hX).mpr hx
    simpa only [sq_abs] using hh
  have hcx := mul_le_mul_of_nonneg_left hxSq (sq_nonneg (g 1 0))
  have ha : (g 0 0)^2 ≤ 2*(g 1 0)^2*X^2+2*M/H := by
    nlinarith [sq_nonneg (g 0 0-2*g 1 0*z.re)]
  have hcxBound := mul_le_mul_of_nonneg_right hc (sq_nonneg X)
  refine ⟨hc, ?_⟩
  calc
    _ ≤ 2*(g 1 0)^2*X^2+2*M/H := ha
    _ ≤ 2*(1/(H*eps))*X^2+2*M/H := by nlinarith [hcxBound]
    _ = 2*X^2/(H*eps)+2*M/H := by ring

end
end ImbalancedChen.Part3.CuspColumnRectangleBudget20261026b
