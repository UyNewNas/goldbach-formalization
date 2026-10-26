import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
A new independent spatial primitive, using only pinned Mathlib.
For an actual real SL2 matrix g=[a b;c d], the image of Im(z)>=H,
H>0, is exactly the tangent Euclidean disk at a/c when c!=0.
Its center is (a/c,1/(2*c^2*H)) and radius is 1/(2*c^2*H).
The c=0 image is the exact horizontal half-space Im(z)>=a^2*H.
This does not import, repair or replace any held rational-cusp Lp frame.
-/
namespace ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise

/-- Denominator for height measured in the inverse actual cusp chart. -/
def inverseHeightDenominator (g : SL(2, ℝ)) (z : UpperHalfPlane) : ℝ :=
  (g 0 0 - g 1 0*z.re)^2 + (g 1 0*z.im)^2

theorem inverseHeightDenominator_eq_normSq (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    inverseHeightDenominator g z =
      Complex.normSq (UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g⁻¹) z) := by
  simp [inverseHeightDenominator, UpperHalfPlane.denom, SL2_inv_expl,
    mapGL_coe_matrix, Complex.normSq_apply] <;> ring

theorem inverseHeightDenominator_pos (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    0 < inverseHeightDenominator g z := by
  rw [inverseHeightDenominator_eq_normSq]
  exact UpperHalfPlane.normSq_denom_pos _ z.im_ne_zero

/-- Actual inverse Mobius height; no frame or unknown coordinate map. -/
theorem inverse_mobius_height (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    (g⁻¹ • z).im = z.im / inverseHeightDenominator g z := by
  change (SpecialLinearGroup.mapGL ℝ g⁻¹ • z).im = _
  rw [UpperHalfPlane.im_smul_eq_div_normSq]
  simp only [SpecialLinearGroup.det_mapGL, Units.val_one, abs_one, one_mul]
  rw [inverseHeightDenominator_eq_normSq]

def heightHalfSpace (H : ℝ) : Set UpperHalfPlane := {z | H ≤ z.im}
def strictHeightHalfSpace (H : ℝ) : Set UpperHalfPlane := {z | H < z.im}

def horoballRadius (g : SL(2, ℝ)) (H : ℝ) : ℝ := 1/(2*(g 1 0)^2*H)

def cuspDisk (g : SL(2, ℝ)) (H : ℝ) : Set UpperHalfPlane :=
  {z | (z.re-g 0 0/g 1 0)^2 + (z.im-horoballRadius g H)^2 ≤
    (horoballRadius g H)^2}

def strictCuspDisk (g : SL(2, ℝ)) (H : ℝ) : Set UpperHalfPlane :=
  {z | (z.re-g 0 0/g 1 0)^2 + (z.im-horoballRadius g H)^2 <
    (horoballRadius g H)^2}

theorem horoballRadius_pos (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hc : g 1 0 ≠ 0) : 0 < horoballRadius g H := by
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hc)) hH)

/-- Completing the square with the exact factor c^2*H. -/
theorem inverse_height_disk_factorization (g : SL(2, ℝ)) {H : ℝ}
    (hH : H ≠ 0) (hc : g 1 0 ≠ 0) (z : UpperHalfPlane) :
    ((g 1 0)^2*H) *
      ((z.re-g 0 0/g 1 0)^2 + (z.im-horoballRadius g H)^2 - (horoballRadius g H)^2) =
      H*inverseHeightDenominator g z - z.im := by
  unfold horoballRadius inverseHeightDenominator
  field_simp [hc, hH] <;> ring

/-- Exact geometric image of the closed high half-plane at a finite cusp. -/
theorem image_heightHalfSpace_eq_cuspDisk (g : SL(2, ℝ)) {H : ℝ}
    (hH : 0 < H) (hc : g 1 0 ≠ 0) :
    g • heightHalfSpace H = cuspDisk g H := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem]
  change H ≤ (g⁻¹ • z).im ↔ _
  rw [inverse_mobius_height, le_div_iff₀ (inverseHeightDenominator_pos g z)]
  have hfactor := inverse_height_disk_factorization g hH.ne' hc z
  have hp : 0 < (g 1 0)^2*H := mul_pos (sq_pos_of_ne_zero hc) hH
  change H*inverseHeightDenominator g z ≤ z.im ↔
    (z.re-g 0 0/g 1 0)^2 + (z.im-horoballRadius g H)^2 ≤ (horoballRadius g H)^2
  rw [← sub_nonpos, ← hfactor]
  simpa only [mul_zero, sub_nonpos] using (mul_le_mul_left hp)

theorem image_strictHeightHalfSpace_eq_strictCuspDisk (g : SL(2, ℝ)) {H : ℝ}
    (hH : 0 < H) (hc : g 1 0 ≠ 0) :
    g • strictHeightHalfSpace H = strictCuspDisk g H := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem]
  change H < (g⁻¹ • z).im ↔ _
  rw [inverse_mobius_height, lt_div_iff₀ (inverseHeightDenominator_pos g z)]
  have hfactor := inverse_height_disk_factorization g hH.ne' hc z
  have hp : 0 < (g 1 0)^2*H := mul_pos (sq_pos_of_ne_zero hc) hH
  change H*inverseHeightDenominator g z < z.im ↔
    (z.re-g 0 0/g 1 0)^2 + (z.im-horoballRadius g H)^2 < (horoballRadius g H)^2
  rw [← sub_neg, ← hfactor]
  simpa only [mul_zero, sub_neg] using (mul_lt_mul_left hp)

/-- At the actual infinity cusp, the image is a horizontal half-space,
with the exact factor a^2.  No nonzero-c formula is used at c=0. -/
theorem image_heightHalfSpace_of_c_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) (H : ℝ) :
    g • heightHalfSpace H = {z : UpperHalfPlane | H*(g 0 0)^2 ≤ z.im} := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem]
  change H ≤ (g⁻¹ • z).im ↔ _
  rw [inverse_mobius_height, le_div_iff₀ (inverseHeightDenominator_pos g z)]
  simp [inverseHeightDenominator, hc]

theorem image_strictHeightHalfSpace_of_c_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) (H : ℝ) :
    g • strictHeightHalfSpace H = {z : UpperHalfPlane | H*(g 0 0)^2 < z.im} := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem]
  change H < (g⁻¹ • z).im ↔ _
  rw [inverse_mobius_height, lt_div_iff₀ (inverseHeightDenominator_pos g z)]
  simp [inverseHeightDenominator, hc]

end
end ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
