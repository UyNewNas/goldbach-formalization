import ImbalancedChen.P4AOriginalThirdFallbackChartIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant

/-! Exact change of variables on the original open chart cells. The
matrix is the differential of the map to ordered prime coordinates
(x,y,z), so the unit y-to-(y+z) determinant is already included. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackJacobian
noncomputable section
open Set MeasureTheory
open P4AOriginalThirdFallbackArchive
open P4AOriginalThirdFallbackSlope
open P4AOriginalThirdFallbackChartIntegral

private abbrev coord (i : Fin 3) : Point →L[ℝ] ℝ := ContinuousLinearMap.proj i
def dx : Point →L[ℝ] ℝ := (h : ℝ) • coord 0
def ds (b : Bool) (t : Point) : Point →L[ℝ] ℝ :=
  ((branch b : ℝ)*(h : ℝ)*t 0) • coord 1 + t 1 • (((branch b : ℝ)*(h : ℝ)) • coord 0)
def dz (b : Bool) (t : Point) : Point →L[ℝ] ℝ :=
  (2:ℝ)⁻¹ • (S b (t 0) (t 1) • coord 2 + t 2 • ds b t)
def D (b : Bool) (t : Point) : Point →L[ℝ] Point :=
  ContinuousLinearMap.pi (![dx,ds b t-dz b t,dz b t] : Fin 3 → Point →L[ℝ] ℝ)

theorem derivative (b : Bool) (t : Point) : HasFDerivAt (chart b) (D b t) t := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) t
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) t
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) t
  have hx : HasFDerivAt (fun p : Point => X (p 0)) dx t :=
    (h0.const_mul (h : ℝ)).const_add (mu : ℝ)
  have hs : HasFDerivAt (fun p : Point => S b (p 0) (p 1)) (ds b t) t :=
    ((h0.const_mul ((branch b : ℝ)*(h : ℝ))).mul h1).const_add (mu : ℝ)
  have hz : HasFDerivAt (fun p : Point => Z b (p 0) (p 1) (p 2)) (dz b t) t := by
    simpa only [Z,dz,div_eq_mul_inv] using (hs.mul h2).mul_const (2:ℝ)⁻¹
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hx
  · exact hs.sub hz
  · exact hz

theorem determinant (b : Bool) (t : Point) :
    (D b t).det = (branch b : ℝ)*(h : ℝ)^2*t 0*S b (t 0) (t 1)/2 := by
  change LinearMap.det (D b t).toLinearMap = _
  rw [← LinearMap.det_toMatrix',Matrix.det_fin_three]
  simp [LinearMap.toMatrix'_apply,D,dx,ds,dz,coord,Pi.single_apply,smul_eq_mul] <;> ring

theorem strict_unit (c : Cell) {t : Point} (ht : t ∈ box c) :
    t 0 ∈ Ioo (0:ℝ) 1 ∧ t 1 ∈ Ioo (0:ℝ) 1 ∧ t 2 ∈ Ioo (5/9:ℝ) 1 := by
  have h0 := ht 0 (mem_univ _)
  have h1 := ht 1 (mem_univ _)
  have h2 := ht 2 (mem_univ _)
  have hindex : (c.2.1.val : ℝ) ≤ 7 := by exact_mod_cast (show c.2.1.val ≤ 7 by omega)
  have hj : (c.2.2.1.val : ℝ) ≤ 7 := by exact_mod_cast (show c.2.2.1.val ≤ 7 by omega)
  have hl : (c.2.2.2.val : ℝ) ≤ 31 := by exact_mod_cast (show c.2.2.2.val ≤ 31 by omega)
  simp [lo,hi,ua,ub,va,vb,wa,wb,Set.mem_Ioo] at h0 h1 h2
  exact ⟨⟨by linarith [h0.1,Nat.cast_nonneg (α := ℝ) c.2.1.val],by linarith [h0.2]⟩,
    ⟨by linarith [h1.1,Nat.cast_nonneg (α := ℝ) c.2.2.1.val],by linarith [h1.2]⟩,
    ⟨by linarith [h2.1,Nat.cast_nonneg (α := ℝ) c.2.2.2.val],by linarith [h2.2]⟩⟩

theorem abs_det (c : Cell) {t : Point} (ht : t ∈ box c) : |(D c.1 t).det| = jac c.1 (t 0) (t 1) := by
  obtain ⟨hu,hv,_⟩ := strict_unit c ht
  have hS := positive_s (b := c.1) ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩
  rw [determinant]
  simp [jac,abs_div,abs_mul,abs_of_nonneg hu.1.le,abs_of_nonneg hS.le,abs_of_nonneg (sq_nonneg (h : ℝ))]

def inverse (b : Bool) (p : Point) : Point :=
  ![(p 0-(mu : ℝ))/(h : ℝ),(p 1+p 2-(mu : ℝ))/((branch b : ℝ)*(p 0-(mu : ℝ))),2*p 2/(p 1+p 2)]

theorem inverse_chart (b : Bool) {t : Point} (hu : 0 < t 0) (hs : 0 < S b (t 0) (t 1)) :
    inverse b (chart b t) = t := by
  have hh : (h : ℝ) ≠ 0 := by norm_num [h]
  have hk : (branch b : ℝ) ≠ 0 := by cases b <;> norm_num [branch]
  have hxm : X (t 0)-(mu : ℝ) = (h : ℝ)*t 0 := by unfold X; ring
  have hsum : Y b (t 0) (t 1) (t 2)+Z b (t 0) (t 1) (t 2) = S b (t 0) (t 1) := by unfold Y; ring
  funext i
  fin_cases i
  · change (X (t 0)-(mu : ℝ))/(h : ℝ) = _
    rw [hxm]; field_simp
  · change (Y b (t 0) (t 1) (t 2)+Z b (t 0) (t 1) (t 2)-(mu : ℝ))/
      ((branch b : ℝ)*(X (t 0)-(mu : ℝ))) = _
    rw [hxm,hsum]
    unfold S
    field_simp [hh,hk,hu.ne'] <;> ring
  · change 2*Z b (t 0) (t 1) (t 2)/(Y b (t 0) (t 1) (t 2)+Z b (t 0) (t 1) (t 2)) = _
    rw [hsum]
    unfold Z
    field_simp [hs.ne'] <;> ring

theorem inverse_on_box (c : Cell) {t : Point} (ht : t ∈ box c) : inverse c.1 (chart c.1 t) = t := by
  obtain ⟨hu,hv,_⟩ := strict_unit c ht
  exact inverse_chart _ hu.1 (positive_s ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩)

theorem chart_injOn (c : Cell) : InjOn (chart c.1) (box c) := by
  intro t ht u hu he
  have hh := congrArg (inverse c.1) he
  simpa only [inverse_on_box c ht,inverse_on_box c hu] using hh

def region (c : Cell) : Set Point := chart c.1 '' box c

theorem row_eq_physical (c : Cell) :
    (∫ p in region c,kernel p) = ∫ t in box c,pullback c.1 t := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Point)
    (box_measurable c) (fun t _ => (derivative c.1 t).hasFDerivWithinAt) (chart_injOn c) kernel
  refine hh.trans (setIntegral_congr_fun (box_measurable c) ?_)
  intro t ht
  rw [abs_det c ht,smul_eq_mul]
  rfl

theorem slot_le_physical_images : currentUpperEighteenGains 5 ≤ ∑ c : Cell, ∫ p in region c,kernel p := by
  simp_rw [row_eq_physical]
  exact original_sixth_slot_le_chartSum

end
end ImbalancedChen.P4AOriginalThirdFallbackJacobian

