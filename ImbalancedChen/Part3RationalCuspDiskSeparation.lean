import ImbalancedChen.Part3RationalCuspHoroballDisks
import Mathlib.Analysis.Complex.Norm

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Independent real cusp-disk separation at the exact determinant threshold.
For finite cusp columns (a,c),(b,d), Delta=a*d-b*c.  The squared center
distance minus the squared sum of radii is
  (Delta^2*H*J-1)/((c*d)^2*H*J).
Thus strict cusp horoballs are disjoint when Delta^2*H*J>=1; closed ones
are disjoint at strict inequality.  This is actual matrix-image geometry;
no assertion that given cusps are Gamma0-inequivalent is manufactured.
-/
namespace ImbalancedChen.Part3.RationalCuspDiskSeparation20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b

def cuspCross (g h : SL(2, ℝ)) : ℝ := g 0 0*h 1 0-h 0 0*g 1 0

def diskCenter (g : SL(2, ℝ)) (H : ℝ) : ℂ :=
  ⟨g 0 0/g 1 0, horoballRadius g H⟩

/-- Exact difference of the two real boundary tangency coordinates. -/
theorem boundary_center_difference (g h : SL(2, ℝ))
    (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0) :
    g 0 0/g 1 0-h 0 0/h 1 0 = cuspCross g h/(g 1 0*h 1 0) := by
  unfold cuspCross
  field_simp [hc, hd] <;> ring

/-- The threshold includes the different vertical coordinates of the
centers; simply comparing horizontal center distance to r+s is wrong. -/
theorem center_distance_threshold_identity (g h : SL(2, ℝ))
    {H J : ℝ} (hH : H ≠ 0) (hJ : J ≠ 0)
    (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0) :
    Complex.normSq (diskCenter g H-diskCenter h J) -
        (horoballRadius g H+horoballRadius h J)^2 =
      ((cuspCross g h)^2*H*J-1)/((g 1 0*h 1 0)^2*H*J) := by
  simp only [diskCenter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mk_re, Complex.mk_im]
  unfold horoballRadius cuspCross
  field_simp [hc, hd, hH, hJ] <;> ring

private theorem disk_norm_le (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hc : g 1 0 ≠ 0) {z : UpperHalfPlane} (hz : z ∈ cuspDisk g H) :
    ‖(z : ℂ)-diskCenter g H‖ ≤ horoballRadius g H := by
  have hr := horoballRadius_pos g hH hc
  have hs : ‖(z : ℂ)-diskCenter g H‖^2 ≤ (horoballRadius g H)^2 := by
    simpa only [Complex.sq_norm, diskCenter, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mk_re, Complex.mk_im] using hz
  nlinarith [norm_nonneg ((z : ℂ)-diskCenter g H)]

private theorem strict_disk_norm_lt (g : SL(2, ℝ)) {H : ℝ} (hH : 0 < H)
    (hc : g 1 0 ≠ 0) {z : UpperHalfPlane} (hz : z ∈ strictCuspDisk g H) :
    ‖(z : ℂ)-diskCenter g H‖ < horoballRadius g H := by
  have hr := horoballRadius_pos g hH hc
  have hs : ‖(z : ℂ)-diskCenter g H‖^2 < (horoballRadius g H)^2 := by
    simpa only [Complex.sq_norm, diskCenter, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.mk_re, Complex.mk_im] using hz
  nlinarith [norm_nonneg ((z : ℂ)-diskCenter g H)]

private theorem center_triangle (g h : SL(2, ℝ)) (H J : ℝ) (z : UpperHalfPlane) :
    ‖diskCenter g H-diskCenter h J‖ ≤
      ‖(z : ℂ)-diskCenter g H‖ + ‖(z : ℂ)-diskCenter h J‖ := by
  calc
    _ = ‖(diskCenter g H-(z : ℂ))+((z : ℂ)-diskCenter h J)‖ := by congr 1; ring
    _ ≤ ‖diskCenter g H-(z : ℂ)‖+‖(z : ℂ)-diskCenter h J‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (diskCenter g H) (z : ℂ)]

/-- Strict interiors are disjoint even at the tangency threshold. -/
theorem strictCuspDisk_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 ≤ (cuspCross g h)^2*H*J) :
    Disjoint (strictCuspDisk g H) (strictCuspDisk h J) := by
  apply Set.disjoint_left.mpr
  intro z hzg hzh
  have hg := strict_disk_norm_lt g hH hc hzg
  have hh := strict_disk_norm_lt h hJ hd hzh
  have htri := center_triangle g h H J z
  have hr : 0 < horoballRadius g H+horoballRadius h J :=
    add_pos (horoballRadius_pos g hH hc) (horoballRadius_pos h hJ hd)
  have hden : 0 < (g 1 0*h 1 0)^2*H*J :=
    mul_pos (mul_pos (sq_pos_of_ne_zero (mul_ne_zero hc hd)) hH) hJ
  have hid := center_distance_threshold_identity g h hH.ne' hJ.ne' hc hd
  have hnonneg : 0 ≤ ((cuspCross g h)^2*H*J-1)/((g 1 0*h 1 0)^2*H*J) :=
    div_nonneg (sub_nonneg.mpr hsep) hden.le
  rw [Complex.normSq_eq_norm_sq] at hid
  nlinarith [norm_nonneg (diskCenter g H-diskCenter h J)]

/-- Closed horoballs are disjoint strictly beyond the determinant threshold. -/
theorem cuspDisk_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 < (cuspCross g h)^2*H*J) :
    Disjoint (cuspDisk g H) (cuspDisk h J) := by
  apply Set.disjoint_left.mpr
  intro z hzg hzh
  have hg := disk_norm_le g hH hc hzg
  have hh := disk_norm_le h hJ hd hzh
  have htri := center_triangle g h H J z
  have hr : 0 < horoballRadius g H+horoballRadius h J :=
    add_pos (horoballRadius_pos g hH hc) (horoballRadius_pos h hJ hd)
  have hden : 0 < (g 1 0*h 1 0)^2*H*J :=
    mul_pos (mul_pos (sq_pos_of_ne_zero (mul_ne_zero hc hd)) hH) hJ
  have hid := center_distance_threshold_identity g h hH.ne' hJ.ne' hc hd
  have hpos : 0 < ((cuspCross g h)^2*H*J-1)/((g 1 0*h 1 0)^2*H*J) :=
    div_pos (sub_pos.mpr hsep) hden
  rw [Complex.normSq_eq_norm_sq] at hid
  nlinarith [norm_nonneg (diskCenter g H-diskCenter h J)]

/-- The actual matrix images inherit the sharp disk separation. -/
theorem strict_horoball_images_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 ≤ (cuspCross g h)^2*H*J) :
    Disjoint (g • strictHeightHalfSpace H) (h • strictHeightHalfSpace J) := by
  rw [image_strictHeightHalfSpace_eq_strictCuspDisk g hH hc,
    image_strictHeightHalfSpace_eq_strictCuspDisk h hJ hd]
  exact strictCuspDisk_disjoint g h hH hJ hc hd hsep

theorem closed_horoball_images_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 < (cuspCross g h)^2*H*J) :
    Disjoint (g • heightHalfSpace H) (h • heightHalfSpace J) := by
  rw [image_heightHalfSpace_eq_cuspDisk g hH hc, image_heightHalfSpace_eq_cuspDisk h hJ hd]
  exact cuspDisk_disjoint g h hH hJ hc hd hsep

/-- Exact integer determinant arithmetic for applications to rational
cusps.  Distinct integral cusp columns have cross-square at least one. -/
theorem integer_cross_square_one_le (a b c d : ℤ) (hn : a*d-b*c ≠ 0) :
    (1 : ℝ) ≤ (((a*d-b*c : ℤ) : ℝ))^2 := by
  have hp : (0 : ℤ) < (a*d-b*c)^2 := sq_pos_of_ne_zero hn
  have h1 : (1 : ℤ) ≤ (a*d-b*c)^2 := by omega
  exact_mod_cast h1

end
end ImbalancedChen.Part3.RationalCuspDiskSeparation20261026b
