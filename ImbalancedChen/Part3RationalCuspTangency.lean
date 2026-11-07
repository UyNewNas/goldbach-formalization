import ImbalancedChen.Part3RationalCuspDiskSeparation

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
At the sharp determinant threshold Delta^2*H*J=1, the two CLOSED
finite-cusp horoballs meet in exactly one point.  If their boundary
coordinates are p,q and radii r,s, its actual coordinates are
  x=(s*p+r*q)/(r+s), y=2*r*s/(r+s)>0.
The proof uses the exact weighted sum of the two disk inequalities,
not a postulated circle tangency or a Gamma0 cusp classification.
-/
namespace ImbalancedChen.Part3.RationalCuspTangency20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b RationalCuspDiskSeparation20261026b

/-- The weighted disk defects determine the contact point exactly. -/
theorem weighted_disk_identity (x y p q r s : ℝ) :
    (r+s)*(s*((x-p)^2+(y-r)^2-r^2)+r*((x-q)^2+(y-s)^2-s^2)) =
      ((r+s)*x-(s*p+r*q))^2 + ((r+s)*y-2*r*s)^2 +
        r*s*((p-q)^2-4*r*s) := by ring

private theorem contact_first_boundary (p q r s : ℝ) (hsum : r+s ≠ 0)
    (hgap : (p-q)^2-4*r*s = 0) :
    ((s*p+r*q)/(r+s)-p)^2 + (2*r*s/(r+s)-r)^2 = r^2 := by
  have hid : ((s*p+r*q)/(r+s)-p)^2 + (2*r*s/(r+s)-r)^2-r^2 =
      (r^2/(r+s)^2)*((p-q)^2-4*r*s) := by
    field_simp [hsum] <;> ring
  rw [hgap, mul_zero] at hid
  linarith

private theorem contact_second_boundary (p q r s : ℝ) (hsum : r+s ≠ 0)
    (hgap : (p-q)^2-4*r*s = 0) :
    ((s*p+r*q)/(r+s)-q)^2 + (2*r*s/(r+s)-s)^2 = s^2 := by
  have hid : ((s*p+r*q)/(r+s)-q)^2 + (2*r*s/(r+s)-s)^2-s^2 =
      (s^2/(r+s)^2)*((p-q)^2-4*r*s) := by
    field_simp [hsum] <;> ring
  rw [hgap, mul_zero] at hid
  linarith

/-- Exact singleton intersection at determinant equality, with the
literal point in the actual upper half-plane and both coordinates. -/
theorem cuspDisk_intersection_singleton (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hthreshold : (cuspCross g h)^2*H*J = 1) :
    ∃ z : UpperHalfPlane,
      z.re = (horoballRadius h J*(g 0 0/g 1 0)+horoballRadius g H*(h 0 0/h 1 0)) /
        (horoballRadius g H+horoballRadius h J) ∧
      z.im = 2*horoballRadius g H*horoballRadius h J /
        (horoballRadius g H+horoballRadius h J) ∧
      cuspDisk g H ∩ cuspDisk h J = {z} := by
  let p := g 0 0/g 1 0
  let q := h 0 0/h 1 0
  let r := horoballRadius g H
  let s := horoballRadius h J
  have hr : 0 < r := horoballRadius_pos g hH hc
  have hs : 0 < s := horoballRadius_pos h hJ hd
  have hsum : r+s ≠ 0 := (add_pos hr hs).ne'
  have hgap : (p-q)^2-4*r*s = 0 := by
    have hid := center_distance_threshold_identity g h hH.ne' hJ.ne' hc hd
    rw [hthreshold, sub_self, zero_div] at hid
    simp only [diskCenter, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mk_re, Complex.mk_im] at hid
    change (p-q)^2+(r-s)^2-(r+s)^2 = 0 at hid
    nlinarith [hid]
  let z : UpperHalfPlane := ⟨⟨(s*p+r*q)/(r+s), 2*r*s/(r+s)⟩,
    div_pos (mul_pos (mul_pos (by norm_num) hr) hs) (add_pos hr hs)⟩
  have hz : z ∈ cuspDisk g H ∩ cuspDisk h J := by
    change (((s*p+r*q)/(r+s)-p)^2+(2*r*s/(r+s)-r)^2 ≤ r^2) ∧
      (((s*p+r*q)/(r+s)-q)^2+(2*r*s/(r+s)-s)^2 ≤ s^2)
    exact ⟨(contact_first_boundary p q r s hsum hgap).le,
      (contact_second_boundary p q r s hsum hgap).le⟩
  have hunique {u : UpperHalfPlane} (hu : u ∈ cuspDisk g H ∩ cuspDisk h J) : u = z := by
    have hg : (u.re-p)^2+(u.im-r)^2-r^2 ≤ 0 := sub_nonpos.mpr hu.1
    have hh : (u.re-q)^2+(u.im-s)^2-s^2 ≤ 0 := sub_nonpos.mpr hu.2
    have hw := mul_nonpos_of_nonneg_of_nonpos (add_pos hr hs).le
      (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hs.le hg)
        (mul_nonpos_of_nonneg_of_nonpos hr.le hh))
    rw [weighted_disk_identity, hgap, mul_zero, add_zero] at hw
    have hx : (r+s)*u.re-(s*p+r*q) = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [sq_nonneg ((r+s)*u.im-2*r*s)]
    have hy : (r+s)*u.im-2*r*s = 0 := by
      apply sq_eq_zero_iff.mp
      nlinarith [sq_nonneg ((r+s)*u.re-(s*p+r*q))]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change u.re = (s*p+r*q)/(r+s)
      apply (eq_div_iff hsum).mpr
      nlinarith [hx]
    · change u.im = 2*r*s/(r+s)
      apply (eq_div_iff hsum).mpr
      nlinarith [hy]
  refine ⟨z, rfl, rfl, ?_⟩
  ext u
  constructor
  · intro hu
    exact Set.mem_singleton_iff.mpr (hunique hu)
  · intro hu
    have heu : u = z := Set.mem_singleton_iff.mp hu
    simpa only [heu] using hz

/-- The same singleton is an intersection of ACTUAL matrix images of
closed high half-planes, not merely an abstract pair of planar disks. -/
theorem horoball_images_intersection_singleton (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hthreshold : (cuspCross g h)^2*H*J = 1) :
    ∃ z : UpperHalfPlane, (g • heightHalfSpace H) ∩ (h • heightHalfSpace J) = {z} := by
  obtain ⟨z, hx, hy, hz⟩ := cuspDisk_intersection_singleton g h hH hJ hc hd hthreshold
  refine ⟨z, ?_⟩
  rw [image_heightHalfSpace_eq_cuspDisk g hH hc, image_heightHalfSpace_eq_cuspDisk h hJ hd]
  exact hz

end
end ImbalancedChen.Part3.RationalCuspTangency20261026b
