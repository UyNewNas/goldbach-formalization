import ImbalancedChen.Part3RationalCuspDiskSeparation

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The missing mixed infinity/finite branch of sharp cusp horoball geometry.
If g.c=0 and h.c!=0, Delta=g.a*h.c.  Strict images are disjoint for
Delta^2*H*J>=1; closed images are disjoint for >1, and at equality their
intersection is exactly the top of the finite cusp disk.  This is actual
SL2 matrix-image geometry, without a Gamma0 cusp inequivalence claim.
-/
namespace ImbalancedChen.Part3.MixedCuspHoroballGeometry20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b RationalCuspDiskSeparation20261026b

theorem twice_horoballRadius (h : SL(2, ℝ)) {J : ℝ}
    (hJ : 0 < J) (hd : h 1 0 ≠ 0) :
    2*horoballRadius h J = 1/((h 1 0)^2*J) := by
  unfold horoballRadius
  field_simp [hd, hJ.ne'] <;> ring

/-- Every actual finite-cusp disk lies below its exact top height. -/
theorem cuspDisk_height_le (h : SL(2, ℝ)) {J : ℝ} {z : UpperHalfPlane}
    (hz : z ∈ cuspDisk h J) : z.im ≤ 2*horoballRadius h J := by
  have hs : z.im^2 ≤ (2*horoballRadius h J)*z.im := by
    change (z.re-h 0 0/h 1 0)^2+(z.im-horoballRadius h J)^2 ≤
      (horoballRadius h J)^2 at hz
    nlinarith [sq_nonneg (z.re-h 0 0/h 1 0)]
  exact (mul_le_mul_right z.im_pos).mp (by simpa only [pow_two] using hs)

theorem strictCuspDisk_height_lt (h : SL(2, ℝ)) {J : ℝ} {z : UpperHalfPlane}
    (hz : z ∈ strictCuspDisk h J) : z.im < 2*horoballRadius h J := by
  have hs : z.im^2 < (2*horoballRadius h J)*z.im := by
    change (z.re-h 0 0/h 1 0)^2+(z.im-horoballRadius h J)^2 <
      (horoballRadius h J)^2 at hz
    nlinarith [sq_nonneg (z.re-h 0 0/h 1 0)]
  exact (mul_lt_mul_right z.im_pos).mp (by simpa only [pow_two] using hs)

private theorem mixed_threshold_le (g h : SL(2, ℝ)) {H J : ℝ}
    (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 ≤ (cuspCross g h)^2*H*J) :
    2*horoballRadius h J ≤ H*(g 0 0)^2 := by
  rw [twice_horoballRadius h hJ hd]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_ne_zero hd) hJ)).mpr
  have hs : 1 ≤ (g 0 0*h 1 0)^2*H*J := by simpa [cuspCross, hc] using hsep
  nlinarith [hs]

private theorem mixed_threshold_lt (g h : SL(2, ℝ)) {H J : ℝ}
    (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 < (cuspCross g h)^2*H*J) :
    2*horoballRadius h J < H*(g 0 0)^2 := by
  rw [twice_horoballRadius h hJ hd]
  apply (div_lt_iff₀ (mul_pos (sq_pos_of_ne_zero hd) hJ)).mpr
  have hs : 1 < (g 0 0*h 1 0)^2*H*J := by simpa [cuspCross, hc] using hsep
  nlinarith [hs]

/-- Sharp mixed open-image exclusion, including equality. -/
theorem mixed_strict_images_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 ≤ (cuspCross g h)^2*H*J) :
    Disjoint (g • strictHeightHalfSpace H) (h • strictHeightHalfSpace J) := by
  rw [image_strictHeightHalfSpace_of_c_eq_zero g hc H,
    image_strictHeightHalfSpace_eq_strictCuspDisk h hJ hd]
  apply Set.disjoint_left.mpr
  intro z hzg hzh
  have htop := strictCuspDisk_height_lt h hzh
  have hthreshold := mixed_threshold_le g h hJ hc hd hsep
  change H*(g 0 0)^2 < z.im at hzg
  linarith

theorem mixed_closed_images_disjoint (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hsep : 1 < (cuspCross g h)^2*H*J) :
    Disjoint (g • heightHalfSpace H) (h • heightHalfSpace J) := by
  rw [image_heightHalfSpace_of_c_eq_zero g hc H, image_heightHalfSpace_eq_cuspDisk h hJ hd]
  apply Set.disjoint_left.mpr
  intro z hzg hzh
  have htop := cuspDisk_height_le h hzh
  have hthreshold := mixed_threshold_lt g h hJ hc hd hsep
  change H*(g 0 0)^2 ≤ z.im at hzg
  linarith

/-- At equality the contact point is the exact top of the finite disk. -/
theorem mixed_closed_images_tangency (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hthreshold : (cuspCross g h)^2*H*J = 1) :
    ∃ z : UpperHalfPlane, z.re = h 0 0/h 1 0 ∧
      z.im = 1/((h 1 0)^2*J) ∧
      (g • heightHalfSpace H) ∩ (h • heightHalfSpace J) = {z} := by
  have hr := horoballRadius_pos h hJ hd
  have heq : 2*horoballRadius h J = H*(g 0 0)^2 := by
    rw [twice_horoballRadius h hJ hd]
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 hd) hJ.ne')).mpr
    have hs : (g 0 0*h 1 0)^2*H*J = 1 := by
      simpa [cuspCross, hc] using hthreshold
    nlinarith [hs]
  let z : UpperHalfPlane := ⟨⟨h 0 0/h 1 0, 2*horoballRadius h J⟩,
    mul_pos (by norm_num) hr⟩
  have hz : z ∈ {u : UpperHalfPlane | H*(g 0 0)^2 ≤ u.im} ∩ cuspDisk h J := by
    constructor
    · change H*(g 0 0)^2 ≤ 2*horoballRadius h J
      exact heq.ge
    · change (h 0 0/h 1 0-h 0 0/h 1 0)^2+
        (2*horoballRadius h J-horoballRadius h J)^2 ≤ (horoballRadius h J)^2
      nlinarith
  have hunique {u : UpperHalfPlane}
      (hu : u ∈ {v : UpperHalfPlane | H*(g 0 0)^2 ≤ v.im} ∩ cuspDisk h J) : u = z := by
    have htop := cuspDisk_height_le h hu.2
    have hy : u.im = 2*horoballRadius h J := by
      have hbottom : H*(g 0 0)^2 ≤ u.im := hu.1
      linarith [hbottom]
    have hx : u.re-h 0 0/h 1 0 = 0 := by
      apply sq_eq_zero_iff.mp
      have huDisk := hu.2
      change (u.re-h 0 0/h 1 0)^2+(u.im-horoballRadius h J)^2 ≤
        (horoballRadius h J)^2 at huDisk
      rw [hy] at huDisk
      nlinarith [sq_nonneg (u.re-h 0 0/h 1 0)]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change u.re = h 0 0/h 1 0
      linarith [hx]
    · exact hy
  refine ⟨z, rfl, twice_horoballRadius h hJ hd, ?_⟩
  rw [image_heightHalfSpace_of_c_eq_zero g hc H, image_heightHalfSpace_eq_cuspDisk h hJ hd]
  ext u
  constructor
  · intro hu
    exact Set.mem_singleton_iff.mpr (hunique hu)
  · intro hu
    have heu : u = z := Set.mem_singleton_iff.mp hu
    simpa only [heu] using hz

end
end ImbalancedChen.Part3.MixedCuspHoroballGeometry20261026b
