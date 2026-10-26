import ImbalancedChen.Part3MixedCuspHoroballGeometry

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Completes the converse mixed infinity/finite cusp image threshold.
Below Delta^2 H J=1, an actual point halfway between the horizontal
infinity boundary and the finite disk top belongs to both strict images.
Thus strict images are disjoint iff Delta^2 H J>=1, closed iff >1.
-/
namespace ImbalancedChen.Part3.MixedCuspOverlapThreshold20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b RationalCuspDiskSeparation20261026b
open MixedCuspHoroballGeometry20261026b

/-- Explicit interior overlap point for the actual mixed cusp images. -/
theorem mixed_below_threshold_overlap (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0)
    (hbelow : (cuspCross g h)^2*H*J < 1) :
    ∃ z : UpperHalfPlane, z.re = h 0 0/h 1 0 ∧
      z.im = (H*(g 0 0)^2+1/((h 1 0)^2*J))/2 ∧
      z ∈ (g • strictHeightHalfSpace H) ∩ (h • strictHeightHalfSpace J) := by
  have ha : g 0 0 ≠ 0 := by
    have hdet := g.det_coe
    rw [Matrix.det_fin_two, hc] at hdet
    intro hz
    simp [hz] at hdet
  let L := H*(g 0 0)^2
  let r := horoballRadius h J
  have hL : 0 < L := mul_pos hH (sq_pos_of_ne_zero ha)
  have hr : 0 < r := horoballRadius_pos h hJ hd
  have htop : L < 2*r := by
    rw [show 2*r = 1/((h 1 0)^2*J) from twice_horoballRadius h hJ hd]
    apply (lt_div_iff₀ (mul_pos (sq_pos_of_ne_zero hd) hJ)).mpr
    have hs : (g 0 0*h 1 0)^2*H*J < 1 := by simpa [cuspCross, hc] using hbelow
    dsimp [L]
    nlinarith [hs]
  let z : UpperHalfPlane := ⟨⟨h 0 0/h 1 0,(L+2*r)/2⟩, by positivity⟩
  have hzlow : L < z.im := by change L < (L+2*r)/2; linarith
  have hzpos : 0 < z.im := z.im_pos
  have hzhigh : z.im < 2*r := by change (L+2*r)/2 < 2*r; linarith
  have hzdisk : z ∈ strictCuspDisk h J := by
    change (h 0 0/h 1 0-h 0 0/h 1 0)^2+(z.im-r)^2 < r^2
    have hp := mul_pos hzpos (sub_pos.mpr hzhigh)
    nlinarith [hp]
  refine ⟨z,rfl,?_,?_⟩
  · change (L+2*r)/2 = (H*(g 0 0)^2+1/((h 1 0)^2*J))/2
    rw [show 2*r = 1/((h 1 0)^2*J) from twice_horoballRadius h hJ hd]
  · rw [image_strictHeightHalfSpace_of_c_eq_zero g hc H,
      image_strictHeightHalfSpace_eq_strictCuspDisk h hJ hd]
    exact ⟨hzlow,hzdisk⟩

theorem mixed_strict_images_disjoint_iff (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0) :
    Disjoint (g • strictHeightHalfSpace H) (h • strictHeightHalfSpace J) ↔
      1 ≤ (cuspCross g h)^2*H*J := by
  constructor
  · intro hdisj
    by_contra hnot
    obtain ⟨z,hx,hy,hz⟩ := mixed_below_threshold_overlap g h hH hJ hc hd (lt_of_not_ge hnot)
    exact Set.disjoint_left.mp hdisj hz.1 hz.2
  · exact mixed_strict_images_disjoint g h hH hJ hc hd

private theorem strict_image_subset_closed (g : SL(2, ℝ)) (H : ℝ) :
    g • strictHeightHalfSpace H ⊆ g • heightHalfSpace H := by
  rintro z ⟨v,hv,rfl⟩
  exact ⟨v,show H ≤ v.im from hv.le,rfl⟩

theorem mixed_closed_images_disjoint_iff (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 = 0) (hd : h 1 0 ≠ 0) :
    Disjoint (g • heightHalfSpace H) (h • heightHalfSpace J) ↔
      1 < (cuspCross g h)^2*H*J := by
  constructor
  · intro hdisj
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hbelow | heq
    · obtain ⟨z,hx,hy,hz⟩ := mixed_below_threshold_overlap g h hH hJ hc hd hbelow
      exact Set.disjoint_left.mp hdisj
        (strict_image_subset_closed g H hz.1) (strict_image_subset_closed h J hz.2)
    · obtain ⟨z,hx,hy,hz⟩ := mixed_closed_images_tangency g h hH hJ hc hd heq
      have hmem : z ∈ (g • heightHalfSpace H) ∩ (h • heightHalfSpace J) := by rw [hz]; simp
      exact Set.disjoint_left.mp hdisj hmem.1 hmem.2
  · exact mixed_closed_images_disjoint g h hH hJ hc hd

end
end ImbalancedChen.Part3.MixedCuspOverlapThreshold20261026b
