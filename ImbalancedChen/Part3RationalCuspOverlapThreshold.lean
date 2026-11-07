import ImbalancedChen.Part3RationalCuspTangency

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The converse side of sharp finite-cusp separation.  Below Delta^2*H*J=1
an explicit positive-height weighted-center point lies in BOTH actual
strict horoball images.  This completes the exact disjointness iff:
open images are disjoint iff Delta^2*H*J>=1; closed images iff >1.
The equality contact supplier is reused, with no cusp-class assertion.
-/
namespace ImbalancedChen.Part3.RationalCuspOverlapThreshold20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b RationalCuspDiskSeparation20261026b
open RationalCuspTangency20261026b

private theorem weighted_difference_left (a b : ℂ) (r s : ℝ) (hn : r+s ≠ 0) :
    ((s : ℂ)*a+(r : ℂ)*b)/((r+s : ℝ) : ℂ)-a =
      ((r/(r+s) : ℝ) : ℂ)*(b-a) := by
  have hc : (r : ℂ)+(s : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hc] <;> ring

private theorem weighted_difference_right (a b : ℂ) (r s : ℝ) (hn : r+s ≠ 0) :
    ((s : ℂ)*a+(r : ℂ)*b)/((r+s : ℝ) : ℂ)-b =
      ((s/(r+s) : ℝ) : ℂ)*(a-b) := by
  have hc : (r : ℂ)+(s : ℂ) ≠ 0 := by exact_mod_cast hn
  push_cast
  field_simp [hc] <;> ring

/-- The witness has exact positive coordinates, rather than an abstract
nonempty-intersection hypothesis. -/
theorem below_threshold_actual_overlap (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0)
    (hbelow : (cuspCross g h)^2*H*J < 1) :
    ∃ z : UpperHalfPlane,
      z.re = (horoballRadius h J*(g 0 0/g 1 0)+horoballRadius g H*(h 0 0/h 1 0)) /
        (horoballRadius g H+horoballRadius h J) ∧
      z.im = 2*horoballRadius g H*horoballRadius h J /
        (horoballRadius g H+horoballRadius h J) ∧
      z ∈ (g • strictHeightHalfSpace H) ∩ (h • strictHeightHalfSpace J) := by
  let p := g 0 0/g 1 0
  let q := h 0 0/h 1 0
  let r := horoballRadius g H
  let s := horoballRadius h J
  have hr : 0 < r := horoballRadius_pos g hH hc
  have hs : 0 < s := horoballRadius_pos h hJ hd
  have hsum : 0 < r+s := add_pos hr hs
  have hden : 0 < (g 1 0*h 1 0)^2*H*J :=
    mul_pos (mul_pos (sq_pos_of_ne_zero (mul_ne_zero hc hd)) hH) hJ
  have hid := center_distance_threshold_identity g h hH.ne' hJ.ne' hc hd
  have hnegative : ((cuspCross g h)^2*H*J-1)/((g 1 0*h 1 0)^2*H*J) < 0 :=
    div_neg_of_neg_of_pos (sub_neg.mpr hbelow) hden
  rw [Complex.normSq_eq_norm_sq] at hid
  have hcentersq : ‖diskCenter g H-diskCenter h J‖^2 < (r+s)^2 := by
    change ‖diskCenter g H-diskCenter h J‖^2-(r+s)^2 = _ at hid
    linarith
  have hcenter : ‖diskCenter g H-diskCenter h J‖ < r+s :=
    (sq_lt_sq₀ (norm_nonneg _) hsum.le).mp hcentersq
  let z : UpperHalfPlane := ⟨⟨(s*p+r*q)/(r+s),2*r*s/(r+s)⟩,
    div_pos (mul_pos (mul_pos (by norm_num) hr) hs) hsum⟩
  have hzcomplex : (z : ℂ) =
      ((s : ℂ)*diskCenter g H+(r : ℂ)*diskCenter h J)/((r+s : ℝ) : ℂ) := by
    change (⟨(s*p+r*q)/(r+s),2*r*s/(r+s)⟩ : ℂ) =
      ((s : ℂ)*(⟨p,r⟩ : ℂ)+(r : ℂ)*(⟨q,s⟩ : ℂ))/((r+s : ℝ) : ℂ)
    apply Complex.ext <;>
      simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
      field_simp [hsum.ne'] <;> ring
  have hgnorm : ‖(z : ℂ)-diskCenter g H‖ < r := by
    rw [hzcomplex, weighted_difference_left _ _ r s hsum.ne', norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr hsum)]
    rw [norm_sub_rev (diskCenter h J) (diskCenter g H)]
    calc
      _ < (r/(r+s))*(r+s) := mul_lt_mul_of_pos_left hcenter (div_pos hr hsum)
      _ = r := div_mul_cancel₀ r hsum.ne'
  have hhnorm : ‖(z : ℂ)-diskCenter h J‖ < s := by
    rw [hzcomplex, weighted_difference_right _ _ r s hsum.ne', norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hs hsum)]
    calc
      _ < (s/(r+s))*(r+s) := mul_lt_mul_of_pos_left hcenter (div_pos hs hsum)
      _ = s := div_mul_cancel₀ s hsum.ne'
  have hzg : z ∈ strictCuspDisk g H := by
    have hsq := (sq_lt_sq₀ (norm_nonneg ((z : ℂ)-diskCenter g H)) hr.le).mpr hgnorm
    simpa only [Complex.sq_norm, diskCenter, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mk_re, Complex.mk_im] using hsq
  have hzh : z ∈ strictCuspDisk h J := by
    have hsq := (sq_lt_sq₀ (norm_nonneg ((z : ℂ)-diskCenter h J)) hs.le).mpr hhnorm
    simpa only [Complex.sq_norm, diskCenter, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mk_re, Complex.mk_im] using hsq
  refine ⟨z, rfl, rfl, ?_⟩
  rw [image_strictHeightHalfSpace_eq_strictCuspDisk g hH hc,
    image_strictHeightHalfSpace_eq_strictCuspDisk h hJ hd]
  exact ⟨hzg,hzh⟩

theorem strict_images_disjoint_iff_threshold (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0) :
    Disjoint (g • strictHeightHalfSpace H) (h • strictHeightHalfSpace J) ↔
      1 ≤ (cuspCross g h)^2*H*J := by
  constructor
  · intro hdisj
    by_contra hnot
    obtain ⟨z,hx,hy,hz⟩ := below_threshold_actual_overlap g h hH hJ hc hd (lt_of_not_ge hnot)
    exact Set.disjoint_left.mp hdisj hz.1 hz.2
  · exact strict_horoball_images_disjoint g h hH hJ hc hd

private theorem strict_image_subset_closed (g : SL(2, ℝ)) (H : ℝ) :
    g • strictHeightHalfSpace H ⊆ g • heightHalfSpace H := by
  rintro z ⟨v,hv,rfl⟩
  exact ⟨v, show H ≤ v.im from hv.le, rfl⟩

theorem closed_images_disjoint_iff_threshold (g h : SL(2, ℝ)) {H J : ℝ}
    (hH : 0 < H) (hJ : 0 < J) (hc : g 1 0 ≠ 0) (hd : h 1 0 ≠ 0) :
    Disjoint (g • heightHalfSpace H) (h • heightHalfSpace J) ↔
      1 < (cuspCross g h)^2*H*J := by
  constructor
  · intro hdisj
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hbelow | heq
    · obtain ⟨z,hx,hy,hz⟩ := below_threshold_actual_overlap g h hH hJ hc hd hbelow
      exact Set.disjoint_left.mp hdisj
        (strict_image_subset_closed g H hz.1) (strict_image_subset_closed h J hz.2)
    · obtain ⟨z,hz⟩ := horoball_images_intersection_singleton g h hH hJ hc hd heq
      have hmem : z ∈ (g • heightHalfSpace H) ∩ (h • heightHalfSpace J) := by
        rw [hz]
        simp
      exact Set.disjoint_left.mp hdisj hmem.1 hmem.2
  · exact closed_horoball_images_disjoint g h hH hJ hc hd

end
end ImbalancedChen.Part3.RationalCuspOverlapThreshold20261026b
