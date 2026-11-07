import ImbalancedChen.Part3MixedCuspHoroballGeometry
import ImbalancedChen.Part3RationalCuspTangency
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual integral-column arithmetic closes the real disk separation bridge.
Distinct projective rational cusps have nonzero integral column cross
product; its square is at least one.  Consequently their actual integral
SL2 high images are disjoint for every two strict heights H,J>=1, including
infinity.  Cross determinant +/-1 gives exact Ford contact at height one.
No Gamma0 cusp-class inequivalence or quotient embedding is inferred.
-/
namespace ImbalancedChen.Part3.IntegralCuspFordGeometry20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane Pointwise
open RationalCuspHoroballDisks20261026b RationalCuspDiskSeparation20261026b
open RationalCuspTangency20261026b MixedCuspHoroballGeometry20261026b
open Gamma0GeneralCuspUnitPeriod20261025a

def integralCuspCross (g h : SL(2, ℤ)) : ℤ := g 0 0*h 1 0-h 0 0*g 1 0

theorem relative_c_eq_cross (g h : SL(2, ℤ)) :
    (g⁻¹*h) 1 0 = integralCuspCross g h := by
  simp [integralCuspCross, SL2_inv_expl, coe_mul, Matrix.mul_fin_two] <;> ring

/-- This is equality of actual projective cusp POINTS, not Gamma0 cusp
classes.  The integer cross determinant is the exact criterion. -/
theorem projective_cusp_eq_iff_cross_zero (g h : SL(2, ℤ)) :
    SpecialLinearGroup.mapGL ℝ g • (∞ : OnePoint ℝ) =
      SpecialLinearGroup.mapGL ℝ h • (∞ : OnePoint ℝ) ↔ integralCuspCross g h = 0 := by
  have hfix : SpecialLinearGroup.mapGL ℝ (g⁻¹*h) • (∞ : OnePoint ℝ) = ∞ ↔
      (g⁻¹*h) 1 0 = 0 := by
    simp [smul_infty_eq_self_iff, mapGL_coe_matrix]
  rw [← relative_c_eq_cross, ← hfix]
  simp only [map_mul, map_inv, mul_smul]
  constructor
  · intro heq
    rw [← heq, inv_smul_smul]
  · intro heq
    have hh := congrArg (fun x : OnePoint ℝ => SpecialLinearGroup.mapGL ℝ g • x) heq
    simpa only [smul_inv_smul] using hh.symm

theorem real_cross_eq_integer (g h : SL(2, ℤ)) :
    cuspCross (integralReal g) (integralReal h) = (integralCuspCross g h : ℝ) := by
  simp [cuspCross, integralCuspCross, integralReal, Matrix.SpecialLinearGroup.map_apply_coe]

private theorem real_image_eq_integral (g : SL(2, ℤ)) (S : Set UpperHalfPlane) :
    integralReal g • S = g • S := by
  ext z
  simp only [Set.mem_smul_set, integralReal_smul]

private theorem cross_swap (g h : SL(2, ℝ)) : cuspCross h g = -cuspCross g h := by
  unfold cuspCross
  ring

private theorem uniform_threshold (g h : SL(2, ℤ)) {H J : ℝ}
    (hH : 1 ≤ H) (hJ : 1 ≤ J) (hn : integralCuspCross g h ≠ 0) :
    1 ≤ (cuspCross (integralReal g) (integralReal h))^2*H*J := by
  rw [real_cross_eq_integer]
  have hsq : (1 : ℝ) ≤ (integralCuspCross g h : ℝ)^2 :=
    integer_cross_square_one_le (g 0 0) (h 0 0) (g 1 0) (h 1 0) hn
  have hfirst : 1 ≤ (integralCuspCross g h : ℝ)^2*H :=
    hsq.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hH (sq_nonneg (integralCuspCross g h : ℝ)))
  exact hfirst.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ (integralCuspCross g h : ℝ)^2*H))

/-- All actual integral cusp columns, including either infinity case,
have disjoint strict high images at the true uniform threshold. -/
theorem integral_strict_high_images_disjoint (g h : SL(2, ℤ)) {H J : ℝ}
    (hH : 1 ≤ H) (hJ : 1 ≤ J) (hn : integralCuspCross g h ≠ 0) :
    Disjoint (g • strictHeightHalfSpace H) (h • strictHeightHalfSpace J) := by
  let G := integralReal g
  let K := integralReal h
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hJp : 0 < J := lt_of_lt_of_le (by norm_num) hJ
  have hsep : 1 ≤ (cuspCross G K)^2*H*J := uniform_threshold g h hH hJ hn
  have hcross : cuspCross G K ≠ 0 := by
    rw [real_cross_eq_integer]
    exact_mod_cast hn
  rw [← real_image_eq_integral g, ← real_image_eq_integral h]
  change Disjoint (G • strictHeightHalfSpace H) (K • strictHeightHalfSpace J)
  by_cases hc : G 1 0 = 0
  · have hd : K 1 0 ≠ 0 := by intro hd; simp [cuspCross, hc, hd] at hcross
    exact mixed_strict_images_disjoint G K hHp hJp hc hd hsep
  · by_cases hd : K 1 0 = 0
    · have hswap : 1 ≤ (cuspCross K G)^2*J*H := by
        rw [cross_swap, neg_sq]
        nlinarith [hsep]
      exact (mixed_strict_images_disjoint K G hJp hHp hd hc hswap).symm
    · exact strict_horoball_images_disjoint G K hHp hJp hc hd hsep

/-- Integral determinant +/-1 gives an actual singleton Ford contact;
the finite/finite and infinity/finite cases use their exact real suppliers. -/
theorem integral_Ford_contact (g h : SL(2, ℤ))
    (hunit : integralCuspCross g h = 1 ∨ integralCuspCross g h = -1) :
    ∃ z : UpperHalfPlane, (g • heightHalfSpace 1) ∩ (h • heightHalfSpace 1) = {z} := by
  let G := integralReal g
  let K := integralReal h
  have hthreshold : (cuspCross G K)^2*(1 : ℝ)*1 = 1 := by
    rw [real_cross_eq_integer]
    rcases hunit with hu | hu <;> simp [hu]
  have hcross : cuspCross G K ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide), zero_mul, zero_mul] at hthreshold
    norm_num at hthreshold
  rw [← real_image_eq_integral g, ← real_image_eq_integral h]
  change ∃ z : UpperHalfPlane, (G • heightHalfSpace 1) ∩ (K • heightHalfSpace 1) = {z}
  by_cases hc : G 1 0 = 0
  · have hd : K 1 0 ≠ 0 := by intro hd; simp [cuspCross, hc, hd] at hcross
    obtain ⟨z, hx, hy, hz⟩ := mixed_closed_images_tangency G K (by norm_num) (by norm_num) hc hd hthreshold
    exact ⟨z, hz⟩
  · by_cases hd : K 1 0 = 0
    · have hswap : (cuspCross K G)^2*(1 : ℝ)*1 = 1 := by
        rw [cross_swap, neg_sq]
        exact hthreshold
      obtain ⟨z, hx, hy, hz⟩ := mixed_closed_images_tangency K G (by norm_num) (by norm_num) hd hc hswap
      exact ⟨z, by simpa only [Set.inter_comm] using hz⟩
    · exact horoball_images_intersection_singleton G K (by norm_num) (by norm_num) hc hd hthreshold

end
end ImbalancedChen.Part3.IntegralCuspFordGeometry20261026b
