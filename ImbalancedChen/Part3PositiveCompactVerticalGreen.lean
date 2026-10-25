import ImbalancedChen.Part3OneCompactCrossGreen
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

Positive-height generalization of the one-compact vertical integration
by parts: the noncompact second factor is C2 only on y>0. The compact
first factor and its derivative have support strictly in y>0. The three
native IBP integrability conditions are derived from those actual supports.
The zero extension at y=0 is never assumed smooth for the second factor.
-/

namespace ImbalancedChen.Part3.PositiveCompactVerticalGreen20261025a

noncomputable section
open Set Filter Topology MeasureTheory

theorem star_tsupport (a : ℝ → ℂ) : tsupport (fun y => star (a y)) = tsupport a := by
  unfold tsupport
  congr 1
  ext y
  simp only [Function.mem_support,ne_eq,star_eq_zero]

theorem positive_compact_product_continuous (a J : ℝ → ℂ)
    (ha : Continuous a) (hap : tsupport a ⊆ Ioi (0 : ℝ))
    (hJ : ContinuousOn J (Ioi (0 : ℝ))) : Continuous (fun y => a y*J y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : 0 < y
  · exact ha.continuousAt.mul ((hJ y hy).continuousAt (isOpen_Ioi.mem_nhds hy))
  · have hnot : y ∉ tsupport a := fun h => hy (hap h)
    have heq : (fun t => a t*J t) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hnot] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]
    exact continuousAt_const.congr_of_eventuallyEq heq

theorem positive_compact_product_integrable (a J : ℝ → ℂ)
    (ha : Continuous a) (hac : HasCompactSupport a) (hap : tsupport a ⊆ Ioi (0 : ℝ))
    (hJ : ContinuousOn J (Ioi (0 : ℝ))) : Integrable (fun y => a y*J y) :=
  (positive_compact_product_continuous a J ha hap hJ).integrable_of_hasCompactSupport hac.mul_right

/-- Masking by a genuinely positive-support factor produces a global C2
function even when the unmasked chart function is only C2 for y>0. -/
theorem positive_mask_C2 (a g : ℝ → ℂ) (ha : ContDiff ℝ 2 a)
    (hap : tsupport a ⊆ Ioi (0 : ℝ)) (hg : ContDiffOn ℝ 2 g (Ioi (0 : ℝ))) :
    ContDiff ℝ 2 (fun y => a y*g y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < y
  · exact ha.contDiffAt.mul ((hg y hy).contDiffAt (isOpen_Ioi.mem_nhds hy))
  · have hnot : y ∉ tsupport a := fun h => hy (hap h)
    have heq : (fun t => a t*g t) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hnot] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The positive-chart test can be noncompact; no target integrability
or boundary conclusion is assumed. -/
theorem positive_compact_vertical_green (P g : ℝ → ℂ)
    (hP : ContDiff ℝ 2 P) (hPc : HasCompactSupport P)
    (hPp : tsupport P ⊆ Ioi (0 : ℝ)) (hg : ContDiffOn ℝ 2 g (Ioi (0 : ℝ))) :
    (∫ y in Ioi (0 : ℝ), star (P y)*(-deriv (deriv g) y)) =
      ∫ y in Ioi (0 : ℝ), star (deriv P y)*deriv g y := by
  have hPd : ContDiff ℝ 1 (deriv P) := hP.deriv'
  have hPdp : tsupport (deriv P) ⊆ Ioi (0 : ℝ) := tsupport_deriv_subset.trans hPp
  have hgd : ContDiffOn ℝ 1 (deriv g) (Ioi (0 : ℝ)) :=
    hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hgdd : ContinuousOn (deriv (deriv g)) (Ioi (0 : ℝ)) :=
    hgd.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hi₀ : Integrable (fun y => star (P y)*deriv g y) :=
    positive_compact_product_integrable _ _ hP.continuous.star
      (hPc.comp_left (g := star) (by simp)) (by simpa only [star_tsupport] using hPp) hgd.continuousOn
  have hi₁ : Integrable (fun y => star (P y)*deriv (deriv g) y) :=
    positive_compact_product_integrable _ _ hP.continuous.star
      (hPc.comp_left (g := star) (by simp)) (by simpa only [star_tsupport] using hPp) hgdd
  have hi₂ : Integrable (fun y => star (deriv P y)*deriv g y) :=
    positive_compact_product_integrable _ _ hPd.continuous.star
      (hPc.deriv.comp_left (g := star) (by simp))
      (by simpa only [star_tsupport] using hPdp) hgd.continuousOn
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun y => star (P y)) (v := deriv g)
    (u' := fun y => star (deriv P y)) (v' := deriv (deriv g))
    (fun y _ => (hP.differentiable (by norm_num) y).hasDerivAt.star)
    (fun y hy => by
      have hyp : 0 < y := hPp (by simpa only [star_tsupport] using hy)
      exact (((hgd y hyp).contDiffAt (isOpen_Ioi.mem_nhds hyp)).differentiableAt (by norm_num)).hasDerivAt)
    hi₁ hi₂ hi₀
  have hleft : (∫ y in Ioi (0 : ℝ), star (P y)*(-deriv (deriv g) y)) =
      ∫ y : ℝ, star (P y)*(-deriv (deriv g) y) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have hz : P y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hPp h))
      simp only [hz,star_zero,zero_mul])
  have hright : (∫ y in Ioi (0 : ℝ), star (deriv P y)*deriv g y) =
      ∫ y : ℝ, star (deriv P y)*deriv g y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have hz : deriv P y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hPdp h))
      simp only [hz,star_zero,zero_mul])
  rw [hleft,hright]
  simp_rw [mul_neg]
  rw [integral_neg,hparts,neg_neg]

end
end ImbalancedChen.Part3.PositiveCompactVerticalGreen20261025a
