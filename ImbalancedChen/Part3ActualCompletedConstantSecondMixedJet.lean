import ImbalancedChen.Part3ActualCompletedFourierParameterMixedJets

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The second spatial jet of the actual completed constant is parameter
holomorphic by its proved actual Euler equation. Its honest parameter/y
commutation follows from the actual affine-power computation off 1/2,
and from true reflection plus holomorphy at 1/2. This is the missing
constant-term ingredient for a genuine spatial Laplacian of d_s E.
-/

namespace ImbalancedChen.Part3.ActualCompletedConstantSecondMixedJet20261026b
noncomputable section
open Set Complex Filter Topology
open CompletedEisensteinReflection20261025a CompletedEisensteinSpatialMaass
open ActualCompletedConstantParameterJets20261026b ActualCompletedConstantMixedDerivative20261026b

theorem completedSecond_eq_euler (s : ℂ) {y : ℝ} (hy : 0 < y) :
    completedSecond s y = -(s * (1 - s) * completedConstant y s) / (y : ℂ) ^ 2 := by
  have h := completedConstant_euler s hy
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  field_simp [hyC] at h ⊢
  linear_combination -h

theorem completedSecond_parameter_differentiableAt {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ (fun w : ℂ => completedSecond w y) s := by
  have he : (fun w : ℂ => completedSecond w y) =
      (fun w : ℂ => -(w * (1 - w) * completedConstant y w) / (y : ℂ) ^ 2) :=
    funext (fun w => completedSecond_eq_euler w hy)
  rw [he]
  exact ((differentiableAt_id.mul (differentiableAt_const.sub differentiableAt_id)).mul
    (completedConstant_parameter_differentiableAt hs0 hs1 hy)).neg.div_const _

theorem completedSecond_parameter_deriv_half {y : ℝ} (hy : 0 < y) :
    deriv (fun w : ℂ => completedSecond w y) (1 / 2 : ℂ) = 0 := by
  apply deriv_half_eq_zero_of_reflection _
    (completedSecond_parameter_differentiableAt (by norm_num) (by norm_num) hy)
  intro w
  rw [completedSecond_eq_euler (1 - w) hy, completedSecond_eq_euler w hy,
    completedConstant_reflection]
  congr 2
  ring

theorem completedFirst_parameter_hasDerivAt_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (fun w : ℂ => completedFirst w t) s)
      (deriv (fun w : ℂ => completedSecond w y) s) y := by
  by_cases hh : s = 1 / 2
  · subst s
    rw [completedSecond_parameter_deriv_half hy]
    apply (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact completedFirst_parameter_deriv_half ht
  · have hA : DifferentiableAt ℂ (fun w : ℂ => completedRiemannZeta (2 * w)) s := by
      apply (differentiableAt_completedZeta (mul_ne_zero (by norm_num) hs0) ?_).comp s
        (differentiable_id.const_mul (2 : ℂ) s)
      intro h; apply hh; linear_combination (1 / 2 : ℂ) * h
    have hB : DifferentiableAt ℂ (fun w : ℂ => completedRiemannZeta (2 * w - 1)) s := by
      apply (differentiableAt_completedZeta ?_ ?_).comp s
        ((differentiable_id.const_mul (2 : ℂ)).sub_const 1 s)
      · intro h; apply hh; linear_combination (1 / 2 : ℂ) * h
      · intro h; apply hs1; linear_combination (1 / 2 : ℂ) * h
    let A : ℂ → ℂ := fun w => completedRiemannZeta (2 * w) * w
    let B : ℂ → ℂ := fun w => completedRiemannZeta (2 * w - 1) * (1 - w)
    have hAc : DifferentiableAt ℂ A s := hA.mul differentiableAt_id
    have hBc : DifferentiableAt ℂ B s := hB.mul (differentiableAt_const.sub differentiableAt_id)
    have hAp := affineHeight_parameter_hasDerivAt_y A (-1) 1 s hAc
      (by intro h; apply hs1; linear_combination h) hy
    have hBp := affineHeight_parameter_hasDerivAt_y B 0 (-1) s hBc
      (by simpa using neg_ne_zero.mpr hs0) hy
    have he1 (t : ℝ) : (fun w : ℂ => completedFirst w t) =ᶠ[𝓝 s]
        (fun w : ℂ => A w * (t : ℂ) ^ (-1 + 1 * w) + B w * (t : ℂ) ^ (0 + (-1) * w)) := by
      filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hh] with w hw
      simp only [completedFirst, if_neg hw, noncentralFirst, heightFirst, A, B]
      have h1 : -1 + 1 * w = w - 1 := by ring
      have h2 : 1 - w - 1 = 0 + (-1) * w := by ring
      rw [h1, h2]
      ring
    have he2 : (fun w : ℂ => completedSecond w y) =ᶠ[𝓝 s]
        (fun w : ℂ => A w * heightFirst (-1 + 1 * w) y + B w * heightFirst (0 + (-1) * w) y) := by
      filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hh] with w hw
      simp only [completedSecond, if_neg hw, noncentralSecond, heightSecond, heightFirst, A, B]
      have h1 : -1 + 1 * w = w - 1 := by ring
      have h2 : 0 + (-1) * w = 1 - w - 1 := by ring
      have h3 : w - 1 - 1 = w - 2 := by ring
      have h4 : 1 - w - 1 - 1 = 1 - w - 2 := by ring
      rw [h1, h2, h3, h4]
      ring
    have hPA (t : ℝ) (ht : 0 < t) : DifferentiableAt ℂ (fun w : ℂ => A w * (t : ℂ) ^ (-1 + 1 * w)) s :=
      hAc.mul ((((differentiableAt_id.const_mul (1 : ℂ)).const_add (-1 : ℂ))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne')))
    have hPB (t : ℝ) (ht : 0 < t) : DifferentiableAt ℂ (fun w : ℂ => B w * (t : ℂ) ^ (0 + (-1) * w)) s :=
      hBc.mul ((((differentiableAt_id.const_mul (-1 : ℂ)).const_add (0 : ℂ))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne')))
    have he : (fun t : ℝ => deriv (fun w : ℂ => completedFirst w t) s) =ᶠ[𝓝 y]
        (fun t : ℝ => deriv (fun w : ℂ => A w * (t : ℂ) ^ (-1 + 1 * w)) s +
          deriv (fun w : ℂ => B w * (t : ℂ) ^ (0 + (-1) * w)) s) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      rw [(he1 t).deriv_eq]
      exact ((hPA t ht).hasDerivAt.add (hPB t ht).hasDerivAt).deriv
    have hHA : DifferentiableAt ℂ (fun w : ℂ => A w * heightFirst (-1 + 1 * w) y) s :=
      hAc.mul ((heightFirst_parameter_differentiable hy).comp
        ((differentiable_id.const_mul (1 : ℂ)).const_add (-1 : ℂ)) s)
    have hHB : DifferentiableAt ℂ (fun w : ℂ => B w * heightFirst (0 + (-1) * w) y) s :=
      hBc.mul ((heightFirst_parameter_differentiable hy).comp
        ((differentiable_id.const_mul (-1 : ℂ)).const_add (0 : ℂ)) s)
    rw [he2.deriv_eq, (hHA.hasDerivAt.add hHB.hasDerivAt).deriv]
    exact (hAp.add hBp).congr_of_eventuallyEq he

end
end ImbalancedChen.Part3.ActualCompletedConstantSecondMixedJet20261026b
