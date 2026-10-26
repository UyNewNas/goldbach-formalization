import ImbalancedChen.Part3ActualCompletedConstantParameterJets

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Honest parameter/y commutation for the ACTUAL regularized completed
constant. Away from 1/2 a direct affine-height-power computation applies
to its two actual completed-zeta coefficients. At 1/2 the previously
proved holomorphy of the original completedFirst and literal reflection
force both parameter derivatives to vanish. Thus the central case uses
the genuine removable value, never the totalized two-Lambda expression.
-/

namespace ImbalancedChen.Part3.ActualCompletedConstantMixedDerivative20261026b
noncomputable section
open Set Complex Filter Topology
open ActualCompletedConstantParameterJets20261026b
open CompletedEisensteinReflection20261025a CompletedEisensteinMeromorphic20261025a
open CompletedEisensteinSpatialMaass

/-- Elementary mixed differentiation of a genuine affine-height power.
Only the coefficient's actual one-variable differentiability is needed. -/
theorem affineHeight_parameter_hasDerivAt_y (A : ℂ → ℂ) (a b s : ℂ)
    (hA : DifferentiableAt ℂ A s) (hp : a + b * s ≠ 0) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (fun w : ℂ => A w * (t : ℂ) ^ (a + b * w)) s)
      (deriv (fun w : ℂ => A w * heightFirst (a + b * w) y) s) y := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hparam (t : ℝ) (ht : 0 < t) :
      deriv (fun w : ℂ => A w * (t : ℂ) ^ (a + b * w)) s =
        deriv A s * (t : ℂ) ^ (a + b * s) +
          A s * ((t : ℂ) ^ (a + b * s) * (Real.log t : ℂ) * b) := by
    have hP := (((hasDerivAt_id s).const_mul b).const_add a).const_cpow
      (c := (t : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))
    convert (hA.hasDerivAt.mul hP).deriv using 1 <;>
      simp only [← Complex.ofReal_log ht.le] <;> ring
  have he : (fun t : ℝ => deriv (fun w : ℂ => A w * (t : ℂ) ^ (a + b * w)) s) =ᶠ[𝓝 y]
      (fun t : ℝ => deriv A s * (t : ℂ) ^ (a + b * s) +
        A s * ((t : ℂ) ^ (a + b * s) * (Real.log t : ℂ) * b)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hparam t ht
  have hP := heightPower_hasDerivAt (a + b * s) hp hy
  have hlog : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (y : ℂ)⁻¹ y := by
    simpa only [Complex.ofReal_inv] using (Real.hasDerivAt_log hy.ne').ofReal_comp
  have hleft := ((hP.const_mul (deriv A s)).add
    (((hP.mul hlog).mul_const b).const_mul (A s))).congr_of_eventuallyEq he
  have hlin := ((hasDerivAt_id s).const_mul b).const_add a
  have hP1 := (hlin.sub_const (1 : ℂ)).const_cpow (c := (y : ℂ)) (Or.inl hyC)
  have hright := hA.hasDerivAt.mul (hlin.mul hP1)
  have hrightEq : deriv (fun w : ℂ => A w * heightFirst (a + b * w) y) s =
      deriv A s * heightFirst (a + b * s) y +
        A s * (b * (y : ℂ) ^ (a + b * s - 1) +
          (a + b * s) * ((y : ℂ) ^ (a + b * s - 1) * (Real.log y : ℂ) * b)) := by
    convert hright.deriv using 1 <;> simp only [heightFirst, ← Complex.ofReal_log hy.le] <;> ring
  rw [hrightEq]
  convert hleft using 1
  simp only [heightFirst, Complex.cpow_sub _ 1 hyC, Complex.cpow_one]
  field_simp [hyC]
  ring

/-- Reflection around 1/2 forces the ACTUAL complex derivative to vanish. -/
theorem deriv_half_eq_zero_of_reflection (f : ℂ → ℂ)
    (hf : DifferentiableAt ℂ f (1 / 2 : ℂ)) (href : ∀ w : ℂ, f (1 - w) = f w) :
    deriv f (1 / 2 : ℂ) = 0 := by
  have hf' : HasDerivAt f (deriv f (1 / 2 : ℂ)) (1 - (1 / 2 : ℂ)) := by
    norm_num
    exact hf.hasDerivAt
  have h := hf'.comp (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1)
  have he : (fun w : ℂ => f (1 - w)) = f := funext href
  rw [he] at h
  have hEq := h.unique hf.hasDerivAt
  norm_num at hEq
  linear_combination -(1 / 2 : ℂ) * hEq

theorem completedFirst_reflection (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) : completedFirst (1 - s) y = completedFirst s y := by
  have hr0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hr1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  have h := completedConstant_hasDerivAt (1 - s) hr0 hr1 hy
  have he : (fun t : ℝ => completedConstant t (1 - s)) = (fun t : ℝ => completedConstant t s) :=
    funext (fun t => completedConstant_reflection t s)
  rw [he] at h
  exact h.unique (completedConstant_hasDerivAt s hs0 hs1 hy)

theorem completedConstant_parameter_deriv_half {y : ℝ} (hy : 0 < y) :
    deriv (fun w : ℂ => completedConstant y w) (1 / 2 : ℂ) = 0 :=
  deriv_half_eq_zero_of_reflection _
    (completedConstant_parameter_differentiableAt (by norm_num) (by norm_num) hy)
    (completedConstant_reflection y)

theorem completedFirst_parameter_deriv_half {y : ℝ} (hy : 0 < y) :
    deriv (fun w : ℂ => completedFirst w y) (1 / 2 : ℂ) = 0 := by
  have hf := (completedFirst_parameter_differentiableAt
    (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num) hy).hasDerivAt
  have hf' : HasDerivAt (fun w : ℂ => completedFirst w y)
      (deriv (fun w : ℂ => completedFirst w y) (1 / 2 : ℂ)) (1 - (1 / 2 : ℂ)) := by
    norm_num
    exact hf
  have h := hf'.comp (1 / 2 : ℂ) ((hasDerivAt_id (1 / 2 : ℂ)).const_sub 1)
  have he : (fun w : ℂ => completedFirst (1 - w) y) =ᶠ[𝓝 (1 / 2 : ℂ)]
      (fun w : ℂ => completedFirst w y) := by
    filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds (by norm_num : (1 / 2 : ℂ) ≠ 0),
      (isOpen_ne continuous_id continuous_const).mem_nhds (by norm_num : (1 / 2 : ℂ) ≠ 1)] with w hw0 hw1
    exact completedFirst_reflection w hw0 hw1 hy
  have h' := h.congr_of_eventuallyEq he.symm
  have hEq := h'.unique hf
  norm_num at hEq
  linear_combination -(1 / 2 : ℂ) * hEq

/-- Honest actual constant-term mixed derivative, including 1/2. -/
theorem completedConstant_parameter_hasDerivAt_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (fun w : ℂ => completedConstant t w) s)
      (deriv (fun w : ℂ => completedFirst w y) s) y := by
  by_cases hh : s = 1 / 2
  · subst s
    rw [completedFirst_parameter_deriv_half hy]
    apply (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact completedConstant_parameter_deriv_half ht
  · have hA : DifferentiableAt ℂ (fun w : ℂ => completedRiemannZeta (2 * w)) s := by
      apply (differentiableAt_completedZeta (mul_ne_zero (by norm_num) hs0) ?_).comp s
        (differentiable_id.const_mul (2 : ℂ) s)
      intro h; apply hh; linear_combination (1 / 2 : ℂ) * h
    have hB : DifferentiableAt ℂ (fun w : ℂ => completedRiemannZeta (2 * w - 1)) s := by
      apply (differentiableAt_completedZeta ?_ ?_).comp s
        ((differentiable_id.const_mul (2 : ℂ)).sub_const 1 s)
      · intro h; apply hh; linear_combination (1 / 2 : ℂ) * h
      · intro h; apply hs1; linear_combination (1 / 2 : ℂ) * h
    have hAp := affineHeight_parameter_hasDerivAt_y
      (fun w : ℂ => completedRiemannZeta (2 * w)) 0 1 s hA (by simpa using hs0) hy
    have hBp := affineHeight_parameter_hasDerivAt_y
      (fun w : ℂ => completedRiemannZeta (2 * w - 1)) 1 (-1) s hB
        (by simpa using sub_ne_zero.mpr hs1.symm) hy
    have hraw (t : ℝ) :
        deriv (fun w : ℂ => completedConstant t w) s =
          deriv (fun w : ℂ => completedRiemannZeta (2 * w) * (t : ℂ) ^ w +
            completedRiemannZeta (2 * w - 1) * (t : ℂ) ^ (1 - w)) s := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hh] with w hw
      exact completedConstant_eq_raw t w hw
    have hfirst : (fun w : ℂ => completedFirst w y) =ᶠ[𝓝 s]
        (fun w : ℂ => completedRiemannZeta (2 * w) * heightFirst w y +
          completedRiemannZeta (2 * w - 1) * heightFirst (1 - w) y) := by
      filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hh] with w hw
      simp only [completedFirst, if_neg hw, noncentralFirst]
    have hsum (t : ℝ) (ht : 0 < t) :
        deriv (fun w : ℂ => completedConstant t w) s =
          deriv (fun w : ℂ => completedRiemannZeta (2 * w) * (t : ℂ) ^ w) s +
            deriv (fun w : ℂ => completedRiemannZeta (2 * w - 1) * (t : ℂ) ^ (1 - w)) s := by
      rw [hraw]
      exact ((hA.mul (heightPower_differentiable ht s)).hasDerivAt.add
        (hB.mul (reflectedHeightPower_differentiable ht s)).hasDerivAt).deriv
    have he : (fun t : ℝ => deriv (fun w : ℂ => completedConstant t w) s) =ᶠ[𝓝 y]
        (fun t : ℝ => deriv (fun w : ℂ => completedRiemannZeta (2 * w) * (t : ℂ) ^ w) s +
          deriv (fun w : ℂ => completedRiemannZeta (2 * w - 1) * (t : ℂ) ^ (1 - w)) s) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact hsum t ht
    have hH := heightFirst_parameter_differentiable hy
    have hHr := hH.comp (differentiable_const.sub differentiable_id)
    rw [hfirst.deriv_eq, ((hA.mul (hH s)).hasDerivAt.add (hB.mul (hHr s)).hasDerivAt).deriv]
    convert (hAp.add hBp).congr_of_eventuallyEq (by simpa only [zero_add, one_mul, neg_one_mul, ← sub_eq_add_neg] using he) using 1 <;>
      simp only [zero_add, one_mul, neg_one_mul, ← sub_eq_add_neg]

theorem completedConstant_parameter_y_commute (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => completedConstant t w) s) y =
      deriv (fun w : ℂ => deriv (fun t : ℝ => completedConstant t w) y) s := by
  have he : (fun w : ℂ => deriv (fun t : ℝ => completedConstant t w) y) =ᶠ[𝓝 s]
      (fun w : ℂ => completedFirst w y) := by
    filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hs0,
      (isOpen_ne continuous_id continuous_const).mem_nhds hs1] with w hw0 hw1
    exact (completedConstant_hasDerivAt w hw0 hw1 hy).deriv
  rw [he.deriv_eq]
  exact (completedConstant_parameter_hasDerivAt_y s hs0 hs1 hy).deriv

end
end ImbalancedChen.Part3.ActualCompletedConstantMixedDerivative20261026b
