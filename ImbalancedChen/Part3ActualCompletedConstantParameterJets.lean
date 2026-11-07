import ImbalancedChen.Part3ActualFourierParameterSpatialCommutation
import ImbalancedChen.Part3CompletedEisensteinSpatialMaass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

An actual regularized formula for the first spatial jet of the completed
constant term. Its divided difference Q has the exact recurrence
  Q_y = (Q + y^s + y^(1-s))/(2*y),
INCLUDING the derivative-defined value s=1/2. This proves holomorphy of
the actual first y derivative at the central parameter; no continuity of
spatial jets in parameter or false totalized-Lambda formula is assumed.
-/

namespace ImbalancedChen.Part3.ActualCompletedConstantParameterJets20261026b
noncomputable section
open Set Complex Filter Topology
open CompletedEisensteinReflection20261025a CompletedEisensteinMeromorphic20261025a
open CompletedEisensteinSpatialMaass CompletedEisensteinCentralHeight
open ContinuedFourierNonconstantMaass

theorem heightFirst_eq_power_div (p : ℂ) {y : ℝ} (hy : 0 < y) :
    heightFirst p y = p * (y : ℂ) ^ p / (y : ℂ) := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [heightFirst, Complex.cpow_sub p 1 hyC, Complex.cpow_one]
  ring

def heightQuotientFirst (s : ℂ) (y : ℝ) : ℂ :=
  (reflectionHeightQuotient y s + (y : ℂ) ^ s + (y : ℂ) ^ (1 - s)) / (2 * (y : ℂ))

/-- The recurrence includes the central logarithmic derivative value. -/
theorem reflectionHeightQuotient_hasDerivAt_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => reflectionHeightQuotient t s) (heightQuotientFirst s y) y := by
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  by_cases hh : s = 1 / 2
  · subst s
    have hlog : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (y : ℂ)⁻¹ y := by
      simpa only [Complex.ofReal_inv] using (Real.hasDerivAt_log hy.ne').ofReal_comp
    have h := (root0_hasDerivAt hy).mul hlog
    have he : (fun t : ℝ => reflectionHeightQuotient t (1 / 2 : ℂ)) =ᶠ[𝓝 y]
        (fun t : ℝ => root0 t * (Real.log t : ℂ)) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact reflectionHeightQuotient_half t ht
    have hval : heightQuotientFirst (1 / 2 : ℂ) y =
        root1 y * (Real.log y : ℂ) + root0 y * (y : ℂ)⁻¹ := by
      rw [heightQuotientFirst, reflectionHeightQuotient_half y hy,
        show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, complex_half_power_eq_root0 y hy]
      have hr := root1_relation hy
      field_simp [hyC] at hr ⊢
      linear_combination -(Real.log y : ℂ) * hr
    rw [hval]
    exact h.congr_of_eventuallyEq he
  · have hd : 2 * s - 1 ≠ 0 := by intro h; apply hh; linear_combination (1 / 2 : ℂ) * h
    have h := ((heightPower_hasDerivAt s hs0 hy).sub
      (heightPower_hasDerivAt (1 - s) (sub_ne_zero.mpr hs1.symm) hy)).div_const (2 * s - 1)
    have he : (fun t : ℝ => reflectionHeightQuotient t s) =
        (fun t : ℝ => ((t : ℂ) ^ s - (t : ℂ) ^ (1 - s)) / (2 * s - 1)) :=
      funext (fun t => reflectionHeightQuotient_eq_div t s hh)
    rw [he]
    convert h using 1
    rw [heightQuotientFirst, reflectionHeightQuotient_eq_div y s hh, heightDifference,
      heightFirst_eq_power_div s hy, heightFirst_eq_power_div (1 - s) hy]
    field_simp [hyC, hd]
    ring

theorem heightQuotientFirst_parameter_differentiable {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => heightQuotientFirst s y) :=
  (((reflectionHeightQuotient_entire hy).add (heightPower_differentiable hy)).add
    (reflectedHeightPower_differentiable hy)).div_const (2 * (y : ℂ))

def regularizedConstantFirst (s : ℂ) (y : ℝ) : ℂ :=
  completedRiemannZeta₀ (2 * s) * heightFirst s y +
    completedRiemannZeta₀ (2 * s - 1) * heightFirst (1 - s) y -
    heightFirst s y / (2 * s) - heightFirst (1 - s) y / (2 * (1 - s)) +
    heightQuotientFirst s y

theorem completedConstant_hasDerivAt_regularized (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedConstant t s) (regularizedConstantFirst s y) y := by
  exact (((((heightPower_hasDerivAt s hs0 hy).const_mul (completedRiemannZeta₀ (2 * s))).add
    ((heightPower_hasDerivAt (1 - s) (sub_ne_zero.mpr hs1.symm) hy).const_mul
      (completedRiemannZeta₀ (2 * s - 1)))).sub
        ((heightPower_hasDerivAt s hs0 hy).div_const (2 * s))).sub
          ((heightPower_hasDerivAt (1 - s) (sub_ne_zero.mpr hs1.symm) hy).div_const (2 * (1 - s)))).add
            (reflectionHeightQuotient_hasDerivAt_y s hs0 hs1 hy)

/-- Identification with the PREEXISTING literal first spatial derivative,
including its central branch; no new prescribed jet is substituted. -/
theorem completedFirst_eq_regularized (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    completedFirst s y = regularizedConstantFirst s y :=
  (completedConstant_hasDerivAt s hs0 hs1 hy).unique
    (completedConstant_hasDerivAt_regularized s hs0 hs1 hy)

theorem heightFirst_parameter_differentiable {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => heightFirst s y) := by
  have hp := (differentiable_id.sub_const (1 : ℂ)).const_cpow
    (c := (y : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  exact differentiable_id.mul hp

theorem regularizedConstantFirst_parameter_differentiableAt {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ (fun w : ℂ => regularizedConstantFirst w y) s := by
  have hH := heightFirst_parameter_differentiable hy
  have hR : Differentiable ℂ (fun w : ℂ => heightFirst (1 - w) y) :=
    hH.comp (differentiable_const.sub differentiable_id)
  have hZ := differentiable_completedZeta₀.comp (differentiable_id.const_mul (2 : ℂ))
  have hZr := differentiable_completedZeta₀.comp ((differentiable_id.const_mul (2 : ℂ)).sub_const 1)
  have hD := (differentiable_id.const_mul (2 : ℂ)).differentiableAt
  have hDr := ((differentiable_const.sub differentiable_id).const_mul (2 : ℂ)).differentiableAt
  exact (((((hZ s).mul (hH s)).add ((hZr s).mul (hR s))).sub
    ((hH s).div hD (mul_ne_zero (by norm_num) hs0))).sub
      ((hR s).div hDr (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs1.symm)))).add
        (heightQuotientFirst_parameter_differentiable hy s)

theorem completedFirst_parameter_differentiableAt {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ (fun w : ℂ => completedFirst w y) s := by
  apply (regularizedConstantFirst_parameter_differentiableAt hs0 hs1 hy).congr_of_eventuallyEq
  filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hs0,
    (isOpen_ne continuous_id continuous_const).mem_nhds hs1] with w hw0 hw1
  exact completedFirst_eq_regularized w hw0 hw1 hy

theorem completedConstant_parameter_differentiableAt {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℂ (fun w : ℂ => completedConstant y w) s := by
  have hZ := differentiable_completedZeta₀.comp (differentiable_id.const_mul (2 : ℂ))
  have hZr := differentiable_completedZeta₀.comp ((differentiable_id.const_mul (2 : ℂ)).sub_const 1)
  have hH := heightPower_differentiable hy
  have hR := reflectedHeightPower_differentiable hy
  exact (((((hZ s).mul (hH s)).add ((hZr s).mul (hR s))).sub
    ((hH s).div (differentiable_id.const_mul (2 : ℂ) s) (mul_ne_zero (by norm_num) hs0))).sub
      ((hR s).div ((differentiable_const.sub differentiable_id).const_mul (2 : ℂ) s)
        (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs1.symm)))).add
          (reflectionHeightQuotient_entire hy s)

end
end ImbalancedChen.Part3.ActualCompletedConstantParameterJets20261026b
