import ImbalancedChen.Part3RealPotentialSecondOrderIVP
import Mathlib.Analysis.Calculus.MeanValue

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

For genuine solutions f''=V*f and g''=V*g, zero ordinary Wronskian at
ONE anchor with a nonzero reference value determines proportional jets.
The proved native IVP then makes f=c*g on the ENTIRE original half-line,
including every zero of g. A second API allows a nonzero reference jet
with g(a)=0 and g'(a)!=0. No nowhere-zero hypothesis is used.

The nonzero reference jet is an honest primitive input. For actual K
selection the caller must derive an anchor from the actual asymptotic;
this module does not claim W=0 implies f=c*g when g is identically zero.
The Wronskian need only vanish at the selected anchor, even when its
vanishing is supplied solely by a separate far-tail argument.
-/

namespace ImbalancedChen.Part3.RealPotentialWronskianDependence20261026b
noncomputable section
open Set Filter
open scoped Topology
open RealPotentialSecondOrderIVP20261026b

def potentialWronskian (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  f y * deriv g y - deriv f y * g y

/-- Actual native jets differentiate the Wronskian to zero. -/
theorem potentialWronskian_hasDerivAt_zero {V : ℝ → ℝ} {Y : ℝ} {f g : ℝ → ℂ}
    (hf : CuspPotentialSolution V Y f) (hg : CuspPotentialSolution V Y g)
    {y : ℝ} (hy : Y < y) : HasDerivAt (potentialWronskian f g) 0 y := by
  have hd := ((hf y hy).1.mul (hg y hy).2).sub ((hf y hy).2.mul (hg y hy).1)
  convert hd using 1 <;> dsimp [potentialWronskian] <;> ring

theorem potentialWronskian_eq {V : ℝ → ℝ} {Y : ℝ} {f g : ℝ → ℂ}
    (hf : CuspPotentialSolution V Y f) (hg : CuspPotentialSolution V Y g)
    {a b : ℝ} (ha : Y < a) (hb : Y < b) :
    potentialWronskian f g a = potentialWronskian f g b := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro y hy
    exact (potentialWronskian_hasDerivAt_zero hf hg hy).differentiableAt.differentiableWithinAt
  · intro y hy
    exact (potentialWronskian_hasDerivAt_zero hf hg hy).deriv
  · exact ha
  · exact hb

theorem cuspPotentialSolution_const_mul {V : ℝ → ℝ} {Y : ℝ} {g : ℝ → ℂ}
    (hg : CuspPotentialSolution V Y g) (c : ℂ) :
    CuspPotentialSolution V Y (fun y => c * g y) := by
  have hderiv (y : ℝ) (hy : Y < y) :
      deriv (fun t => c * g t) y = c * deriv g y := ((hg y hy).1.const_mul c).deriv
  intro y hy
  constructor
  · rw [hderiv y hy]
    exact (hg y hy).1.const_mul c
  · have heq : deriv (fun t => c * g t) =ᶠ[𝓝 y] (fun t => c * deriv g t) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact hderiv t ht
    convert ((hg y hy).2.const_mul c).congr_of_eventuallyEq heq using 1 <;> ring

/-- ZERO W AT ONE ANCHOR suffices. The reference may have arbitrary
zeros elsewhere; native IVP propagates over the original entire domain. -/
theorem cusp_solution_eq_unique_scalar_of_wronskian_value
    {V : ℝ → ℝ} {Y a : ℝ} {f g : ℝ → ℂ}
    (hV : ContinuousOn V (Ioi Y))
    (hf : CuspPotentialSolution V Y f) (hg : CuspPotentialSolution V Y g)
    (ha : Y < a)
    (hW : f a * deriv g a - deriv f a * g a = 0) (hga : g a ≠ 0) :
    ∃! c : ℂ, ∀ y : ℝ, Y < y → f y = c * g y := by
  let c : ℂ := f a / g a
  have hvalue : f a = (fun y => c * g y) a := by dsimp [c]; field_simp [hga]
  have hderiv0 : deriv f a = c * deriv g a := by
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hga).mpr
    linear_combination -hW
  have hderiv : deriv f a = deriv (fun y => c * g y) a := by
    rw [((hg a ha).1.const_mul c).deriv]
    exact hderiv0
  have hrep := cusp_initial_value_unique hV hf (cuspPotentialSolution_const_mul hg c)
    ha hvalue hderiv
  refine ⟨c, fun y hy => hrep hy, ?_⟩
  intro d hd
  apply mul_right_cancel₀ hga
  exact (hd a ha).symm.trans (hrep ha)

/-- Nonzero reference JET suffices even if the anchor is a zero of g.
In that case the Wronskian forces f(a)=0, and derivative data select c. -/
theorem cusp_solution_eq_unique_scalar_of_wronskian_jet
    {V : ℝ → ℝ} {Y a : ℝ} {f g : ℝ → ℂ}
    (hV : ContinuousOn V (Ioi Y))
    (hf : CuspPotentialSolution V Y f) (hg : CuspPotentialSolution V Y g)
    (ha : Y < a)
    (hW : f a * deriv g a - deriv f a * g a = 0)
    (hjet : g a ≠ 0 ∨ deriv g a ≠ 0) :
    ∃! c : ℂ, ∀ y : ℝ, Y < y → f y = c * g y := by
  by_cases hga : g a = 0
  · have hdga : deriv g a ≠ 0 := hjet.resolve_left (not_not.mpr hga)
    have hfa : f a = 0 := by
      rw [hga, mul_zero, sub_zero] at hW
      exact (mul_eq_zero.mp hW).resolve_right hdga
    let c : ℂ := deriv f a / deriv g a
    have hvalue : f a = (fun y => c * g y) a := by simp only [hfa, hga, mul_zero]
    have hderiv : deriv f a = deriv (fun y => c * g y) a := by
      rw [((hg a ha).1.const_mul c).deriv]
      dsimp [c]
      field_simp [hdga]
    have hrep := cusp_initial_value_unique hV hf (cuspPotentialSolution_const_mul hg c)
      ha hvalue hderiv
    refine ⟨c, fun y hy => hrep hy, ?_⟩
    intro d hd
    have heq : (fun y => d * g y) =ᶠ[𝓝 a] f := by
      filter_upwards [Ioi_mem_nhds ha] with y hy
      exact (hd y hy).symm
    have hdvalue : d * deriv g a = deriv f a :=
      (((hg a ha).1.const_mul d).congr_of_eventuallyEq heq.symm).deriv.symm
    apply mul_right_cancel₀ hdga
    calc
      d * deriv g a = deriv f a := hdvalue
      _ = c * deriv g a := by dsimp [c]; field_simp [hdga]
  · exact cusp_solution_eq_unique_scalar_of_wronskian_value hV hf hg ha hW hga

/-- C2 + literal ODE caller API with a SINGLE nonzero reference value. -/
theorem cusp_C2_solution_eq_unique_scalar_of_wronskian_value
    {V : ℝ → ℝ} {Y a : ℝ} {f g : ℝ → ℂ}
    (hV : ContinuousOn V (Ioi Y))
    (hf : ContDiffOn ℝ 2 f (Ioi Y)) (hg : ContDiffOn ℝ 2 g (Ioi Y))
    (hfODE : ∀ y : ℝ, Y < y → deriv (deriv f) y = (V y : ℂ) * f y)
    (hgODE : ∀ y : ℝ, Y < y → deriv (deriv g) y = (V y : ℂ) * g y)
    (ha : Y < a)
    (hW : f a * deriv g a - deriv f a * g a = 0) (hga : g a ≠ 0) :
    ∃! c : ℂ, ∀ y : ℝ, Y < y → f y = c * g y :=
  cusp_solution_eq_unique_scalar_of_wronskian_value hV
    (cuspPotentialSolution_of_contDiffOn hf hfODE)
    (cuspPotentialSolution_of_contDiffOn hg hgODE) ha hW hga

end
end ImbalancedChen.Part3.RealPotentialWronskianDependence20261026b
