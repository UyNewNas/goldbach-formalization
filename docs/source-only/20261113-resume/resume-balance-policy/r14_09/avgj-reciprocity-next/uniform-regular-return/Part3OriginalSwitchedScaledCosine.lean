import ImbalancedChen.Part3OriginalSwitchedRegularModePrice
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Dilate the actual cosine transform before making the hyperbolic
substitution. The Schwartz seminorms therefore live at unit scale. -/
namespace ImbalancedChen.Part3.OriginalSwitchedScaledCosine20261113
noncomputable section
open Set MeasureTheory Complex FourierTransform
open scoped Topology FourierTransform
open OriginalSwitchedSchwartzPrices20261113
open OriginalSwitchedCutoffModes20261113 (mode)
open ActualPositiveCosineProfile20261112 (cosineTest cosineTest_apply testDiv)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private physical evenDiv frequency from ImbalancedChen.Part3ActualPositiveCosineProfile
open private front front_control from ImbalancedChen.Part3OriginalSwitchedRegularModePrice
open private finite_price from ImbalancedChen.Part3OriginalSwitchedSchwartzPrices

abbrev unitCos (k : ℤ) := cosineTest (mode k) (show (0:ℝ)<1 by norm_num)

theorem scaled_cosine (k : ℤ) {V : ℝ} (vp : 0<V) (y : ℝ) :
    cosineTest (mode k) vp y=unitCos k (V*y) := by
  rw [cosineTest_apply,show unitCos k (V*y)=∫ x in Ioi (0:ℝ),
    (Real.cos (x*(V*y)):ℂ)*testDiv (mode k) 1 x from cosineTest_apply _ _ _]
  let G := fun x : ℝ => (Real.cos (x*y):ℂ)*testDiv (mode k) V x
  have S := integral_comp_mul_left_Ioi' G 0 vp
  rw [mul_zero] at S
  change (∫ x in Ioi (0:ℝ),G x)=_
  rw [←S,←integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have a : V*x/V=x := by field_simp [vp.ne']
  simp only [G,testDiv,spectralTest,a,div_one,Complex.real_smul,Nat.cast_one,
    show V*x*y=x*(V*y) by ring,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr vp.ne',Complex.ofReal_ne_zero.mpr hx.ne'] <;> ring

private theorem unit_control : Controlled unitCos := by
  let p : (0:ℝ)<1 := by norm_num
  let N : Space→L[ℂ]Space := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E:=ℝ))
  have H := front_control p
  have U : Controlled (fun k => physical (mode k) p) := by
    have A := add_control H (map_control H N)
    have E (k : ℤ) : physical (mode k) p=front k p+N (front k p) := by ext x;rfl
    simpa only [E] using A
  let M : Space→L[ℂ]Space := (1/2:ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequency).comp (fourierCLM ℂ Space)
  exact map_control U M

/-- Uniform joint bound for all jets used in three integrations by
parts. Constants are chosen before the period frequency. -/
theorem unit_jets :
    ∃ (r : ℕ) (C : ℝ),0≤C ∧ ∀ (k : ℤ) (j : ℕ),j≤3 → ∀ y : ℝ,0≤y →
      (1+y)*y^j*‖iteratedDeriv j (unitCos k) y‖≤C*(weight k)^r := by
  let P := fun j k => SchwartzMap.seminorm ℂ j j (unitCos k)+SchwartzMap.seminorm ℂ (j+1) j (unitCos k)
  obtain ⟨r,C,c,B⟩ := finite_price (Finset.range 4) P (fun j _ =>
    price_add (unit_control j j) (unit_control (j+1) j))
  refine ⟨r,C,c,fun k j hj y yp => ?_⟩
  have a := SchwartzMap.le_seminorm' ℂ j j (unitCos k) y
  have b := SchwartzMap.le_seminorm' ℂ (j+1) j (unitCos k) y
  simp only [Real.norm_eq_abs,abs_of_nonneg yp,pow_succ] at a b
  apply le_trans _ (B k)
  apply le_trans _ (Finset.single_le_sum (f:=fun j => P j k)
    (fun i _ => add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    (Finset.mem_range.mpr (show j<4 by omega)))
  dsimp only [P]
  nlinarith only [a,b]

/-- All three derivatives of the physical small-scale profile are
bounded by genuine jets at v=V cosh(u), since |V sinh(u)|≤v. -/
theorem third_jet (f : Space) (V u : ℝ) :
    let v := V*Real.cosh u
    let w := V*Real.sinh u
    iteratedDeriv 3 (fun x => f (V*Real.cosh x)) u=
      (w:ℂ)*deriv f v+3*(w:ℂ)*(v:ℂ)*iteratedDeriv 2 f v+
        (w:ℂ)^3*iteratedDeriv 3 f v := by
  let v := fun x : ℝ => V*Real.cosh x
  let w := fun x : ℝ => V*Real.sinh x
  have hv (x : ℝ) : HasDerivAt v (w x) x := (Real.hasDerivAt_cosh x).const_mul V
  have hw (x : ℝ) : HasDerivAt w (v x) x := (Real.hasDerivAt_sinh x).const_mul V
  have dj (j : ℕ) (x : ℝ) : HasDerivAt (fun y => iteratedDeriv j f (v y))
      (iteratedDeriv (j+1) f (v x)*(w x:ℂ)) x := by
    have A := ((f.smooth ⊤).differentiable_iteratedDeriv j (by simp) (v x)).hasDerivAt.scomp x (hv x)
    simpa only [iteratedDeriv_succ,Complex.real_smul,Function.comp_def,mul_comm] using A
  have D1 : deriv (fun x => f (v x))=fun x => deriv f (v x)*(w x:ℂ) := by
    funext x
    simpa only [iteratedDeriv_zero,iteratedDeriv_one] using (dj 0 x).deriv
  have D2 : deriv (fun x => deriv f (v x)*(w x:ℂ))=
      fun x => iteratedDeriv 2 f (v x)*(w x:ℂ)^2+deriv f (v x)*(v x:ℂ) := by
    funext x
    have H := ((dj 1 x).mul (hw x).ofReal_comp).deriv
    simp only [iteratedDeriv_one] at H
    rw [H];ring
  change iteratedDeriv 3 (fun x => f (v x)) u=_
  rw [show iteratedDeriv 3 (fun x => f (v x))=
    deriv (deriv (deriv (fun x => f (v x)))) by simp [iteratedDeriv_succ],D1,D2]
  have A := (dj 2 u).mul ((hw u).ofReal_comp.pow 2)
  have B := (dj 1 u).mul (hv u).ofReal_comp
  simp only [iteratedDeriv_one] at B
  rw [(A.add B).deriv]
  dsimp only [v,w];ring

end
end ImbalancedChen.Part3.OriginalSwitchedScaledCosine20261113
