import ImbalancedChen.Part3ComplexOrderKRadialRegularity
import ImbalancedChen.Part3ComplexOrderKQODE
import ImbalancedChen.Part3ActualFourierBesselConjugation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual physical K reference: strong jets and physical ODE at all complex orders

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal reference F(y)=sqrt(y) K_nu(a*y), a>0, is C2 on y>0.
Actual dominated K moment derivatives give both physical derivatives;
the actual all-complex-order K ODE gives -F''+a^2 F=(1/4-nu^2)F/y^2.
No reference ODE, scalar classification, nonzero condition, basis or held
imaginary radial derivative supplier is a hypothesis.
-/

namespace ImbalancedChen.Part3.ActualPhysicalKJets20261026b

noncomputable section
open Set Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus ComplexOrderKQODE
open ComplexOrderKRadialRegularitySourceOnly ActualFourierBesselConjugation20261026a

/-- Literal physical-height K branch, at an unrestricted complex order. -/
def physicalK (nu : ℂ) (a y : ℝ) : ℂ :=
  (Real.sqrt y : ℂ)*complexOrderK nu (a*y)

def physicalKFirst (nu : ℂ) (a y : ℝ) : ℂ :=
  (1/2 : ℂ)*heightPower (-1/2) y*qMoment 0 nu (a*y)+
    (a : ℂ)*heightPower (1/2) y*qMoment 1 nu (a*y)

def physicalKSecond (nu : ℂ) (a y : ℝ) : ℂ :=
  (-1/4 : ℂ)*heightPower (-3/2) y*qMoment 0 nu (a*y)+
    (a : ℂ)*heightPower (-1/2) y*qMoment 1 nu (a*y)+
    (a : ℂ)^2*heightPower (1/2) y*qMoment 2 nu (a*y)

/-- Strong C2 regularity follows from actual radial K composed with the
positive logarithmic chart and the physical square-root multiplier. -/
theorem physicalK_contDiffOn_two (nu : ℂ) {a : ℝ} (ha : 0<a) :
    ContDiffOn ℝ 2 (physicalK nu a) (Ioi (0 : ℝ)) := by
  have hlog : ContDiffOn ℝ 2 (fun y : ℝ => Real.log (a*y)) (Ioi (0 : ℝ)) :=
    (contDiffOn_const.mul contDiffOn_id).log (fun y hy => (mul_pos ha hy).ne')
  have hsqrt : ContDiffOn ℝ 2 (fun y : ℝ => (Real.sqrt y : ℂ)) (Ioi (0 : ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_id.sqrt (fun y hy => hy.ne'))
  apply (hsqrt.mul ((radialK_C2 nu).comp_contDiffOn hlog)).congr
  intro y hy
  simp only [physicalK,radialK,Real.exp_log (mul_pos ha hy)]

private theorem scaledMoment_hasDerivAt (k : ℕ) (nu : ℂ) {a y : ℝ}
    (ha : 0<a) (hy : 0<y) :
    HasDerivAt (fun t : ℝ => qMoment k nu (a*t))
      ((a : ℂ)*qMoment (k+1) nu (a*y)) y := by
  convert (qMoment_hasDerivAt k nu (mul_pos ha hy)).comp y
    ((hasDerivAt_id y).const_mul a) using 1 <;>
    simp only [Function.comp_def,Complex.real_smul,mul_comm]

/-- Literal physical first derivative from the actual K integral. -/
theorem physicalK_hasDerivAt (nu : ℂ) {a y : ℝ} (ha : 0<a) (hy : 0<y) :
    HasDerivAt (physicalK nu a) (physicalKFirst nu a y) y := by
  have h := (heightPower_hasDerivAt (1/2) hy).mul (scaledMoment_hasDerivAt 0 nu ha hy)
  convert h using 1 <;>
    simp only [physicalK,physicalKFirst,heightPower,Real.sqrt_eq_rpow,qMoment_zero] <;>
    norm_num <;> ring

/-- Differentiate the explicit first jet using the next genuine moments. -/
theorem physicalKFirst_hasDerivAt (nu : ℂ) {a y : ℝ} (ha : 0<a) (hy : 0<y) :
    HasDerivAt (physicalKFirst nu a) (physicalKSecond nu a y) y := by
  have hA := ((heightPower_hasDerivAt (-1/2) hy).mul
    (scaledMoment_hasDerivAt 0 nu ha hy)).const_mul (1/2 : ℂ)
  have hB := ((heightPower_hasDerivAt (1/2) hy).mul
    (scaledMoment_hasDerivAt 1 nu ha hy)).const_mul (a : ℂ)
  convert hA.add hB using 1 <;>
    dsimp [physicalKFirst,physicalKSecond] <;> norm_num <;> ring

/-- Strong derivative of the actual derivative, rather than a supplied
formal second-jet expression. -/
theorem physicalK_second_hasDerivAt (nu : ℂ) {a y : ℝ} (ha : 0<a) (hy : 0<y) :
    HasDerivAt (deriv (physicalK nu a)) (physicalKSecond nu a y) y := by
  apply (physicalKFirst_hasDerivAt nu ha hy).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
  exact (physicalK_hasDerivAt nu ha ht).deriv

private theorem heightPower_half_shift_one {y : ℝ} (hy : 0<y) :
    (y : ℂ)*heightPower (-1/2) y=heightPower (1/2) y := by
  have hr : y*y^(-1/2 : ℝ)=y^(1/2 : ℝ) := by
    rw [← Real.rpow_one y,← Real.rpow_add hy]
    norm_num
  dsimp [heightPower]
  exact_mod_cast hr

private theorem heightPower_half_shift_two {y : ℝ} (hy : 0<y) :
    (y : ℂ)^2*heightPower (-3/2) y=heightPower (1/2) y := by
  have hr : y^2*y^(-3/2 : ℝ)=y^(1/2 : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hy]
    norm_num
  dsimp [heightPower]
  exact_mod_cast hr

/-- Actual physical square-root conjugation, with the full y^2 factor.
All orders are complex; in particular real, imaginary and zero orders. -/
theorem physicalK_scaled_equation (nu : ℂ) {a y : ℝ} (ha : 0<a) (hy : 0<y) :
    -(y : ℂ)^2*(deriv (deriv (physicalK nu a)) y-(a : ℂ)^2*physicalK nu a y)=
      (1/4-nu^2)*physicalK nu a y := by
  rw [(physicalK_second_hasDerivAt nu ha hy).deriv]
  have hK := complexOrderK_qMoment_ODE nu (mul_pos ha hy)
  rw [Complex.ofReal_mul] at hK
  have hs1 := heightPower_half_shift_one hy
  have hs2 := heightPower_half_shift_two hy
  simp only [physicalKSecond,physicalK,Real.sqrt_eq_rpow,← heightPower,qMoment_zero] at *
  linear_combination -heightPower (1/2) y*hK+
    (1/4 : ℂ)*complexOrderK nu (a*y)*hs2-
    ((a : ℂ)*(y : ℂ))*qMoment 1 nu (a*y)*hs1

/-- Physical ODE in its unscaled form. -/
theorem physicalK_equation (nu : ℂ) {a y : ℝ} (ha : 0<a) (hy : 0<y) :
    -deriv (deriv (physicalK nu a)) y+(a : ℂ)^2*physicalK nu a y=
      ((1/4-nu^2)/(y : ℂ)^2)*physicalK nu a y := by
  have h := physicalK_scaled_equation nu ha hy
  have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  field_simp [hyC]
  linear_combination h

/-- When a real spectral parameter determines nu^2, the actual physical
reference solves that REAL-parameter equation without an order restriction. -/
theorem physicalK_real_parameter_equation (nu : ℂ) {a y lambda : ℝ}
    (ha : 0<a) (hy : 0<y) (horder : nu^2=((1/4-lambda : ℝ) : ℂ)) :
    -deriv (deriv (physicalK nu a)) y+(a : ℂ)^2*physicalK nu a y=
      ((lambda : ℂ)/(y : ℂ)^2)*physicalK nu a y := by
  have h := physicalK_equation nu ha hy
  rw [horder] at h
  push_cast at h
  convert h using 1 <;> ring

end
end ImbalancedChen.Part3.ActualPhysicalKJets20261026b


