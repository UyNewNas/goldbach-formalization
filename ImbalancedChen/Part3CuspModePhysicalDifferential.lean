import ImbalancedChen.Part3CuspModeNativeClosedForm
import ImbalancedChen.Part3ActualRadialFriedrichsSmoothExtension
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual dy/y^2 physical differential expression is computed on the
sqrt(y) Liouville lift of every genuine smooth compact radial test.
Its L2 representative is proved equal to the inverse actual height
unitary applied to (-d²/dr²+exp(2r)+1/4)T. Consequently the previously
constructed native physical Friedrichs graph extends the literal physical
second derivative operator. Neither differential identity nor desired
graph inclusion is an input. No held Liouville source is imported.
-/

namespace ImbalancedChen.Part3.CuspModePhysicalDifferential20261026b
noncomputable section
open Set Filter MeasureTheory
open CuspCylinderMeasure20261024z
open CuspModePhysicalCoreForm20261026a
open CuspModeNativeClosedForm20261026a
open WeightedHeightNativeUnitary20261026a
open WeightedHeightLogMeasure20261026a
open RadialSchrodingerL2Form20261025a

/-- Literal hyperbolic separated expression on physical height profiles. -/
def physicalDifferential (a : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  -(y : ℂ) ^ 2 * deriv (deriv f) y + ((a * y : ℝ) : ℂ) ^ 2 * f y

theorem physicalLift_second_deriv (a : ℝ) (ha : 0 < a)
    (T : RadialTest) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (physicalLift a T.function)) y =
      (Real.sqrt y : ℂ)⁻¹ * (y : ℂ)⁻¹ *
        (deriv (deriv T.function) (Real.log (a * y)) -
          (1 / 4 : ℂ) * T.function (Real.log (a * y))) := by
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hsq : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  have hl : HasDerivAt (fun z : ℝ => Real.log (a * z)) y⁻¹ y := by
    convert (Real.hasDerivAt_log (mul_pos ha hy).ne').comp y
      ((hasDerivAt_id y).const_mul a) using 1
    simp only [mul_one]
    field_simp [ha.ne', hy.ne']
  have hf : DifferentiableAt ℝ T.function (Real.log (a * y)) :=
    T.smooth.differentiable (by simp) _
  have hd : DifferentiableAt ℝ (deriv T.function) (Real.log (a * y)) :=
    (contDiff_infty_iff_deriv.mp T.smooth).2.differentiable (by simp) _
  have h := ((Real.hasDerivAt_sqrt hy.ne').ofReal_comp.inv hs).mul
    ((hd.hasDerivAt.scomp y hl).add
      ((hf.hasDerivAt.scomp y hl).const_mul (1 / 2 : ℂ)))
  have heq : deriv (physicalLift a T.function) =ᶠ[𝓝 y]
      (fun z : ℝ => (Real.sqrt z : ℂ)⁻¹ *
        (deriv T.function (Real.log (a * z)) +
          (1 / 2 : ℂ) * T.function (Real.log (a * z)))) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact (physicalLift_hasDerivAt ha hz T.function
      (T.smooth.differentiable (by simp) _)).deriv
  have hh := (h.congr_of_eventuallyEq heq).deriv
  rw [hh]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← hsq]
  field_simp [hs] <;> ring

/-- Pointwise physical Liouville identity including the actual quarter.
The differential expression is literally -y²f''+(ay)²f. -/
theorem physicalDifferential_lift (a : ℝ) (ha : 0 < a)
    (T : RadialTest) {y : ℝ} (hy : 0 < y) :
    physicalDifferential a (physicalLift a T.function) y =
      physicalLift a (fun r => radialOperatorFunction T r +
        (1 / 4 : ℂ) * T.function r) y := by
  rw [physicalDifferential, physicalLift_second_deriv a ha T hy]
  simp only [physicalLift, radialOperatorFunction_literal]
  have hs : (Real.sqrt y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hsq : (Real.sqrt y : ℂ) ^ 2 = (y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  have hexp : Real.exp (2 * Real.log (a * y)) = (a * y) ^ 2 := by
    rw [show 2 * Real.log (a * y) = Real.log (a * y) + Real.log (a * y) by ring,
      Real.exp_add, Real.exp_log (mul_pos ha hy), pow_two]
  rw [hexp]
  push_cast
  rw [← hsq]
  field_simp [hs] <;> ring

theorem physicalDifferential_core_inverse_unitary_ae (a : ℝ) (ha : 0 < a)
    (T : RadialTest) :
    (weightedHeightUnitary a ha).symm
        (radialOperatorL2 T + (1 / 4 : ℂ) • radialCoreL2 T) =ᵐ[heightMeasure]
      (fun y : PositiveHeight => physicalDifferential a (physicalLift a T.function) y) := by
  have hrep : (radialOperatorL2 T + (1 / 4 : ℂ) • radialCoreL2 T : RadialL2) =ᵐ[volume]
      (fun r => radialOperatorFunction T r + (1 / 4 : ℂ) * T.function r) := by
    filter_upwards [Lp.coeFn_add (radialOperatorL2 T) ((1 / 4 : ℂ) • radialCoreL2 T),
      Lp.coeFn_smul (1 / 4 : ℂ) (radialCoreL2 T),
      (radialOperatorFunction_memLp T).coeFn_toLp, T.function_memLp.coeFn_toLp]
      with r hadd hsmul hA hT
    simp only [hadd, hsmul, Pi.smul_apply, smul_eq_mul]
    rw [hA, hT]
  have hrepY := (scaledHeightEquiv_symm_quasiMeasurePreserving a ha).ae hrep
  filter_upwards [weightedHeightUnitary_inverse_ae a ha
      (radialOperatorL2 T + (1 / 4 : ℂ) • radialCoreL2 T), hrepY] with y hv hr
  rw [hv, hr]
  exact (physicalDifferential_lift a ha T y.property).symm

theorem physicalDifferential_core_memLp (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    MemLp (fun y : PositiveHeight => physicalDifferential a (physicalLift a T.function) y)
      2 heightMeasure :=
  (Lp.memLp ((weightedHeightUnitary a ha).symm
    (radialOperatorL2 T + (1 / 4 : ℂ) • radialCoreL2 T))).congr
      (physicalDifferential_core_inverse_unitary_ae a ha T)

def physicalDifferentialCoreL2 (a : ℝ) (ha : 0 < a) (T : RadialTest) :
    PhysicalHeightL2 :=
  (physicalDifferential_core_memLp a ha T).toLp
    (fun y : PositiveHeight => physicalDifferential a (physicalLift a T.function) y)

theorem physicalDifferentialCoreL2_eq_inverse_unitary (a : ℝ) (ha : 0 < a)
    (T : RadialTest) :
    physicalDifferentialCoreL2 a ha T = (weightedHeightUnitary a ha).symm
      (radialOperatorL2 T + (1 / 4 : ℂ) • radialCoreL2 T) := by
  apply Lp.ext
  exact (physicalDifferential_core_memLp a ha T).coeFn_toLp.trans
    (physicalDifferential_core_inverse_unitary_ae a ha T).symm

/-- The genuine physical Friedrichs operator extends the literal
hyperbolic separated second derivative on every compact radial-image test. -/
theorem actualModeFriedrichs_extends_physicalDifferential (a : ℝ) (ha : 0 < a)
    (T : RadialTest) :
    (physicalCoreL2 a ha T, physicalDifferentialCoreL2 a ha T) ∈
      (actualModeFriedrichs a ha).graph := by
  apply (actualModeFriedrichs_graph_conjugacy a ha _ _).mpr
  rw [physicalDifferentialCoreL2_eq_inverse_unitary,
    ← inverse_unitary_core_eq a ha T]
  simpa using actualRadialFriedrichs_extends_logSchrodinger T

end
end ImbalancedChen.Part3.CuspModePhysicalDifferential20261026b
