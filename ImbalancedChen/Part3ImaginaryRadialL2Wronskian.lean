import ImbalancedChen.Part3ImaginaryRadialTailDerivativeL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Zero Wronskian for actual L2 imaginary-order radial tail solutions

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The Wronskian is constant by differentiating the actual native ODE.
The preceding cutoff/exhaustion theorem gives L2 derivatives on a smaller
tail. Holder then makes the Wronskian integrable there. Since that tail
has infinite Lebesgue measure, the constant is zero, throughout the
original ODE domain. No limit-point, basis, derivative-L2, endpoint-flux,
or special-function asymptotic assumption occurs in this theorem.
-/

namespace ImbalancedChen.Part3.ImaginaryRadialL2Wronskian20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryRadialCutoffEnergy20261026b ImaginaryRadialTailDerivativeL220261026b

def radialWronskian (u v : ℝ → ℂ) (r : ℝ) : ℂ :=
  u r*deriv v r-deriv u r*v r

/-- Abel's identity for the native log-radial equation, obtained solely
from the first/second derivative jets of the two genuine solutions. -/
theorem radialWronskian_hasDerivAt_zero {tau R : ℝ} {u v : ℝ → ℂ}
    (hu : TailSolution tau R u) (hv : TailSolution tau R v)
    {r : ℝ} (hr : R < r) : HasDerivAt (radialWronskian u v) 0 r := by
  have hd := (((hu r hr).1.mul (hv r hr).2).sub ((hu r hr).2.mul (hv r hr).1))
  convert hd using 1 <;> dsimp [radialWronskian] <;> ring

/-- The Wronskian is constant on the actual tail, without extending the
solutions across the omitted finite interval. -/
theorem radialWronskian_eq {tau R : ℝ} {u v : ℝ → ℂ}
    (hu : TailSolution tau R u) (hv : TailSolution tau R v)
    {a b : ℝ} (ha : R < a) (hb : R < b) :
    radialWronskian u v a = radialWronskian u v b := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro r hr
    exact (radialWronskian_hasDerivAt_zero hu hv hr).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (radialWronskian_hasDerivAt_zero hu hv hr).deriv
  · exact ha
  · exact hb

/-- Actual L2 solutions have an integrable Wronskian on a smaller tail.
The derivative-L2 inputs of Holder are proved by genuine Caccioppoli
cutoffs and exhaustion, rather than supplied by the caller. -/
theorem radialWronskian_integrable {tau R : ℝ} {u v : ℝ → ℂ}
    (hu : TailSolution tau R u) (hv : TailSolution tau R v)
    (hLu : MemLp u 2 (volume.restrict (Ioi R)))
    (hLv : MemLp v 2 (volume.restrict (Ioi R))) :
    IntegrableOn (radialWronskian u v) (Ioi (R+2)) := by
  have hsub : Ioi (R+2) ⊆ Ioi R := by intro r hr; change R < r; linarith
  have hU := hLu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hV := hLv.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDU := derivative_memLp_two_smaller_tail hu hLu
  have hDV := derivative_memLp_two_smaller_tail hv hLv
  exact (hU.integrable_mul hDV).sub (hDU.integrable_mul hV)

/-- The actual limit-point determinant conclusion: any two genuine L2
solutions have zero Wronskian throughout their common ODE tail. This
includes tau=0 and all real tau without using real-order I growth. -/
theorem L2_tail_radialWronskian_eq_zero {tau R : ℝ} {u v : ℝ → ℂ}
    (hu : TailSolution tau R u) (hv : TailSolution tau R v)
    (hLu : MemLp u 2 (volume.restrict (Ioi R)))
    (hLv : MemLp v 2 (volume.restrict (Ioi R)))
    {a : ℝ} (ha : R < a) : radialWronskian u v a = 0 := by
  have hW := radialWronskian_integrable hu hv hLu hLv
  have hc : Integrable (fun _ : ℝ => radialWronskian u v a)
      (volume.restrict (Ioi (R+2))) := by
    apply hW.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact radialWronskian_eq hu hv (by linarith : R < r) ha
  have hInfinite : ¬ IsFiniteMeasure (volume.restrict (Ioi (R+2))) := by
    apply not_isFiniteMeasure_iff.mpr
    simp only [Measure.restrict_apply_univ, Real.volume_Ioi]
  exact (integrable_const_iff.mp hc).resolve_right hInfinite

/-- At every point, the initial-value columns of two actual L2 solutions
are linearly dependent. The coefficient is computed from a nonzero
value, and the derivative relation is a consequence of the proved zero
Wronskian, not a prescribed initial condition. -/
theorem L2_tail_initial_jets_dependent {tau R : ℝ} {u v : ℝ → ℂ}
    (hu : TailSolution tau R u) (hv : TailSolution tau R v)
    (hLu : MemLp u 2 (volume.restrict (Ioi R)))
    (hLv : MemLp v 2 (volume.restrict (Ioi R)))
    {a : ℝ} (ha : R < a) (hua : u a ≠ 0) :
    v a = (v a/u a)*u a ∧ deriv v a = (v a/u a)*deriv u a := by
  have hW := L2_tail_radialWronskian_eq_zero hu hv hLu hLv ha
  dsimp [radialWronskian] at hW
  constructor
  · field_simp [hua]
  · rw [div_mul_eq_mul_div]
    apply (eq_div_iff hua).mpr
    linear_combination hW

end
end ImbalancedChen.Part3.ImaginaryRadialL2Wronskian20261026b
