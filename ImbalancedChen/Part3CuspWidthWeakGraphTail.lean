import ImbalancedChen.Part3CuspGeneralWeakGraphClosure

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual cusp width is retained in the general weak graph and its
sharp tail estimate. The genuine weak equation gives the unit-coordinate
derivative wD; the already constructed graph approximation is transported
back by a continuous derivative rescaling. Actual classical pairs are
rescaled before closure, so membership in the width-w graph is proved.
The resulting constant is w²/(4π²Y²), with no width or graph premise hidden
inside a coefficient assumption.
-/
namespace ImbalancedChen.Part3.CuspWidthWeakGraphTail20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z ClosedHorizontalCuspTail20261026a
open CuspPhysicalWeakTailModes20261026b CuspGeneralWeakGraphClosure20261026b

attribute [local instance] Measure.Subtype.measureSpace

/-- The true physical derivative in unit coordinates is w times D.
The representative identity is transported from raw dy to dy/y² using
the proved positive-tail measure comparison. -/
theorem weak_physical_scale_derivative {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d) :
    HasWeakPhysicalTailDerivative 1 a u ((w : ℂ) • d) := by
  have hs : ∀ᵐ z ∂functionMeasure a, ((w : ℂ) • d) z = (w : ℂ) * d z := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (Measure.absolutelyContinuous_of_le_smul
        (functionMeasure_le_derivativeMeasure ha)).ae_eq (Lp.coeFn_smul (w : ℂ) d)
  intro φ ψ hφ hd β hβ hc hsupport
  calc
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 *
        ((1 : ℂ) * ((w : ℂ) • d) z) ∂functionMeasure a) =
        ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * d z)
          ∂functionMeasure a := by
      apply integral_congr_ae
      filter_upwards [hs] with z hz
      simp only [one_mul, hz]
    _ = -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * u z
        ∂functionMeasure a) := hweak φ ψ hφ hd β hβ hc hsupport

/-- A genuine classical pair can be re-expressed at any nonzero physical
width. Its function is unchanged and its physical derivative is divided
by the width. -/
def unscaleClassicalPair {w a : ℝ} (hw : w ≠ 0) (P : ClassicalPair 1 a) :
    ClassicalPair w a where
  function := P.function
  derivative := fun z => (w : ℂ)⁻¹ * P.derivative z
  continuous_function := P.continuous_function
  continuous_derivative := continuous_const.mul P.continuous_derivative
  hasDeriv := fun y hy t => by
    have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
    convert P.hasDeriv y hy t using 1 <;> simp [mul_assoc, hwc]
  mean_zero := P.mean_zero
  function_memLp := P.function_memLp
  derivative_memLp := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      P.derivative_memLp.const_smul ((w : ℂ)⁻¹)

theorem unscaleClassicalPair_coordinates {w a : ℝ} (hw : w ≠ 0)
    (P : ClassicalPair 1 a) :
    (unscaleClassicalPair hw P).coordinates =
      (P.coordinates.1, (w : ℂ)⁻¹ • P.coordinates.2) := by
  apply Prod.ext
  · rfl
  · apply Lp.ext
    filter_upwards [(unscaleClassicalPair hw P).derivative_memLp.coeFn_toLp,
      Lp.coeFn_smul ((w : ℂ)⁻¹) P.coordinates.2,
      P.derivative_memLp.coeFn_toLp] with z hleft hright hP
    change (unscaleClassicalPair hw P).coordinates.2 z =
      ((w : ℂ)⁻¹ • P.coordinates.2) z
    rw [hright, Pi.smul_apply, smul_eq_mul, hP]
    exact hleft

/-- Continuous rescaling maps the closure of actual unit-coordinate
classical pairs into the closure of actual width-w classical pairs. -/
theorem width_graph_of_unit_scaled_graph {w a : ℝ} (hw : w ≠ 0)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (h : (u, (w : ℂ) • d) ∈ closedHorizontalGraph 1 a) :
    (u, d) ∈ closedHorizontalGraph w a := by
  let T : FunctionL2 a × DerivativeL2 a → FunctionL2 a × DerivativeL2 a :=
    fun p => (p.1, (w : ℂ)⁻¹ • p.2)
  have hT : Continuous T := continuous_fst.prodMk (continuous_const.smul continuous_snd)
  have hmap : MapsTo T (classicalHorizontalGraph 1 a) (classicalHorizontalGraph w a) := by
    rintro p ⟨P, rfl⟩
    exact ⟨unscaleClassicalPair hw P, unscaleClassicalPair_coordinates hw P⟩
  have ht := map_mem_closure hT h hmap
  have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
  simpa only [T, smul_smul, inv_mul_cancel₀ hwc, one_smul] using ht

/-- Full general-height physical weak graph inclusion at the literal
positive cusp width, with actual horizontal zero mean. -/
theorem width_weak_physical_pair_mem_closed_graph {w a : ℝ} (hw : 0 < w) (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (u, d) ∈ closedHorizontalGraph w a :=
  width_graph_of_unit_scaled_graph hw.ne'
    (weak_physical_pair_mem_closed_graph ha (weak_physical_scale_derivative ha hweak) hmean)

/-- Sharp physical weak cusp tail with the actual width factor retained. -/
theorem width_weak_physical_pair_sharp_tail {w a Y : ℝ}
    (hw : 0 < w) (ha : 0 < a) (hY : 0 < Y) (haY : a ≤ Y)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    ‖tailRestriction a Y haY u‖^2 ≤
      (w^2 / (4 * Real.pi^2 * Y^2)) * ‖d‖^2 :=
  closed_horizontal_tail_bound hw hY haY
    (width_weak_physical_pair_mem_closed_graph hw ha hweak hmean)

end
end ImbalancedChen.Part3.CuspWidthWeakGraphTail20261026b
