import ImbalancedChen.Part3CuspClassicalRawWeakTesting

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reverse graph inclusion and equality for the literal physical cusp.
For each genuine compact tensor test the raw weak equation is a closed
condition in weighted-value × raw-derivative L², by the actual pairing
continuity already proved. Actual classical pairs satisfy every such
condition, hence their closure does. The actual zero-horizontal-mean
condition is also closed, via the native Fourier zero coefficient of the
isometric value zero extension. The forward inclusion is consumed, not
reproved. This is genuine rawweak+actualAEmean0 iff classical graph closure.
-/
namespace ImbalancedChen.Part3.CuspRawWeakGraphEquality20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a ActualZeroMeanCylinderFourierUnitary20261026a
open CuspPhysicalWeakTailModes20261026b CuspRawWeakDerivativeBridge20261026b
open CuspRawTestPairingContinuity20261026b CuspClassicalRawWeakTesting20261026b
open CuspUpperBandMixedFourierConvergence20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private theorem raw_width_pairing (w a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (d : DerivativeL2 a) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * d z)
      ∂derivativeMeasure a) =
      (w : ℂ) * (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z
        ∂derivativeMeasure a) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

/-- A fixed raw tensor weak equation is closed in the actual two-norm
physical graph space. No convergence of test pairings is a premise. -/
theorem isClosed_raw_test_equation (w a : ℝ) (φ ψ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    IsClosed {p : FunctionL2 a × DerivativeL2 a |
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * p.2 z)
        ∂derivativeMeasure a) =
      -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * p.1 z ∂derivativeMeasure a)} := by
  have hleft : Continuous (fun p : FunctionL2 a × DerivativeL2 a =>
      (w : ℂ) * (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * p.2 z
        ∂derivativeMeasure a)) :=
    continuous_const.mul ((continuous_raw_derivative_pairing a φ β hβ hc hs).comp continuous_snd)
  have hright : Continuous (fun p : FunctionL2 a × DerivativeL2 a =>
      -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * p.1 z ∂derivativeMeasure a)) :=
    ((continuous_raw_value_pairing a ψ β hβ hc hs).comp continuous_fst).neg
  simpa only [raw_width_pairing] using isClosed_eq hleft hright

/-- Every actual classical-graph limit satisfies the genuine raw
distributional equation, with no additional weak-equation premise. -/
theorem closed_graph_raw_weak {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hgraph : (u, d) ∈ closedHorizontalGraph w a) :
    HasRawWeakPhysicalTailDerivative w a u d := by
  intro φ ψ hφ hd β hβ hc hs
  have hclosed := isClosed_raw_test_equation w a φ ψ β hβ.continuous hc hs
  have hclassical : classicalHorizontalGraph w a ⊆
      {p : FunctionL2 a × DerivativeL2 a |
        (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * p.2 z)
          ∂derivativeMeasure a) =
        -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * p.1 z ∂derivativeMeasure a)} := by
    rintro p ⟨P, rfl⟩
    exact classical_coordinates_raw_weak ha P φ ψ hφ hd β hβ hc hs
  exact closure_minimal hclassical hclosed hgraph

/-- The value zero extension is the actual isometric zero extension of
the restricted weighted L² class; hence it is continuous. -/
theorem continuous_tailValue (a : ℝ) : Continuous (fun u : FunctionL2 a => tailValue a u) := by
  change Continuous (restrictedZeroExtension cylinderMeasure (strictCylinderTail a)
    (strictCylinderTail_measurable a))
  exact (restrictedZeroExtension cylinderMeasure (strictCylinderTail a)
    (strictCylinderTail_measurable a)).continuous

theorem isClosed_physical_native_zero_mean (w a : ℝ) :
    IsClosed {p : FunctionL2 a × DerivativeL2 a |
      cylinderCoefficient 0 (tailValue a p.1) = 0} := by
  exact isClosed_eq
    ((cylinderCoefficient 0).continuous.comp ((continuous_tailValue a).comp continuous_fst))
    continuous_const

/-- Necessity of the ORIGINAL raw-AE zero-horizontal-mean condition is
proved from closure, not inserted as an extra condition on graph limits. -/
theorem closed_graph_zero_mean {w a : ℝ}
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hgraph : (u, d) ∈ closedHorizontalGraph w a) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0 := by
  apply (physical_zero_mean_iff_native a u).mpr
  have hclassical : classicalHorizontalGraph w a ⊆
      {p : FunctionL2 a × DerivativeL2 a | cylinderCoefficient 0 (tailValue a p.1) = 0} := by
    rintro p ⟨P, rfl⟩
    exact classical_coordinates_zero_mean P
  exact closure_minimal hclassical (isClosed_physical_native_zero_mean w a) hgraph

def rawWeakZeroMeanGraph (w a : ℝ) : Set (FunctionL2 a × DerivativeL2 a) :=
  {p | HasRawWeakPhysicalTailDerivative w a p.1 p.2 ∧
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, p.1 (x, y) ∂AddCircle.haarAddCircle) = 0}

/-- Exact equality of the actual classical physical graph closure and
the genuine raw distributional mean-zero weak graph. -/
theorem closed_graph_eq_raw_weak_zero_mean {w a : ℝ} (hw : 0 < w) (ha : 0 < a) :
    closedHorizontalGraph w a = rawWeakZeroMeanGraph w a := by
  ext p
  constructor
  · intro hp
    exact ⟨closed_graph_raw_weak ha hp, closed_graph_zero_mean hp⟩
  · rintro ⟨hraw, hmean⟩
    exact raw_weak_physical_pair_mem_closed_graph hw ha hraw hmean

theorem mem_closed_graph_iff_raw_weak_and_zero_mean {w a : ℝ} (hw : 0 < w) (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) :
    (u, d) ∈ closedHorizontalGraph w a ↔
      HasRawWeakPhysicalTailDerivative w a u d ∧
      ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
        (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0 := by
  rw [closed_graph_eq_raw_weak_zero_mean hw ha]
  rfl

end
end ImbalancedChen.Part3.CuspRawWeakGraphEquality20261026b
