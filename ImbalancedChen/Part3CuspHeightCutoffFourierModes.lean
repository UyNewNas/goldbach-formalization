import ImbalancedChen.Part3CuspPhysicalHeightExhaustion
import ImbalancedChen.Part3ActualCylinderFiniteFourierProjection

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Measurable height localization commutes with the actual cylinder Fourier
coefficients. This uses actual product-measure AE slicing, including a
single AE height set for all integer coefficients, rather than a formal
pointwise representative identity. Consequently the coefficient equation
derived from weak tensor tests survives compact height indicators.
No smoothness of the indicators and no classical weak equation for the
cutoff itself is postulated.
-/
namespace ImbalancedChen.Part3.CuspHeightCutoffFourierModes20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open CuspWeakCylinderFourierModes20261026b
open CuspPhysicalHeightExhaustion20261026b

attribute [local instance] Measure.Subtype.measureSpace

def heightLocalizedCylinder (K : Set PositiveHeight) (hK : MeasurableSet K)
    (F : CylinderL2) : CylinderL2 :=
  indicatorVector (univ ×ˢ K) (MeasurableSet.univ.prod hK) F

/-- The product AE identity is sliced after swapping the product measure.
Every integer coefficient is then computed on the SAME AE height set. -/
theorem heightLocalizedCylinder_all_coefficients_ae (K : Set PositiveHeight)
    (hK : MeasurableSet K) (F : CylinderL2) :
    ∀ᵐ y ∂heightMeasure, ∀ n : ℤ,
      sliceCoefficient n (heightLocalizedCylinder K hK F) y =
        K.indicator (sliceCoefficient n F) y := by
  have hp := indicatorVector_ae (univ ×ˢ K) (MeasurableSet.univ.prod hK) F
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      heightLocalizedCylinder K hK F (p.2, p.1) =
        (univ ×ˢ K).indicator F (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae hp
  filter_upwards [ae_ae_of_ae_prod hswap] with y hy
  intro n
  have hcoeff := congrFun (AddCircle.fourierCoeff_congr_ae hy) n
  by_cases hyK : y ∈ K
  · simpa [sliceCoefficient, hyK, AddCircle.fourierCoeff] using hcoeff
  · simpa [sliceCoefficient, hyK, AddCircle.fourierCoeff] using hcoeff

theorem heightLocalizedCylinder_coefficient (K : Set PositiveHeight)
    (hK : MeasurableSet K) (F : CylinderL2) (n : ℤ) :
    cylinderCoefficient n (heightLocalizedCylinder K hK F) =
      indicatorVector K hK (cylinderCoefficient n F) := by
  apply Lp.ext
  filter_upwards [cylinderCoefficient_ae n (heightLocalizedCylinder K hK F),
    heightLocalizedCylinder_all_coefficients_ae K hK F,
    indicatorVector_ae K hK (cylinderCoefficient n F),
    cylinderCoefficient_ae n F] with y hc hl hi hf
  rw [hc, hl n, hi]
  by_cases hy : y ∈ K <;> simp [hy, hf]

theorem indicatorVector_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : Set α) (hK : MeasurableSet K) :
    indicatorVector K hK (0 : Lp ℂ 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [indicatorVector_ae K hK (0 : Lp ℂ 2 μ),
    Lp.coeFn_zero ℂ 2 μ] with y hi hz
  by_cases hy : y ∈ K <;> simp [hi, hy, hz]

theorem indicatorVector_smul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : Set α) (hK : MeasurableSet K) (c : ℂ) (u : Lp ℂ 2 μ) :
    indicatorVector K hK (c • u) = c • indicatorVector K hK u := by
  apply Lp.ext
  filter_upwards [indicatorVector_ae K hK (c • u),
    indicatorVector_ae K hK u, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (indicatorVector K hK u)] with y hleft hright hu hres
  by_cases hy : y ∈ K <;>
    simp [hleft, hres, hright, hu, hy]

/-- Native zero mean survives arbitrary measurable height localization. -/
theorem heightLocalizedCylinder_zero_mean (K : Set PositiveHeight)
    (hK : MeasurableSet K) {F : CylinderL2} (hF : F ∈ zeroMeanCylinder) :
    heightLocalizedCylinder K hK F ∈ zeroMeanCylinder := by
  change cylinderCoefficient 0 (heightLocalizedCylinder K hK F) = 0
  rw [heightLocalizedCylinder_coefficient, show cylinderCoefficient 0 F = 0 from hF,
    indicatorVector_zero]

/-- This is the exact horizontal equation needed for finite-mode graph
reconstruction after compact-height localization. -/
theorem localized_weak_coefficient_relation (K : Set PositiveHeight)
    (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) (n : ℤ) :
    cylinderCoefficient n (heightLocalizedCylinder K hK G) =
      modeFrequency n • cylinderCoefficient n (heightLocalizedCylinder K hK F) := by
  rw [heightLocalizedCylinder_coefficient, heightLocalizedCylinder_coefficient,
    weak_cylinder_coefficient hweak n, indicatorVector_smul]

theorem localized_weak_all_modes_ae (K : Set PositiveHeight)
    (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) :
    ∀ᵐ y ∂heightMeasure, ∀ n : ℤ,
      sliceCoefficient n (heightLocalizedCylinder K hK G) y =
        modeFrequency n * sliceCoefficient n (heightLocalizedCylinder K hK F) y := by
  filter_upwards [heightLocalizedCylinder_all_coefficients_ae K hK G,
    heightLocalizedCylinder_all_coefficients_ae K hK F,
    weak_cylinder_all_modes_ae hweak] with y hG hF heq
  intro n
  rw [hG n, hF n]
  by_cases hy : y ∈ K <;> simp [hy, heq n]

end
end ImbalancedChen.Part3.CuspHeightCutoffFourierModes20261026b
