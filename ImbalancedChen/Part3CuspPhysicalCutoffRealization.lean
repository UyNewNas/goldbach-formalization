import ImbalancedChen.Part3CuspPhysicalFourierProjectionIdentification

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The compact-height approximants in the two PHYSICAL graph norms have the
same native weighted-cylinder realizations as the height-localized
original weak pair. This joins actual restricted Lp representatives,
zero extension, the raw-to-weighted positive-tail embedding and the
native height coefficient localization. It does not assume that a sharp
height indicator is a smooth distributional test.
-/
namespace ImbalancedChen.Part3.CuspPhysicalCutoffRealization20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open CuspPhysicalWeakTailModes20261026b CuspWeakCylinderFourierModes20261026b
open CuspPhysicalHeightExhaustion20261026b CuspHeightCutoffFourierModes20261026b

attribute [local instance] Measure.Subtype.measureSpace

/-- Actual value zero extension commutes with restriction-space
indicators. The AE restriction implication is used only on the tail. -/
theorem tailValue_indicator (a : ℝ) (u : FunctionL2 a)
    (E : Set CuspCylinder) (hE : MeasurableSet E) :
    tailValue a (indicatorVector E hE u) =
      indicatorVector E hE (tailValue a u) := by
  have hu : ∀ᵐ z ∂cylinderMeasure, z ∈ strictCylinderTail a →
      indicatorVector E hE u z = E.indicator u z :=
    (ae_restrict_iff' (strictCylinderTail_measurable a)).mp (indicatorVector_ae E hE u)
  apply Lp.ext
  filter_upwards [tailValue_ae a (indicatorVector E hE u),
    indicatorVector_ae E hE (tailValue a u), tailValue_ae a u, hu]
      with z hleft hright hvalue hcut
  rw [hleft, hright]
  by_cases ht : z ∈ strictCylinderTail a
  · by_cases he : z ∈ E <;> simp [ht, he, hcut ht, hvalue]
  · by_cases he : z ∈ E <;> simp [ht, he, hvalue]

/-- The same identity for the raw-dy derivative uses the proved a⁻²
measure domination to move its restricted AE identity into dy/y². -/
theorem tailDerivative_indicator {a : ℝ} (ha : 0 < a) (d : DerivativeL2 a)
    (E : Set CuspCylinder) (hE : MeasurableSet E) :
    tailDerivative a ha (indicatorVector E hE d) =
      indicatorVector E hE (tailDerivative a ha d) := by
  have hd : ∀ᵐ z ∂functionMeasure a,
      indicatorVector E hE d z = E.indicator d z :=
    (Measure.absolutelyContinuous_of_le_smul
      (functionMeasure_le_derivativeMeasure ha)).ae_eq (indicatorVector_ae E hE d)
  have hd' : ∀ᵐ z ∂cylinderMeasure, z ∈ strictCylinderTail a →
      indicatorVector E hE d z = E.indicator d z :=
    (ae_restrict_iff' (strictCylinderTail_measurable a)).mp hd
  apply Lp.ext
  filter_upwards [tailDerivative_ae a ha (indicatorVector E hE d),
    indicatorVector_ae E hE (tailDerivative a ha d), tailDerivative_ae a ha d, hd']
      with z hleft hright hvalue hcut
  rw [hleft, hright]
  by_cases ht : z ∈ strictCylinderTail a
  · by_cases he : z ∈ E <;> simp [ht, he, hcut ht, hvalue]
  · by_cases he : z ∈ E <;> simp [ht, he, hvalue]

theorem physicalHeightCutoff_value_realization (a : ℝ) (n : ℕ)
    (p : FunctionL2 a × DerivativeL2 a) :
    tailValue a (physicalHeightCutoff a n p).1 =
      heightLocalizedCylinder (heightBand a n) (heightBand_measurable a n) (tailValue a p.1) :=
  tailValue_indicator a p.1 (cylinderHeightBand a n) (cylinderHeightBand_measurable a n)

theorem physicalHeightCutoff_derivative_realization {a : ℝ} (ha : 0 < a) (n : ℕ)
    (p : FunctionL2 a × DerivativeL2 a) :
    tailDerivative a ha (physicalHeightCutoff a n p).2 =
      heightLocalizedCylinder (heightBand a n) (heightBand_measurable a n)
        (tailDerivative a ha p.2) :=
  tailDerivative_indicator ha p.2 (cylinderHeightBand a n) (cylinderHeightBand_measurable a n)

/-- Physical compact-height cutoff pairs retain the coefficient equation
derived from genuine weak tensor testing of the original pair. -/
theorem physicalHeightCutoff_coefficient_equation {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative 1 a u d) (m : ℕ) (k : ℤ) :
    cylinderCoefficient k (tailDerivative a ha (physicalHeightCutoff a m (u, d)).2) =
      modeFrequency k •
        cylinderCoefficient k (tailValue a (physicalHeightCutoff a m (u, d)).1) := by
  rw [physicalHeightCutoff_value_realization, physicalHeightCutoff_derivative_realization]
  apply localized_weak_coefficient_relation
  simpa only [Complex.ofReal_one, one_smul] using physical_tail_native_weak ha hweak

end
end ImbalancedChen.Part3.CuspPhysicalCutoffRealization20261026b
