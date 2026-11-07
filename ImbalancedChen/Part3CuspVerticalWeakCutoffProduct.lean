import ImbalancedChen.Part3CuspVerticalHeightCommutator
import ImbalancedChen.Part3CuspRawWeakDerivativeBridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The genuine RAW dy vertical distribution equation on the open tail
y>a, with compact tests supported strictly inside that open tail.
All test pairings are proved integrable from mixed L2 regularity.
Actual smooth height localization has the literal weak derivative
chi*d_y + chi'*u. The second term is the independently constructed raw
L2 commutator, not an assumed product-rule or regularity conclusion.
-/
namespace ImbalancedChen.Part3.CuspVerticalWeakCutoffProduct20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a CuspPhysicalWeakTailModes20261026b
open CuspSmoothHeightWeakLocalization20261026b CuspVerticalHeightCommutator20261026b
open CuspRawWeakDerivativeBridge20261026b
attribute [local instance] Measure.Subtype.measureSpace

def HasRawWeakPhysicalVerticalDerivative (a : ℝ) (u : FunctionL2 a) (d : DerivativeL2 a) : Prop :=
  ∀ φ : C(UnitAddCircle, ℂ), ∀ β : ℝ → ℝ,
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a) =
      -(∫ z : CuspCylinder, (deriv β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a)

theorem vertical_raw_test_integrabilities {a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (φ : C(UnitAddCircle, ℂ))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi a) :
    Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1 * d z)
      (derivativeMeasure a) ∧
    Integrable (fun z : CuspCylinder => (deriv β (z.2 : ℝ) : ℂ) * φ z.1 * u z)
      (derivativeMeasure a) := by
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  have hd : MemLp (d : CuspCylinder → ℂ) 2 (functionMeasure a) :=
    (Lp.memLp d).of_measure_le_smul (by simp) (functionMeasure_le_derivativeMeasure ha)
  exact ⟨raw_tensor_integrable a d hd φ hβ.continuous hc hpos,
    raw_tensor_integrable a u (Lp.memLp u) φ
      (contDiff_infty_iff_deriv.mp hβ).2.continuous hc.deriv
      (tsupport_deriv_subset.trans hpos)⟩

theorem derivativeMeasure_absolutelyContinuous_functionMeasure (a : ℝ) :
    derivativeMeasure a ≪ functionMeasure a := by
  rw [physical_functionMeasure_density]
  apply withDensity_absolutelyContinuous'
    ((heightDensity_continuous.measurable.comp measurable_snd).coe_nnreal_ennreal.aemeasurable)
  exact Eventually.of_forall fun z => ENNReal.coe_ne_zero.mpr (heightDensity_pos z.2).ne'

def verticalLocalizedValue {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (u : FunctionL2 a) :
    FunctionL2 a := heightMultiplier (functionMeasure a) (physicalVerticalCutoff a R ha hR) u

def verticalLocalizedDerivative {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (u : FunctionL2 a) (d : DerivativeL2 a) : DerivativeL2 a :=
  heightMultiplier (derivativeMeasure a) (physicalVerticalCutoff a R ha hR) d +
    commutatorVector ha hR u

theorem verticalLocalizedDerivative_ae {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (u : FunctionL2 a) (d : DerivativeL2 a) :
    (verticalLocalizedDerivative ha hR u d : CuspCylinder → ℂ) =ᵐ[derivativeMeasure a]
      (fun z => (verticalHeightCutoff a R (z.2 : ℝ) : ℂ) * d z +
        (deriv (verticalHeightCutoff a R) (z.2 : ℝ) : ℂ) * u z) := by
  filter_upwards [Lp.coeFn_add
    (heightMultiplier (derivativeMeasure a) (physicalVerticalCutoff a R ha hR) d)
    (commutatorVector ha hR u),
    heightMultiplier_ae (derivativeMeasure a) (physicalVerticalCutoff a R ha hR) d,
    (commutator_memLp ha hR u).coeFn_toLp] with z hsum hd hc
  simp only [verticalLocalizedDerivative, hsum, Pi.add_apply, hd, hc,
    heightMultiplierFunction, physicalVerticalCutoff, commutatorFunction]

/-- Actual vertical product rule at distribution level, with both L2
coordinates and the commutator represented in their physical measures. -/
theorem verticalLocalized_preserves_weak_derivative {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasRawWeakPhysicalVerticalDerivative a u d) :
    HasRawWeakPhysicalVerticalDerivative a (verticalLocalizedValue ha hR u)
      (verticalLocalizedDerivative ha hR u d) := by
  intro φ β hβ hβc hβs
  let χ := verticalHeightCutoff a R
  have hχ : ContDiff ℝ ∞ χ := verticalHeightCutoff_smooth a R
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hβs hy)
  have htest := hweak φ (fun y => β y * χ y) (hβ.mul hχ) hβc.mul_right
    (tsupport_mul_subset_left.trans hβs)
  have hprod (y : ℝ) : deriv (fun t => β t * χ t) y =
      deriv β y * χ y + β y * deriv χ y :=
    (((hβ.differentiable (by simp) y).hasDerivAt).mul
      (hχ.differentiable (by simp) y).hasDerivAt).deriv
  let A : CuspCylinder → ℂ := fun z => ((β (z.2 : ℝ) * χ (z.2 : ℝ) : ℝ) : ℂ) * φ z.1 * d z
  let B : CuspCylinder → ℂ := fun z => ((deriv β (z.2 : ℝ) * χ (z.2 : ℝ) : ℝ) : ℂ) * φ z.1 * u z
  let C : CuspCylinder → ℂ := fun z => ((β (z.2 : ℝ) * deriv χ (z.2 : ℝ) : ℝ) : ℂ) * φ z.1 * u z
  have hB : Integrable B (derivativeMeasure a) :=
    raw_tensor_integrable a u (Lp.memLp u) φ
      ((contDiff_infty_iff_deriv.mp hβ).2.continuous.mul hχ.continuous)
      hβc.deriv.mul_right (tsupport_mul_subset_left.trans (tsupport_deriv_subset.trans hpos))
  have hC : Integrable C (derivativeMeasure a) :=
    raw_tensor_integrable a u (Lp.memLp u) φ
      (hβ.continuous.mul (contDiff_infty_iff_deriv.mp hχ).2.continuous)
      hβc.mul_right (tsupport_mul_subset_left.trans hpos)
  have ht : (∫ z, A z ∂derivativeMeasure a) =
      -((∫ z, B z ∂derivativeMeasure a) + ∫ z, C z ∂derivativeMeasure a) := by
    change (∫ z, A z ∂derivativeMeasure a) = _ at htest ⊢
    rw [← integral_add hB hC]
    convert htest using 1
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      simp only [A, B, C, hprod, Complex.ofReal_add, Complex.ofReal_mul, Pi.add_apply]
      ring
  have hu := (derivativeMeasure_absolutelyContinuous_functionMeasure a).ae_eq
    (heightMultiplier_ae (functionMeasure a) (physicalVerticalCutoff a R ha hR) u)
  have hleft : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 *
      verticalLocalizedDerivative ha hR u d z ∂derivativeMeasure a) =
      (∫ z, A z ∂derivativeMeasure a) + ∫ z, C z ∂derivativeMeasure a := by
    have hA : Integrable A (derivativeMeasure a) :=
      (vertical_raw_test_integrabilities ha u d φ (hβ.mul hχ) hβc.mul_right
        (tsupport_mul_subset_left.trans hβs)).1
    rw [← integral_add hA hC]
    apply integral_congr_ae
    filter_upwards [verticalLocalizedDerivative_ae ha hR u d] with z hz
    rw [hz]
    simp only [A, C, Complex.ofReal_mul, Pi.add_apply, χ]
    ring
  have hright : (∫ z : CuspCylinder, (deriv β (z.2 : ℝ) : ℂ) * φ z.1 *
      verticalLocalizedValue ha hR u z ∂derivativeMeasure a) =
      ∫ z, B z ∂derivativeMeasure a := by
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    rw [show verticalLocalizedValue ha hR u z =
      (χ (z.2 : ℝ) : ℂ) * u z from hz]
    simp only [B, Complex.ofReal_mul]
    ring
  rw [hleft, hright]
  linear_combination ht

end
end ImbalancedChen.Part3.CuspVerticalWeakCutoffProduct20261026b
