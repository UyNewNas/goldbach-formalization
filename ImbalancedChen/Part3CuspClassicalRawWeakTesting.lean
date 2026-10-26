import ImbalancedChen.Part3CuspRawTestPairingContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual classical physical pairs satisfy the genuine raw tensor weak
equation. Periodic integration by parts is proved on the normalized
Haar circle by the fundamental theorem of calculus on [0,1], and actual
Bochner Fubini then integrates the compact height test. Native Lp
coordinate representatives are joined using the actual positive density.
The literal raw-AE horizontal zero mean is also identified with the
native zero coefficient of the value's weighted zero extension.
-/
namespace ImbalancedChen.Part3.CuspClassicalRawWeakTesting20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open CuspPhysicalWeakTailModes20261026b CuspRawWeakDerivativeBridge20261026b
open CuspReciprocalHeightTests20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

theorem derivativeMeasure_ac_functionMeasure (a : ℝ) : derivativeMeasure a ≪ functionMeasure a := by
  rw [functionMeasure_eq_raw_withDensity]
  exact withDensity_absolutelyContinuous'
    (heightDensity_continuous.measurable.comp measurable_snd).coe_nnreal_ennreal.aemeasurable
    (Eventually.of_forall fun z => ENNReal.coe_ne_zero.mpr (heightDensity_pos z.2).ne')

private theorem circle_integral_eq_unit_interval (f : UnitAddCircle → ℂ) :
    (∫ x : UnitAddCircle, f x ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, f (t : UnitAddCircle) := by
  rw [circleHaar_eq_volume]
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1, f (t : UnitAddCircle) := by
      simpa only [zero_add] using (AddCircle.integral_preimage 1 0 f).symm
    _ = _ := (intervalIntegral.integral_of_le zero_le_one).symm

/-- Periodic Green identity on an actual circle slice, derived from the
classical derivative and the actual derivative of the test. -/
theorem classical_circle_test_identity {w a : ℝ} (P : ClassicalPair w a)
    (φ ψ : C(UnitAddCircle, ℂ))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) (y : PositiveHeight) (hy : a < (y : ℝ)) :
    (∫ x : UnitAddCircle, φ x * ((w : ℂ) * P.derivative (x, y)) ∂AddCircle.haarAddCircle) =
      -(∫ x : UnitAddCircle, ψ x * P.function (x, y) ∂AddCircle.haarAddCircle) := by
  have hP := P.continuous_function
  have hD := P.continuous_derivative
  have hφ := φ.continuous
  have hψ := ψ.continuous
  have h1 : Continuous (fun t : ℝ => ψ (t : UnitAddCircle) * P.function ((t : UnitAddCircle), y)) := by
    fun_prop
  have h2 : Continuous (fun t : ℝ => φ (t : UnitAddCircle) *
      ((w : ℂ) * P.derivative ((t : UnitAddCircle), y))) := by fun_prop
  have hd (t : ℝ) : HasDerivAt
      (fun s : ℝ => φ (s : UnitAddCircle) * P.function ((s : UnitAddCircle), y))
      (ψ (t : UnitAddCircle) * P.function ((t : UnitAddCircle), y) +
        φ (t : UnitAddCircle) * ((w : ℂ) * P.derivative ((t : UnitAddCircle), y))) t :=
    (htest t).mul (P.hasDeriv y hy t)
  have hi :
      (∫ t in (0 : ℝ)..1, ψ (t : UnitAddCircle) * P.function ((t : UnitAddCircle), y)) +
      (∫ t in (0 : ℝ)..1, φ (t : UnitAddCircle) *
        ((w : ℂ) * P.derivative ((t : UnitAddCircle), y))) = 0 := by
    rw [← intervalIntegral.integral_add (h1.intervalIntegrable 0 1) (h2.intervalIntegrable 0 1),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t)
        ((h1.add h2).intervalIntegrable 0 1)]
    simp only [AddCircle.coe_period, AddCircle.coe_zero, sub_self]
  rw [circle_integral_eq_unit_interval, circle_integral_eq_unit_interval]
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using hi)

private theorem classical_raw_tensor_identity {w a : ℝ} (ha : 0 < a)
    (P : ClassicalPair w a) (φ ψ : C(UnitAddCircle, ℂ))
    (htest : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) {β : ℝ → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * P.derivative z)
      ∂derivativeMeasure a) =
    -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * P.function z ∂derivativeMeasure a) := by
  have hd : MemLp (fun z : CuspCylinder => (w : ℂ) * P.derivative z) 2 (functionMeasure a) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (P.derivative_memLp.of_measure_le_smul (by simp)
        (functionMeasure_le_derivativeMeasure ha)).const_smul (w : ℂ)
  rw [raw_tensor_fubini a _ hd φ hβ hc hs,
    raw_tensor_fubini a P.function P.function_memLp ψ hβ hc hs]
  calc
    _ = ∫ y : PositiveHeight, -(∫ x : UnitAddCircle,
        (β (y : ℝ) : ℂ) * ψ x * P.function (x, y) ∂AddCircle.haarAddCircle)
          ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictHeightTail_measurable a)] with y hy
      simp_rw [mul_assoc]
      rw [integral_const_mul, integral_const_mul,
        classical_circle_test_identity P φ ψ htest y hy, mul_neg]
    _ = _ := integral_neg _

/-- The native coordinates of every actual classical pair satisfy the
genuine raw weak tensor equation; representative changes are raw-AE. -/
theorem classical_coordinates_raw_weak {w a : ℝ} (ha : 0 < a) (P : ClassicalPair w a) :
    HasRawWeakPhysicalTailDerivative w a P.coordinates.1 P.coordinates.2 := by
  have hu := (derivativeMeasure_ac_functionMeasure a).ae_eq P.function_memLp.coeFn_toLp
  have hd := P.derivative_memLp.coeFn_toLp
  intro φ ψ hφ htest β hβ hc hs
  have hleft :
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * P.coordinates.2 z)
        ∂derivativeMeasure a) =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * P.derivative z)
        ∂derivativeMeasure a := by
    apply integral_congr_ae
    filter_upwards [hd] with z hz
    rw [hz]
  have hright :
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * P.coordinates.1 z
        ∂derivativeMeasure a) =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * P.function z
        ∂derivativeMeasure a := by
    apply integral_congr_ae
    filter_upwards [hu] with z hz
    rw [hz]
  rw [hleft, hright]
  exact classical_raw_tensor_identity ha P φ ψ htest hβ.continuous hc hs

/-- Actual raw-AE slice zero mean is exactly the native coefficient-zero
condition for the weighted zero extension. -/
theorem physical_zero_mean_iff_native (a : ℝ) (u : FunctionL2 a) :
    (∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) ↔
      tailValue a u ∈ zeroMeanCylinder := by
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      tailValue a u (p.2, p.1) = (strictCylinderTail a).indicator u (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae (tailValue_ae a u)
  have hslice := ae_ae_of_ae_prod hswap
  constructor
  · intro hm
    apply (mem_zeroMeanCylinder_iff _).mpr
    filter_upwards [hslice, heightMeasure_ae_iff_volume.mpr hm] with y hy hm
    rw [integral_congr_ae hy]
    by_cases ha : a < (y : ℝ)
    · simpa [strictCylinderTail, strictHeightTail, ha] using hm ha
    · simp [strictCylinderTail, strictHeightTail, ha]
  · intro hm
    apply heightMeasure_ae_iff_volume.mp
    have hmean := (mem_zeroMeanCylinder_iff _).mp hm
    filter_upwards [hslice, hmean] with y hy hm
    intro ha
    have he : (∫ x : UnitAddCircle, tailValue a u (x, y) ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      simpa [strictCylinderTail, strictHeightTail, ha] using hx
    exact he.symm.trans hm

theorem classical_coordinates_zero_mean {w a : ℝ} (P : ClassicalPair w a) :
    tailValue a P.coordinates.1 ∈ zeroMeanCylinder := by
  apply (physical_zero_mean_iff_native a P.coordinates.1).mp
  have hp := P.function_memLp.coeFn_toLp
  rw [functionMeasure_product] at hp
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂(heightMeasure.restrict (strictHeightTail a)).prod
        (AddCircle.haarAddCircle (T := (1 : ℝ))),
      P.coordinates.1 (p.2, p.1) = P.function (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae hp
  have hm : ∀ᵐ y ∂heightMeasure.restrict (strictHeightTail a),
      (∫ x : UnitAddCircle, P.coordinates.1 (x, y) ∂AddCircle.haarAddCircle) = 0 := by
    filter_upwards [ae_ae_of_ae_prod hswap,
      ae_restrict_mem (strictHeightTail_measurable a)] with y hy hytail
    rw [integral_congr_ae hy]
    exact P.mean_zero y hytail
  exact heightMeasure_ae_iff_volume.mp
    ((ae_restrict_iff' (strictHeightTail_measurable a)).mp hm)

end
end ImbalancedChen.Part3.CuspClassicalRawWeakTesting20261026b
