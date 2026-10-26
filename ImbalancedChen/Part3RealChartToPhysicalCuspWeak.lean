import ImbalancedChen.Part3PeriodicChartHeightRigidity
import ImbalancedChen.Part3CuspRawWeakGraphEquality

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine real-chart weak horizontal differentiation of the literal real
lifts of physical cusp representatives implies the full raw circle
tensor weak equation, including height tests crossing the lower tail
height. The seam-free compact partition and local height fundamental
lemma are consumed; raw product Fubini then integrates over the sharp
physical tail. Local chart L1 and global physical mixed L² are separate
honest primitive inputs. No chart derivative, H1 trace, circle weak law,
Fourier equation or graph membership is assumed.
-/
namespace ImbalancedChen.Part3.RealChartToPhysicalCuspWeak20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open PeriodicChartHeightRigidity20261026b CuspPhysicalWeakTailModes20261026b
open CuspRawWeakDerivativeBridge20261026b CuspRawWeakGraphEquality20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def realCylinderLift (H : CuspCylinder → ℂ) (p : Plane) : ℂ :=
  if hp : 0 < p.2 then H ((p.1 : UnitAddCircle), ⟨p.2, hp⟩) else 0

@[simp] theorem realCylinderLift_positive (H : CuspCylinder → ℂ)
    (x : ℝ) (y : PositiveHeight) : realCylinderLift H (x, (y : ℝ)) = H ((x : UnitAddCircle), y) := by
  simp [realCylinderLift, y.property]

/-- Periodicity is a property of the literal quotient lift for arbitrary
physical measurable representatives; it does not use differentiability. -/
theorem realCylinderLift_periodic (H : CuspCylinder → ℂ) (y : ℝ) :
    Function.Periodic (fun x : ℝ => realCylinderLift H (x, y)) 1 := by
  intro x
  by_cases hy : 0 < y
  · simp [realCylinderLift, hy, AddCircle.coe_add, AddCircle.coe_period]
  · simp [realCylinderLift, hy]

private theorem circle_integral_eq_interval (f : UnitAddCircle → ℂ) :
    (∫ x : UnitAddCircle, f x ∂AddCircle.haarAddCircle) =
      ∫ t in (0 : ℝ)..1, f (t : UnitAddCircle) := by
  rw [circleHaar_eq_volume]
  calc
    _ = ∫ t in Ioc (0 : ℝ) 1, f (t : UnitAddCircle) := by
      simpa only [zero_add] using (AddCircle.integral_preimage 1 0 f).symm
    _ = _ := (intervalIntegral.integral_of_le zero_le_one).symm

theorem onePeriodChartPair_lift (φ : C(UnitAddCircle, ℂ)) (H : CuspCylinder → ℂ)
    (y : PositiveHeight) :
    onePeriodChartPair φ (realCylinderLift H) (y : ℝ) =
      ∫ x : UnitAddCircle, φ x * H (x, y) ∂AddCircle.haarAddCircle := by
  rw [circle_integral_eq_interval]
  simp only [onePeriodChartPair, realCylinderLift_positive]

/-- The REAL chart weak equation, local chart L1 and the actual mixed L²
vectors suffice for full physical raw tensor testing on the sharp tail. -/
theorem real_chart_implies_physical_raw_weak {w a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a)
    (hU : LocallyIntegrableOn (realCylinderLift u) {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn (realCylinderLift (fun z => (w : ℂ) * d z))
      {p : Plane | a < p.2} volume)
    (hchart : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2}
      (realCylinderLift u) (realCylinderLift (fun z => (w : ℂ) * d z))) :
    HasRawWeakPhysicalTailDerivative w a u d := by
  intro φ ψ hφ htest β hβ hc hs
  have hreal := real_chart_weak_one_period_ae hU hD
    (fun y hy => realCylinderLift_periodic u y)
    (fun y hy => realCylinderLift_periodic (fun z => (w : ℂ) * d z) y)
    hchart φ ψ hφ htest
  have hsub : ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, φ x * ((w : ℂ) * d (x, y)) ∂AddCircle.haarAddCircle) =
        -(∫ x : UnitAddCircle, ψ x * u (x, y) ∂AddCircle.haarAddCircle) := by
    have ht : ∀ᵐ y : PositiveHeight ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
        onePeriodChartPair φ (realCylinderLift (fun z => (w : ℂ) * d z)) (y : ℝ) =
          -onePeriodChartPair ψ (realCylinderLift u) (y : ℝ) :=
      (ae_restrict_iff_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi).mp (ae_restrict_of_ae hreal)
    filter_upwards [ht] with y hy
    intro hay
    simpa only [onePeriodChartPair_lift] using hy hay
  have hdw : MemLp (fun z : CuspCylinder => (w : ℂ) * d z) 2 (functionMeasure a) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      ((Lp.memLp d).of_measure_le_smul (by simp)
        (functionMeasure_le_derivativeMeasure ha)).const_smul (w : ℂ)
  rw [raw_tensor_fubini a _ hdw φ hβ.continuous hc hs,
    raw_tensor_fubini a u (Lp.memLp u) ψ hβ.continuous hc hs]
  calc
    _ = ∫ y : PositiveHeight, -(∫ x : UnitAddCircle,
        (β (y : ℝ) : ℂ) * ψ x * u (x, y) ∂AddCircle.haarAddCircle)
          ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hsub,
        ae_restrict_mem (strictHeightTail_measurable a)] with y hy hytail
      simp_rw [mul_assoc]
      rw [integral_const_mul, integral_const_mul, hy hytail, mul_neg]
    _ = _ := integral_neg _

/-- The actual graph equality is now applicable from REAL chart weak
data, without postulating a circle weak law or seam trace. -/
theorem real_chart_physical_pair_mem_closed_graph {w a : ℝ} (hw : 0 < w) (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a)
    (hU : LocallyIntegrableOn (realCylinderLift u) {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn (realCylinderLift (fun z => (w : ℂ) * d z))
      {p : Plane | a < p.2} volume)
    (hchart : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2}
      (realCylinderLift u) (realCylinderLift (fun z => (w : ℂ) * d z)))
    (hmean : ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (u, d) ∈ closedHorizontalGraph w a :=
  raw_weak_physical_pair_mem_closed_graph hw ha
    (real_chart_implies_physical_raw_weak ha u d hU hD hchart) hmean

end
end ImbalancedChen.Part3.RealChartToPhysicalCuspWeak20261026b
