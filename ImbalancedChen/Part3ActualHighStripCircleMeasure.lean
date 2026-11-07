import ImbalancedChen.Part3ActualInfinityHighTailMeasureTransport
import ImbalancedChen.Part3CanonicalPlanarL2Unitary
import ImbalancedChen.Part3CuspCylinderMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal high-strip coordinates (real part modulo one, imaginary part)
push canonical hyperbolic volume to normalized circle Haar times the
actual real-line y^-2 dy measure restricted to y>=Y. Both the canonical
chart density and the half-open circle representative are proved at
the measure level. This is one spatial coordinate supplier, not an
automorphic spectral measure or an all-cusps identification.
-/
namespace ImbalancedChen.Part3.ActualHighStripCircleMeasure20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open CanonicalTensorHyperbolicLaplacianForm20261024z
open UpperHalfPlaneHyperbolicMeasure20261024z
open CanonicalPlanarL2UnitarySourceOnly
open MaassWeightedCoordinateL220261024zz
open ActualCuspStripCutoff20261025a
open CuspCylinderMeasure20261024z

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The existing canonical chart identities upgraded to equality of
MEASURES, including the exact reciprocal-square density. -/
theorem canonical_chart_map_measure :
    (volume : Measure UpperHalfPlane).map chartMap = chartMeasure := by
  change (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))).map
    chartMap = chartMeasure
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply chartMap_measurableEmbedding.measurable hS,
    Measure.withDensity_apply _ (chartMap_measurableEmbedding.measurable hS),
    chartMeasure, Measure.withDensity_apply _ hS]
  have hd : Measurable (fun p : ℝ × ℝ => (chartWeight p : ℝ≥0∞)) :=
    chartWeight_measurable.coe_nnreal_ennreal
  have hm := lintegral_map (μ := coordinateMeasure) (hd.indicator hS)
    chartMap_measurableEmbedding.measurable
  rw [map_coordinateMeasure, lintegral_indicator hS] at hm
  have heq : (fun z : UpperHalfPlane =>
      S.indicator (fun p : ℝ × ℝ => (chartWeight p : ℝ≥0∞)) (chartMap z)) =
      (chartMap ⁻¹' S).indicator (fun z => (upperDensityNN z : ℝ≥0∞)) := by
    funext z
    by_cases hz : chartMap z ∈ S
    · simp only [Set.indicator_of_mem hz, Set.mem_preimage, upperDensityNN_eq_chartWeight]
    · simp only [Set.indicator_of_notMem hz, Set.mem_preimage]
  rw [heq] at hm
  rw [lintegral_indicator (chartMap_measurableEmbedding.measurable hS)] at hm
  exact hm.symm

theorem highRectangle_measurable (Y : ℝ) : MeasurableSet (highRectangle 1 Y) :=
  measurableSet_Ico.prod measurableSet_Ici

theorem highStrip_chart_preimage (Y : ℝ) :
    chartMap ⁻¹' highRectangle 1 Y = highWidthStrip 1 Y := by
  ext z
  simp only [highRectangle, Set.mem_preimage, Set.mem_prod,
    Set.mem_Ico, Set.mem_Ici, chartMap, Complex.measurableEquivRealProd_apply,
    highWidthStrip, widthStrip, Set.mem_setOf_eq]
  tauto

/-- The width-one high strip carries exactly dx times restricted
positive-height y^-2 dy before quotienting the horizontal coordinate. -/
theorem highStrip_chart_map_measure (Y : ℝ) :
    ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map chartMap =
      ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
        (verticalWeightedMeasure.restrict (Ici Y)) := by
  rw [← highStrip_chart_preimage,
    ← Measure.restrict_map chartMap_measurableEmbedding.measurable
      (highRectangle_measurable Y), canonical_chart_map_measure,
    chartMeasure_eq_product, highRectangle, ← Measure.prod_restrict]

theorem circle_projection_Ico_measurePreserving :
    MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)) AddCircle.haarAddCircle := by
  rw [circleHaar_eq_volume, restrict_Ico_eq_restrict_Ioc]
  simpa only [zero_add] using AddCircle.measurePreserving_mk (1 : ℝ) (0 : ℝ)

def highStripCircleCoordinate (z : UpperHalfPlane) : UnitAddCircle × ℝ :=
  ((z.re : UnitAddCircle), z.im)

theorem highStripCircleCoordinate_measurable : Measurable highStripCircleCoordinate :=
  (AddCircle.measurable_mk'.comp UpperHalfPlane.continuous_re.measurable).prodMk
    UpperHalfPlane.continuous_im.measurable

/-- Exact normalized-Haar and physical-height coordinate measure.
The real height measure itself is already supported on positive heights. -/
theorem highStrip_circle_map_measure (Y : ℝ) :
    ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map
        highStripCircleCoordinate =
      AddCircle.haarAddCircle.prod (verticalWeightedMeasure.restrict (Ici Y)) := by
  have heq : highStripCircleCoordinate =
      (Prod.map (fun x : ℝ => (x : UnitAddCircle)) id) ∘ chartMap := rfl
  rw [heq, ← Measure.map_map
    (AddCircle.measurable_mk'.prodMap measurable_id)
    chartMap_measurableEmbedding.measurable, highStrip_chart_map_measure,
    ← Measure.map_prod_map _ _ AddCircle.measurable_mk' measurable_id,
    circle_projection_Ico_measurePreserving.map_eq, Measure.map_id]

theorem highStripCircleCoordinate_measurePreserving (Y : ℝ) :
    MeasurePreserving highStripCircleCoordinate
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y))
      (AddCircle.haarAddCircle.prod (verticalWeightedMeasure.restrict (Ici Y))) :=
  ⟨highStripCircleCoordinate_measurable, highStrip_circle_map_measure Y⟩

end
end ImbalancedChen.Part3.ActualHighStripCircleMeasure20261026b
