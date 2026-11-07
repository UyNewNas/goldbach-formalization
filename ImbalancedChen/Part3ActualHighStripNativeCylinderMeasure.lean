import ImbalancedChen.Part3ActualHighStripCircleMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal high upper-half-plane strip maps to the ACTUAL native cusp
cylinder with its PositiveHeight subtype and its original normalized
Haar times dy/y^2 measure. The subtype height measure is identified with
the earlier real-coordinate weighted measure, then injectivity of the
real-height embedding gives the full native pushforward identity.
This is spatial coordinate transport only, not spectral completeness.
-/
namespace ImbalancedChen.Part3.ActualHighStripNativeCylinderMeasure20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open CanonicalTensorHyperbolicLaplacianForm20261024z
open MaassWeightedCoordinateL220261024zz
open CuspCylinderMeasure20261024z
open ActualCuspStripCutoff20261025a
open ActualHighStripCircleMeasure20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The actual PositiveHeight dy/y^2 measure has exactly the existing
real-coordinate positive-height weighted measure as its pushforward. -/
theorem positiveHeight_map_coe_measure :
    heightMeasure.map ((↑) : PositiveHeight → ℝ) = verticalWeightedMeasure := by
  have hb : (volume : Measure PositiveHeight).map ((↑) : PositiveHeight → ℝ) =
      (volume : Measure ℝ).restrict (Ioi 0) := by
    change ((volume : Measure ℝ).comap ((↑) : PositiveHeight → ℝ)).map
      ((↑) : PositiveHeight → ℝ) = _
    exact Measure.map_comap_subtype_coe measurableSet_Ioi
  have hdensity (y : PositiveHeight) : heightDensity y = verticalWeight (y : ℝ) := by
    apply NNReal.coe_injective
    simp only [heightDensity_coe, verticalWeight, NNReal.coe_mk, one_div]
  apply Measure.ext
  intro S hS
  rw [heightMeasure, Measure.map_apply measurable_subtype_coe hS,
    Measure.withDensity_apply _ (measurable_subtype_coe hS),
    verticalWeightedMeasure, Measure.withDensity_apply _ hS]
  have hd : Measurable (fun y : ℝ => (verticalWeight y : ℝ≥0∞)) :=
    verticalWeight_measurable.coe_nnreal_ennreal
  have hm := lintegral_map (μ := (volume : Measure PositiveHeight))
    (hd.indicator hS) measurable_subtype_coe
  rw [hb, lintegral_indicator hS] at hm
  have heq : (fun y : PositiveHeight =>
      S.indicator (fun t : ℝ => (verticalWeight t : ℝ≥0∞)) (y : ℝ)) =
      (((↑) : PositiveHeight → ℝ) ⁻¹' S).indicator
        (fun y => (heightDensity y : ℝ≥0∞)) := by
    funext y
    by_cases hy : (y : ℝ) ∈ S
    · simp only [Set.indicator_of_mem hy, Set.mem_preimage, hdensity]
    · simp only [Set.indicator_of_notMem hy, Set.mem_preimage]
  rw [heq, lintegral_indicator (measurable_subtype_coe hS)] at hm
  exact hm.symm

def cylinderRealHeight (p : CuspCylinder) : UnitAddCircle × ℝ :=
  (p.1, (p.2 : ℝ))

theorem cylinderRealHeight_measurableEmbedding : MeasurableEmbedding cylinderRealHeight :=
  MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

theorem cylinder_real_height_map :
    cylinderMeasure.map cylinderRealHeight = AddCircle.haarAddCircle.prod verticalWeightedMeasure := by
  change ((AddCircle.haarAddCircle (T := (1 : ℝ))).prod heightMeasure).map
    (Prod.map id ((↑) : PositiveHeight → ℝ)) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_subtype_coe,
    Measure.map_id, positiveHeight_map_coe_measure]

def closedCylinderTail (Y : ℝ) : Set CuspCylinder := {p | Y ≤ (p.2 : ℝ)}

theorem closedCylinderTail_measurable (Y : ℝ) : MeasurableSet (closedCylinderTail Y) :=
  measurableSet_Ici.preimage (measurable_subtype_coe.comp measurable_snd)

theorem cylinder_real_height_tail_map (Y : ℝ) :
    (cylinderMeasure.restrict (closedCylinderTail Y)).map cylinderRealHeight =
      AddCircle.haarAddCircle.prod (verticalWeightedMeasure.restrict (Ici Y)) := by
  let S : Set (UnitAddCircle × ℝ) := univ ×ˢ Ici Y
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ici
  have hp : cylinderRealHeight ⁻¹' S = closedCylinderTail Y := by
    ext p
    simp [S, closedCylinderTail, cylinderRealHeight]
  rw [← hp, ← Measure.restrict_map cylinderRealHeight_measurableEmbedding.measurable hS,
    cylinder_real_height_map, S, ← Measure.prod_restrict, Measure.restrict_univ]

def highStripNativeCylinderCoordinate (z : UpperHalfPlane) : CuspCylinder :=
  ((z.re : UnitAddCircle), ⟨z.im, z.im_pos⟩)

theorem highStripNativeCylinderCoordinate_measurable :
    Measurable highStripNativeCylinderCoordinate :=
  (AddCircle.measurable_mk'.comp UpperHalfPlane.continuous_re.measurable).prodMk
    (UpperHalfPlane.continuous_im.measurable.subtype_mk (fun z => z.im_pos))

/-- Exact native cylinder pushforward, with the literal height subtype
and closed high tail. Endpoints in the horizontal period are paid by
the previously proved quotient-interval measure identity. -/
theorem highStrip_native_cylinder_map_measure (Y : ℝ) :
    ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map
        highStripNativeCylinderCoordinate = cylinderMeasure.restrict (closedCylinderTail Y) := by
  apply cylinderRealHeight_measurableEmbedding.map_injective
  rw [Measure.map_map cylinderRealHeight_measurableEmbedding.measurable
    highStripNativeCylinderCoordinate_measurable, cylinder_real_height_tail_map]
  change ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)).map
    highStripCircleCoordinate = _
  exact highStrip_circle_map_measure Y

theorem highStripNativeCylinderCoordinate_measurePreserving (Y : ℝ) :
    MeasurePreserving highStripNativeCylinderCoordinate
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y))
      (cylinderMeasure.restrict (closedCylinderTail Y)) :=
  ⟨highStripNativeCylinderCoordinate_measurable, highStrip_native_cylinder_map_measure Y⟩

end
end ImbalancedChen.Part3.ActualHighStripNativeCylinderMeasure20261026b
