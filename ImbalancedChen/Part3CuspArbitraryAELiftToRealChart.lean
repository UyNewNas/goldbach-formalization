import ImbalancedChen.Part3CuspCircleAELiftToRealChart

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

AE physical representatives lift to the real chart WITHOUT pointwise
measurability assumptions on either representative. The actual global
covering map is quasi-measure-preserving, proved from the previous true
unit-interval null-set lifting. Its product with height and the exact
positive-height coordinate embedding then transport arbitrary AE events.
This is the needed interface for merely AE-strong coherent raw gradients.
-/
namespace ImbalancedChen.Part3.CuspArbitraryAELiftToRealChart20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ProductConvolutionSecondDerivatives20261026a RealChartToPhysicalCuspWeak20261026b
open CuspClassicalRawWeakTesting20261026b CuspCircleAELiftToRealChart20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

theorem circle_covering_quasiMeasurePreserving :
    QuasiMeasurePreserving ((↑) : ℝ → UnitAddCircle) volume AddCircle.haarAddCircle := by
  refine ⟨AddCircle.measurable_mk', ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hzero
  rw [Measure.map_apply AddCircle.measurable_mk' hS]
  have hc : ∀ᵐ x ∂AddCircle.haarAddCircle, x ∉ S := by
    rw [ae_iff]
    simpa only [not_not, setOf_mem_eq] using hzero
  have hr := ae_circle_implies_ae_real hc
  rw [ae_iff] at hr
  simpa only [not_not, Set.preimage, mem_setOf_eq] using hr

private theorem height_tail_coordinate_preserving {a : ℝ} (ha : 0 < a) :
    MeasurePreserving ((↑) : PositiveHeight → ℝ)
      ((volume : Measure PositiveHeight).restrict (strictHeightTail a))
      ((volume : Measure ℝ).restrict (Ioi a)) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  have hb : (volume : Measure PositiveHeight).map ((↑) : PositiveHeight → ℝ) =
      (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) :=
    map_comap_subtype_coe measurableSet_Ioi volume
  have hres := (MeasurableEmbedding.subtype_coe measurableSet_Ioi).restrict_map
    (volume : Measure PositiveHeight) (Ioi a)
  change ((volume : Measure PositiveHeight).restrict
    (((↑) : PositiveHeight → ℝ) ⁻¹' Ioi a)).map ((↑) : PositiveHeight → ℝ) = _
  rw [← hres, hb, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (show Ioi a ⊆ Ioi (0 : ℝ) from fun y hy => ha.trans hy)]

def realHeightEmbedding (p : ℝ × PositiveHeight) : Plane := (p.1, (p.2 : ℝ))

theorem realHeightEmbedding_measurableEmbedding : MeasurableEmbedding realHeightEmbedding :=
  MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

theorem realHeightEmbedding_tail_preserving {a : ℝ} (ha : 0 < a) :
    MeasurePreserving realHeightEmbedding
      ((volume : Measure ℝ).prod ((volume : Measure PositiveHeight).restrict (strictHeightTail a)))
      ((volume : Measure Plane).restrict {p : Plane | a < p.2}) := by
  have hm := (MeasurePreserving.id (volume : Measure ℝ)).prod (height_tail_coordinate_preserving ha)
  have hset : (univ : Set ℝ) ×ˢ Ioi a = {p : Plane | a < p.2} := by ext p; simp
  have ht : (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi a)) =
      (volume : Measure Plane).restrict {p : Plane | a < p.2} := by
    simpa only [Measure.restrict_univ, hset] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) univ (Ioi a))
  simpa only [ht, realHeightEmbedding, Prod.map, id_eq] using hm

/-- Strong representative lifting: H and J can be arbitrary functions,
not pointwise measurable choices. Only their genuine physical AE
equality is supplied. -/
theorem arbitrary_raw_physical_ae_real_lift {a : ℝ} (ha : 0 < a) {H J : CuspCylinder → ℂ}
    (hHJ : H =ᵐ[derivativeMeasure a] J) :
    realCylinderLift H =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift J := by
  rw [derivativeMeasure_product] at hHJ
  have hcover := (circle_covering_quasiMeasurePreserving.prodMap
    (MeasurePreserving.id ((volume : Measure PositiveHeight).restrict
      (strictHeightTail a))).quasiMeasurePreserving).ae_eq hHJ
  have hm := realHeightEmbedding_tail_preserving ha
  rw [← hm.map_eq, realHeightEmbedding_measurableEmbedding.ae_map_iff]
  simpa only [realHeightEmbedding, realCylinderLift_positive, Prod.map, id_eq] using hcover

theorem arbitrary_weighted_physical_ae_real_lift {a : ℝ} (ha : 0 < a) {H J : CuspCylinder → ℂ}
    (hHJ : H =ᵐ[functionMeasure a] J) :
    realCylinderLift H =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift J :=
  arbitrary_raw_physical_ae_real_lift ha ((derivativeMeasure_ac_functionMeasure a).ae_eq hHJ)

end
end ImbalancedChen.Part3.CuspArbitraryAELiftToRealChart20261026b
