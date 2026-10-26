import ImbalancedChen.Part3ActualHighStripNativeCylinderMeasure
import ImbalancedChen.Part3ActualInfinityHighTailL2Pullback

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An explicit native complex-linear L2 equivalence between the literal
hyperbolic high infinity strip and the actual restricted cusp cylinder.
The inverse uses the actual AddCircle Ico(0,1) representative. Its two
pointwise inverse laws on the correct sets prove both measure inverse
and Hilbert inverse identities; no onto/isometry premise is supplied.
-/
namespace ImbalancedChen.Part3.ActualHighStripCylinderL2Equivalence20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane ENNReal
open CuspCylinderMeasure20261024z
open ActualCuspStripCutoff20261025a
open ActualHighStripNativeCylinderMeasure20261026b
open ActualInfinityHighTailL2Pullback20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def nativeCylinderPoint (p : CuspCylinder) : UpperHalfPlane :=
  ⟨⟨((AddCircle.measurableEquivIco (1 : ℝ) 0 p.1 : Ico (0 : ℝ) (0 + 1)) : ℝ),
      (p.2 : ℝ)⟩, p.2.property⟩

theorem nativeCylinderPoint_measurable : Measurable nativeCylinderPoint := by
  have hx : Measurable (fun p : CuspCylinder =>
      ((AddCircle.measurableEquivIco (1 : ℝ) 0 p.1 : Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp measurable_fst)
  have hy : Measurable (fun p : CuspCylinder => (p.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact (Complex.measurableEquivRealProd.symm.measurable.comp (hx.prodMk hy)).subtype_mk
    (fun p => p.2.property)

theorem coordinate_nativeCylinderPoint (p : CuspCylinder) :
    highStripNativeCylinderCoordinate (nativeCylinderPoint p) = p := by
  apply Prod.ext
  · change (((AddCircle.equivIco (1 : ℝ) 0 p.1 : Ico (0 : ℝ) (0 + 1)) : ℝ) :
      UnitAddCircle) = p.1
    exact AddCircle.coe_equivIco
  · apply Subtype.ext
    rfl

theorem nativeCylinderPoint_coordinate {Y : ℝ} (z : UpperHalfPlane)
    (hz : z ∈ highWidthStrip 1 Y) :
    nativeCylinderPoint (highStripNativeCylinderCoordinate z) = z := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change ((AddCircle.equivIco (1 : ℝ) 0 (z.re : UnitAddCircle) :
      Ico (0 : ℝ) (0 + 1)) : ℝ) = z.re
    have hx : z.re ∈ Ico (0 : ℝ) (0 + 1) := by simpa only [zero_add] using hz.1
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hx)
  · rfl

theorem nativeCylinderPoint_mem_highStrip {Y : ℝ} (p : CuspCylinder)
    (hp : p ∈ closedCylinderTail Y) : nativeCylinderPoint p ∈ highWidthStrip 1 Y := by
  constructor
  · simpa only [zero_add] using (AddCircle.measurableEquivIco (1 : ℝ) 0 p.1).property
  · exact hp

/-- The explicit representative map is measure preserving in the inverse
direction, using the actual high-strip inverse identity almost everywhere. -/
theorem nativeCylinderPoint_map_measure (Y : ℝ) :
    (cylinderMeasure.restrict (closedCylinderTail Y)).map nativeCylinderPoint =
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y) := by
  rw [← highStrip_native_cylinder_map_measure Y,
    Measure.map_map nativeCylinderPoint_measurable highStripNativeCylinderCoordinate_measurable]
  have hpoint : (nativeCylinderPoint ∘ highStripNativeCylinderCoordinate) =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)] id := by
    filter_upwards [ae_restrict_mem (highWidthStrip_measurable 1 Y)] with z hz
    exact nativeCylinderPoint_coordinate z hz
  rw [Measure.map_congr hpoint, Measure.map_id]

def nativeCylinderPoint_measurePreserving (Y : ℝ) :
    MeasurePreserving nativeCylinderPoint
      (cylinderMeasure.restrict (closedCylinderTail Y))
      ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)) :=
  ⟨nativeCylinderPoint_measurable, nativeCylinderPoint_map_measure Y⟩

abbrev CylinderTailL2 (Y : ℝ) :=
  Lp ℂ 2 (cylinderMeasure.restrict (closedCylinderTail Y))

def stripToCylinderIsometry (Y : ℝ) : HighStripL2 Y →ₗᵢ[ℂ] CylinderTailL2 Y :=
  Lp.compMeasurePreservingₗᵢ ℂ nativeCylinderPoint (nativeCylinderPoint_measurePreserving Y)

def cylinderToStripIsometry (Y : ℝ) : CylinderTailL2 Y →ₗᵢ[ℂ] HighStripL2 Y :=
  Lp.compMeasurePreservingₗᵢ ℂ highStripNativeCylinderCoordinate
    (highStripNativeCylinderCoordinate_measurePreserving Y)

theorem stripToCylinderIsometry_ae (Y : ℝ) (f : HighStripL2 Y) :
    stripToCylinderIsometry Y f =ᵐ[cylinderMeasure.restrict (closedCylinderTail Y)]
      fun p => f (nativeCylinderPoint p) :=
  Lp.coeFn_compMeasurePreserving f (nativeCylinderPoint_measurePreserving Y)

theorem cylinderToStripIsometry_ae (Y : ℝ) (f : CylinderTailL2 Y) :
    cylinderToStripIsometry Y f =ᵐ[
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y)]
      fun z => f (highStripNativeCylinderCoordinate z) :=
  Lp.coeFn_compMeasurePreserving f (highStripNativeCylinderCoordinate_measurePreserving Y)

theorem cylinderToStrip_stripToCylinder (Y : ℝ) (f : HighStripL2 Y) :
    cylinderToStripIsometry Y (stripToCylinderIsometry Y f) = f := by
  apply Lp.ext
  have hf := (highStripNativeCylinderCoordinate_measurePreserving Y).quasiMeasurePreserving.ae_eq
    (stripToCylinderIsometry_ae Y f)
  filter_upwards [cylinderToStripIsometry_ae Y (stripToCylinderIsometry Y f), hf,
    ae_restrict_mem (highWidthStrip_measurable 1 Y)] with z h1 h2 hz
  rw [h1, h2, nativeCylinderPoint_coordinate z hz]

theorem stripToCylinder_cylinderToStrip (Y : ℝ) (f : CylinderTailL2 Y) :
    stripToCylinderIsometry Y (cylinderToStripIsometry Y f) = f := by
  apply Lp.ext
  have hf := (nativeCylinderPoint_measurePreserving Y).quasiMeasurePreserving.ae_eq
    (cylinderToStripIsometry_ae Y f)
  filter_upwards [stripToCylinderIsometry_ae Y (cylinderToStripIsometry Y f), hf] with p h1 h2
  rw [h1, h2, coordinate_nativeCylinderPoint]

/-- An actual ONTO native Hilbert equivalence, with the literal point
representatives and unchanged canonical spatial density. -/
def highStripCylinderL2Equiv (Y : ℝ) : HighStripL2 Y ≃ₗᵢ[ℂ] CylinderTailL2 Y where
  toFun := stripToCylinderIsometry Y
  invFun := cylinderToStripIsometry Y
  map_add' := (stripToCylinderIsometry Y).map_add
  map_smul' := (stripToCylinderIsometry Y).map_smul
  left_inv := cylinderToStrip_stripToCylinder Y
  right_inv := stripToCylinder_cylinderToStrip Y
  norm_map' := (stripToCylinderIsometry Y).norm_map

end
end ImbalancedChen.Part3.ActualHighStripCylinderL2Equivalence20261026b
