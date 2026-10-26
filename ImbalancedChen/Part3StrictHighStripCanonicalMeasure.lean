import ImbalancedChen.Part3PrimeEmbeddedHighCuspStrips
import ImbalancedChen.Part3ActualHighStripCircleMeasure

/-! Strict high-strip normalization in the original canonical H volume.
The native coordinate measure proves horizontal lines null; the actual
strict half-open strip therefore retains the proved closed-strip mass.
Its coordinate pushforward is exactly dx times y^-2 dy on y>Y.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.ActualHighStripCircleMeasure20261026b
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.ActualCuspStripCutoff20261025a
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b

namespace ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b

theorem strictHighStrip_measurable (Y : ℝ) : MeasurableSet (strictHighStrip Y) :=
  strip_measurable.inter
    ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet)

theorem verticalWeightedMeasure_singleton (Y : ℝ) :
    verticalWeightedMeasure ({Y} : Set ℝ) = 0 := by
  rw [verticalWeightedMeasure, Measure.withDensity_apply _ measurableSet_singleton]
  simp

/-- Native hyperbolic nullity is proved through the actual full chart
pushforward, rather than inferred from Euclidean nullity by a slogan. -/
theorem actual_horizontal_line_null (Y : ℝ) :
    (volume : Measure UpperHalfPlane) {z | z.im = Y} = 0 := by
  have hS : MeasurableSet ((Set.univ : Set ℝ) ×ˢ ({Y} : Set ℝ)) :=
    MeasurableSet.univ.prod measurableSet_singleton
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ ((Set.univ : Set ℝ) ×ˢ ({Y} : Set ℝ)))
    canonical_chart_map_measure
  rw [Measure.map_apply chartMap_measurableEmbedding.measurable hS,
    chartMeasure_eq_product, Measure.prod_prod, verticalWeightedMeasure_singleton, mul_zero] at hm
  have hpre : chartMap ⁻¹' ((Set.univ : Set ℝ) ×ˢ ({Y} : Set ℝ)) =
      {z : UpperHalfPlane | z.im = Y} := by
    ext z
    simp [chartMap]
  rwa [hpre] at hm

/-- Strict and closed lower boundaries define the same actual H measure;
the half-open horizontal interval remains literal in both. -/
theorem strictHighStrip_ae_closed (Y : ℝ) :
    strictHighStrip Y =ᵐ[(volume : Measure UpperHalfPlane)] highWidthStrip 1 Y := by
  have hne : ∀ᵐ z : UpperHalfPlane ∂volume, z.im ≠ Y := by
    apply ae_iff.mpr
    simpa only [not_not] using actual_horizontal_line_null Y
  filter_upwards [hne] with z hz
  apply propext
  change (z.re ∈ Ico (0 : ℝ) 1 ∧ Y < z.im) ↔ (z.re ∈ Ico (0 : ℝ) 1 ∧ Y ≤ z.im)
  exact and_congr_right (fun _ => ⟨le_of_lt, fun h => lt_of_le_of_ne h hz.symm⟩)

theorem strictHighStrip_restrict_eq_closed (Y : ℝ) :
    (volume : Measure UpperHalfPlane).restrict (strictHighStrip Y) =
      (volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 Y) :=
  Measure.restrict_congr_set (strictHighStrip_ae_closed Y)

/-- Exact finite canonical width-one mass, with no Gamma0 index factor. -/
theorem strictHighStrip_volume (Y : ℝ) (hY : 0 < Y) :
    (volume : Measure UpperHalfPlane) (strictHighStrip Y) = ENNReal.ofReal (1 / Y) := by
  have hm := congrArg (fun μ : Measure UpperHalfPlane => μ Set.univ)
    (strictHighStrip_restrict_eq_closed Y)
  simp only [Measure.restrict_apply_univ] at hm
  exact hm.trans (highWidthStrip_volume (by norm_num : (0 : ℝ) ≤ 1) hY)

theorem strictHighStrip_const_integrable (Y : ℝ) (hY : 0 < Y) :
    IntegrableOn (fun _ : UpperHalfPlane => (1 : ℂ)) (strictHighStrip Y) := by
  apply integrableOn_const
  rw [strictHighStrip_volume Y hY]
  exact ENNReal.ofReal_ne_top

/-- Exact coordinate measure dx times the ORIGINAL positive-height
reciprocal-square density, now restricted to y>Y rather than y>=Y. -/
theorem strictHighStrip_chart_map_measure (Y : ℝ) :
    ((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map chartMap =
      ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
        (verticalWeightedMeasure.restrict (Ioi Y)) := by
  have hpre : chartMap ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ioi Y) = strictHighStrip Y := by
    ext z
    change (z.re ∈ Ico (0 : ℝ) 1 ∧ z.im ∈ Ioi Y) ↔
      (z.re ∈ Ico (0 : ℝ) 1 ∧ Y < z.im)
    rfl
  rw [← hpre, ← Measure.restrict_map chartMap_measurableEmbedding.measurable
    (measurableSet_Ico.prod measurableSet_Ioi), canonical_chart_map_measure,
    chartMeasure_eq_product, ← Measure.prod_restrict]

end ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b
