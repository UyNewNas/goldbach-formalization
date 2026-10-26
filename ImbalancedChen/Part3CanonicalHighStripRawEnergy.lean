import ImbalancedChen.Part3ActualQuotientHighStripL2
import ImbalancedChen.Part3ActualMaassFourierODE
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The canonical hyperbolic high-strip norm is transported directly through
the actual real/imaginary chart and its y^-2 density. The only period-cell
change is the proved equality of Lebesgue restrictions Ico and Icc.
No trace norm, Fourier coefficient norm, or planar-unitary premise occurs.
-/

namespace ImbalancedChen.Part3.CanonicalHighStripRawEnergy20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ActualPoincareSpectralCoefficient20261026a ActualQuotientHighStripL220261026a
open Gamma0QuotientCellPushforward20261025a GammaInfinityTranslationStrip20261025a
open CanonicalTensorHyperbolicLaplacianForm20261024z
open CanonicalPlanarL2UnitarySourceOnly MaassWeightedCoordinateL220261024zz
open UpperHalfPlaneHyperbolicMeasure20261024z ActualMaassFourierODE20261026a
attribute [local instance] Measure.Subtype.measureSpace

local instance periodCell_finite : IsFiniteMeasure (volume : Measure PeriodCell) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top

/-- Integrability, rather than only a potentially default-zero integral,
is transported through the actual canonical chart and its actual density. -/
theorem canonical_real_integrable_iff_chart (G : ℝ × ℝ → ℝ) :
    Integrable (G ∘ chartMap) (volume : Measure UpperHalfPlane) ↔
      Integrable G chartMeasure := by
  change Integrable (G ∘ chartMap)
    (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul upperDensityNN_measurable]
  unfold chartMeasure
  rw [integrable_withDensity_iff_integrable_smul chartWeight_measurable,
    ← map_coordinateMeasure, chartMap_measurableEmbedding.integrable_map_iff]
  congr 1
  funext z
  simp only [Function.comp_apply, chartMap, upperDensityNN_eq_chartWeight]

def rawRectangle (Y : ℝ) : Set (ℝ × ℝ) := Ico (0 : ℝ) 1 ×ˢ Ioi Y

theorem rawRectangle_measurable (Y : ℝ) : MeasurableSet (rawRectangle Y) :=
  measurableSet_Ico.prod measurableSet_Ioi

theorem rawRectangle_subset_upper {Y : ℝ} (hY : 0 ≤ Y) :
    rawRectangle Y ⊆ upperChart := fun p hp => hY.trans_lt hp.2

theorem rawRectangle_chart_preimage (Y : ℝ) :
    chartMap ⁻¹' rawRectangle Y = actualHighStrip Y := by
  ext z
  change (z.re ∈ Ico (0 : ℝ) 1 ∧ Y < z.im) ↔
    (Y < z.im ∧ z.re ∈ Ico (0 : ℝ) 1)
  exact and_comm

/-- Local density transport on the precise high rectangle. -/
theorem high_strip_integrable_iff_raw (G : ℝ × ℝ → ℝ) {Y : ℝ} (hY : 0 ≤ Y) :
    IntegrableOn (G ∘ chartMap) (actualHighStrip Y) ↔
      IntegrableOn (fun p => p.2⁻¹^2 * G p) (rawRectangle Y) := by
  have hchart := canonical_real_integrable_iff_chart ((rawRectangle Y).indicator G)
  have hind : ((rawRectangle Y).indicator G) ∘ chartMap =
      (actualHighStrip Y).indicator (G ∘ chartMap) := by
    rw [← rawRectangle_chart_preimage]
    rfl
  rw [hind, integrable_indicator_iff (actualHighStrip_measurable Y),
    integrable_indicator_iff (rawRectangle_measurable Y)] at hchart
  rw [hchart]
  change Integrable G (chartMeasure.restrict (rawRectangle Y)) ↔ _
  have hinter : rawRectangle Y ∩ upperChart = rawRectangle Y :=
    inter_eq_left.mpr (rawRectangle_subset_upper hY)
  rw [chartMeasure, restrict_withDensity (rawRectangle_measurable Y),
    Measure.restrict_restrict (rawRectangle_measurable Y), hinter,
    integrable_withDensity_iff_integrable_smul chartWeight_measurable]
  rfl

def cellInclusion : PeriodCell × ℝ → ℝ × ℝ := fun p => (p.1, p.2)

theorem cellInclusion_measurableEmbedding : MeasurableEmbedding cellInclusion :=
  (MeasurableEmbedding.subtype_coe measurableSet_Icc).prodMap MeasurableEmbedding.id

theorem cellInclusion_map (Y : ℝ) :
    Measure.map cellInclusion ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))) =
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Ioi Y)) := by
  change Measure.map (Prod.map Subtype.val id) _ = _
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    Measure.map_id, Measure.map_comap_subtype_coe measurableSet_Icc]

/-- Width-one raw dx dy/y^2 energy on the literal compact period cell,
deduced from the canonical high-strip L2 norm of the original H function. -/
theorem canonical_high_strip_raw_energy (F : UpperHalfPlane → ℂ) {Y : ℝ}
    (hY : 0 ≤ Y)
    (hF : IntegrableOn (fun z => ‖F z‖^2) (actualHighStrip Y)) :
    Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2 * ‖chartPullback F (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))) := by
  have hpull : (fun p : ℝ × ℝ => ‖chartPullback F p‖^2) ∘ chartMap =
      fun z => ‖F z‖^2 := by
    funext z
    rw [Function.comp_apply, chartPullback_at_upper]
  have hraw := (high_strip_integrable_iff_raw
    (fun p => ‖chartPullback F p‖^2) hY).mp (by simpa only [hpull] using hF)
  change Integrable _ ((volume : Measure (ℝ × ℝ)).restrict (rawRectangle Y)) at hraw
  rw [rawRectangle, Measure.volume_eq_prod, ← Measure.prod_restrict,
    restrict_Ico_eq_restrict_Icc, ← cellInclusion_map Y] at hraw
  exact cellInclusion_measurableEmbedding.integrable_map_iff.mp hraw

/-- Actual quotient L2 now supplies the raw spatial energy required by
the independently proved actual Fourier ODE and real K selection. -/
theorem actual_quotient_raw_strip_energy (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U))
    (hU2 : MemLp U 2 (carrierPushforward N)) (Y : ℝ) (hY : 1 ≤ Y) :
    Integrable (fun p : PeriodCell × ℝ =>
      p.2⁻¹^2 * ‖chartPullback (testLift N U) (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))) :=
  canonical_high_strip_raw_energy (testLift N U) (zero_le_one.trans hY)
    (actual_quotient_high_strip_sq_integrable N U hU hU2 Y hY)

end
end ImbalancedChen.Part3.CanonicalHighStripRawEnergy20261026b
