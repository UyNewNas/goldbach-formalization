import ImbalancedChen.Part3CuspCylinderMeasure
import ImbalancedChen.Part3ShiftOneEulerTailSelection
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

An actual native positive-height L2 tail beginning at SOME Y>1, together
with continuity only at positive heights, gives the literal real-carrier
physicalTailMeasure L2 condition used by the Euler-tail classification.
The subtype height-map measure is computed exactly. The missing compact
[1,Y] mass is supplied by continuity and genuine finite compact mass.
The half-open compact piece and closed tail partition the region exactly,
including Y; no boundary point is removed by an AE shortcut.

The native closed tail set below is definitionally the closedHeightTail Y
of the actual infinity Fourier supplier. This module imports no Gamma
Fourier construction and no held constant-mode/Liouville source.
-/

namespace ImbalancedChen.Part3.PhysicalHeightTailMeasureBridge20261026b
noncomputable section
open Set Function Filter MeasureTheory
open CuspCylinderMeasure20261024z
open ShiftOneEulerTailSelection20261026b
attribute [local instance] Measure.Subtype.measureSpace

theorem heightDensity_eq_tailDensity (y : PositiveHeight) :
    heightDensity y = tailDensity (y : ℝ) := by
  apply NNReal.coe_injective
  simp only [heightDensity_coe, tailDensity, one_div]

/-- Exact carrier conversion for the whole positive-height measure. -/
theorem heightMeasure_map_positive :
    Measure.map ((↑) : PositiveHeight → ℝ) heightMeasure =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
        (fun y => (tailDensity y : ℝ≥0∞)) := by
  apply Measure.ext_of_lintegral
  intro q hq
  rw [lintegral_map hq measurable_subtype_coe]
  unfold heightMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
      heightDensity_continuous.measurable.coe_nnreal_ennreal
      (Eventually.of_forall (fun _ => ENNReal.coe_lt_top)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      tailDensity_measurable.coe_nnreal_ennreal
      (Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  rw [← lintegral_subtype_comap measurableSet_Ioi]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun y => by rw [heightDensity_eq_tailDensity]

/-- Exact native open y>1 tail map, with the original real Euler measure. -/
theorem heightMeasure_open_one_map :
    Measure.map ((↑) : PositiveHeight → ℝ)
      (heightMeasure.restrict {y : PositiveHeight | 1 < (y : ℝ)}) =
        physicalTailMeasure := by
  rw [← (MeasurableEmbedding.subtype_coe measurableSet_Ioi).restrict_map
      heightMeasure (Ioi (1 : ℝ)), heightMeasure_map_positive,
    Measure.restrict_withDensity measurableSet_Ioi]
  simp [Measure.restrict_restrict, physicalTailMeasure]

theorem positive_real_ae_eq_height {f g : ℝ → ℂ}
    (h : f =ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] g) :
    (fun y : PositiveHeight => f y) =ᵐ[heightMeasure] (fun y : PositiveHeight => g y) := by
  have hsub := (ae_restrict_iff_subtype measurableSet_Ioi).mp h
  exact hsub.filter_mono (withDensity_absolutelyContinuous
    (volume : Measure PositiveHeight) (fun y => (heightDensity y : ℝ≥0∞))).ae_le

theorem real_positive_volume_ae_eq_height {f g : ℝ → ℂ}
    (h : ∀ᵐ y : ℝ ∂volume, 0 < y → f y = g y) :
    (fun y : PositiveHeight => f y) =ᵐ[heightMeasure] (fun y : PositiveHeight => g y) := by
  apply positive_real_ae_eq_height
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ioi] with y hy hp
  exact hy hp

theorem positive_real_ae_eq_closed_height_tail {f g : ℝ → ℂ} (Y : ℝ)
    (h : f =ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] g) :
    (fun y : PositiveHeight => f y) =ᵐ[
      heightMeasure.restrict {y : PositiveHeight | Y ≤ (y : ℝ)}]
        (fun y : PositiveHeight => g y) :=
  ae_restrict_of_ae (positive_real_ae_eq_height h)

theorem continuous_positive_compact_height_memLp (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi 0)) (l h : PositiveHeight) :
    MemLp (fun y : PositiveHeight => f y) 2 (heightMeasure.restrict (Icc l h)) := by
  have hcont : Continuous (fun y : PositiveHeight => f y) :=
    hf.comp_continuous continuous_subtype_val (fun y => y.property)
  have hK := positiveHeight_Icc_isCompact l h
  letI : IsFiniteMeasure (heightMeasure.restrict (Icc l h)) :=
    ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  apply MemLp.of_bound hcont.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact hC y hy

/-- Main measure/model bridge. The sole L2 premise is the actual native
closed tail beginning at Y; the whole y>1 conclusion is derived. -/
theorem native_closed_height_tail_to_physicalTail (f : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi 0)) (Y : ℝ) (hY : 1 < Y)
    (hTail : MemLp (fun y : PositiveHeight => f y) 2
      (heightMeasure.restrict {y : PositiveHeight | Y ≤ (y : ℝ)})) :
    MemLp f 2 physicalTailMeasure := by
  let l : PositiveHeight := ⟨1, zero_lt_one⟩
  let h : PositiveHeight := ⟨Y, zero_lt_one.trans hY⟩
  have hcompact := continuous_positive_compact_height_memLp f hf l h
  have hhalf : MemLp (fun y : PositiveHeight => f y) 2
      (heightMeasure.restrict (Ico l h)) :=
    hcompact.mono_measure (Measure.restrict_mono_set heightMeasure Ico_subset_Icc_self)
  have hcompactGlobal : MemLp ((Ico l h).indicator (fun y : PositiveHeight => f y))
      2 heightMeasure := (memLp_indicator_iff_restrict measurableSet_Ico).mpr hhalf
  have hclosedMeas : MeasurableSet {y : PositiveHeight | Y ≤ (y : ℝ)} :=
    measurableSet_Ici.preimage measurable_subtype_coe
  have htailGlobal : MemLp
      (({y : PositiveHeight | Y ≤ (y : ℝ)}).indicator (fun y : PositiveHeight => f y))
      2 heightMeasure := (memLp_indicator_iff_restrict hclosedMeas).mpr hTail
  have hsum := (hcompactGlobal.add htailGlobal).restrict {y : PositiveHeight | 1 < (y : ℝ)}
  have heq : ((Ico l h).indicator (fun y : PositiveHeight => f y) +
      ({y : PositiveHeight | Y ≤ (y : ℝ)}).indicator (fun y : PositiveHeight => f y)) =ᵐ[
        heightMeasure.restrict {y : PositiveHeight | 1 < (y : ℝ)}]
      (fun y : PositiveHeight => f y) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioi.preimage measurable_subtype_coe)] with y hy
    by_cases hhigh : Y ≤ (y : ℝ)
    · have hnot : y ∉ Ico l h := fun hh => (not_lt_of_ge hhigh) hh.2
      simp only [Pi.add_apply, indicator_of_notMem hnot, indicator_of_mem hhigh, zero_add]
    · have hmem : y ∈ Ico l h := ⟨hy.le, lt_of_not_ge hhigh⟩
      simp only [Pi.add_apply, indicator_of_mem hmem, indicator_of_notMem hhigh, add_zero]
  have hfull := hsum.congr heq
  rw [← heightMeasure_open_one_map,
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).memLp_map_measure_iff]
  exact hfull

end
end ImbalancedChen.Part3.PhysicalHeightTailMeasureBridge20261026b
