import ImbalancedChen.Part3CommonHeightSmoothApproximation
import ImbalancedChen.Part3CuspCylinderMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The common-height approximation is instantiated with the ACTUAL dy/y^2
and dy measures on PositiveHeight. Both restricted measures are mapped to
the real line on a larger positive compact interval; hence they are finite
and pinned smooth Lp density applies to their sum. The common cutoff
forces every approximant back into that same interval. Indicator identities
then remove the restriction and give both full physical L2 errors.
There is no height-density, representative-join, or hApprox premise.
-/

namespace ImbalancedChen.Part3.PhysicalHeightCommonSmoothing20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CommonHeightSmoothApproximation20261026b
attribute [local instance] Measure.Subtype.measureSpace

local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance

def extendHeight (f : PositiveHeight → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then f ⟨y, hy⟩ else 0

@[simp] theorem extendHeight_coe (f : PositiveHeight → ℂ) (y : PositiveHeight) :
    extendHeight f (y : ℝ) = f y := by simp [extendHeight, y.property]

def outerBand (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : Set PositiveHeight :=
  Icc ⟨a / 2, by positivity⟩ ⟨b + a / 2, by linarith⟩

theorem outerBand_compact (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IsCompact (outerBand a b ha hab) := positiveHeight_Icc_isCompact _ _

theorem outerBand_measurable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    MeasurableSet (outerBand a b ha hab) := measurableSet_Icc

theorem originalBand_subset_outerBand {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {y : PositiveHeight} (hy : a ≤ (y : ℝ) ∧ (y : ℝ) ≤ b) :
    y ∈ outerBand a b ha hab := by
  constructor <;> change _ ≤ _ <;> linarith [hy.1, hy.2]

theorem extendHeight_support {a b : ℝ} {f : PositiveHeight → ℂ}
    (hs : Function.support f ⊆ {y | a ≤ (y : ℝ) ∧ (y : ℝ) ≤ b}) :
    Function.support (extendHeight f) ⊆ Icc a b := by
  intro y hy
  by_cases hp : 0 < y
  · exact hs (by simpa only [extendHeight, dif_pos hp] using hy)
  · exact False.elim (hy (by simp [extendHeight, hp]))

theorem indicator_eq_of_support_subset {α : Type*} {s : Set α} {f : α → ℂ}
    (hs : Function.support f ⊆ s) : s.indicator f = f := by
  funext x
  by_cases hx : x ∈ s
  · simp [hx]
  · have hf : f x = 0 := by
      by_contra h
      exact hx (hs h)
    simp [hx, hf]

theorem eLpNorm_eq_restrict_of_support_subset {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hsm : MeasurableSet s) {f : α → ℂ}
    (hs : Function.support f ⊆ s) :
    eLpNorm f 2 μ = eLpNorm f 2 (μ.restrict s) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hsm, indicator_eq_of_support_subset hs]

theorem memLp_of_restrict_of_support_subset {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hsm : MeasurableSet s) {f : α → ℂ}
    (hs : Function.support f ⊆ s) (hf : MemLp f 2 (μ.restrict s)) : MemLp f 2 μ := by
  have h := (memLp_indicator_iff_restrict hsm).mpr hf
  rwa [indicator_eq_of_support_subset hs] at h

theorem support_sub_subset {α : Type*} {s : Set α} {f g : α → ℂ}
    (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s) :
    Function.support (f - g) ⊆ s := by
  intro x hx
  by_contra hs
  have hf0 : f x = 0 := by by_contra h; exact hs (hf h)
  have hg0 : g x = 0 := by by_contra h; exact hs (hg h)
  exact hx (by simp [hf0, hg0])

def bandRealMeasure (μ : Measure PositiveHeight) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) : Measure ℝ :=
  Measure.map ((↑) : PositiveHeight → ℝ) (μ.restrict (outerBand a b ha hab))

instance bandRealMeasure_finite (μ : Measure PositiveHeight)
    [IsFiniteMeasureOnCompacts μ] (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IsFiniteMeasure (bandRealMeasure μ a b ha hab) := by
  haveI : IsFiniteMeasure (μ.restrict (outerBand a b ha hab)) :=
    ⟨by simpa using (outerBand_compact a b ha hab).measure_lt_top⟩
  unfold bandRealMeasure
  infer_instance

theorem extendHeight_memLp_band {μ : Measure PositiveHeight} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {f : PositiveHeight → ℂ} (hf : MemLp f 2 μ) :
    MemLp (extendHeight f) 2 (bandRealMeasure μ a b ha hab) := by
  rw [bandRealMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Ioi).memLp_map_measure_iff]
  simpa only [Function.comp_def, extendHeight_coe] using
    hf.mono_measure (Measure.restrict_le_self (s := outerBand a b ha hab))

theorem real_error_eq_restricted_error {μ : Measure PositiveHeight} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (f : PositiveHeight → ℂ) (g : ℝ → ℂ) :
    eLpNorm (extendHeight f - g) 2 (bandRealMeasure μ a b ha hab) =
      eLpNorm (fun y : PositiveHeight => f y - g (y : ℝ)) 2
        (μ.restrict (outerBand a b ha hab)) := by
  rw [bandRealMeasure, (MeasurableEmbedding.subtype_coe measurableSet_Ioi).eLpNorm_map_measure]
  simp only [Function.comp_def, Pi.sub_apply, extendHeight_coe]

theorem real_band_memLp_restrict {μ : Measure PositiveHeight} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) {g : ℝ → ℂ}
    (hg : MemLp g 2 (bandRealMeasure μ a b ha hab)) :
    MemLp (fun y : PositiveHeight => g (y : ℝ)) 2
      (μ.restrict (outerBand a b ha hab)) := by
  have h := hg.comp_of_map
    (show AEMeasurable ((↑) : PositiveHeight → ℝ)
      (μ.restrict (outerBand a b ha hab)) from measurable_subtype_coe.aemeasurable)
  exact h

/-- Actual physical height density, for all coefficients simultaneously.
The sequence is common, C-infinity on the real line, and contained in
[a/2,b+a/2] at every step. Both errors use full PositiveHeight measures. -/
theorem exists_physical_common_height_sequence {ι : Type*} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (f : ι → PositiveHeight → ℂ)
    (hw : ∀ i, MemLp (f i) 2 heightMeasure)
    (hr : ∀ i, MemLp (f i) 2 (volume : Measure PositiveHeight))
    (hs : ∀ i, Function.support (f i) ⊆
      {y | a ≤ (y : ℝ) ∧ (y : ℝ) ≤ b}) :
    ∃ g : ℕ → ι → ℝ → ℂ, ∀ n i,
      ContDiff ℝ ∞ (g n i) ∧ HasCompactSupport (g n i) ∧
      tsupport (g n i) ⊆ Icc (a / 2) (b + a / 2) ∧
      MemLp (fun y : PositiveHeight => g n i (y : ℝ)) 2 heightMeasure ∧
      MemLp (fun y : PositiveHeight => g n i (y : ℝ)) 2
        (volume : Measure PositiveHeight) ∧
      eLpNorm (fun y : PositiveHeight => f i y - g n i (y : ℝ)) 2 heightMeasure ≤
        ENNReal.ofReal (tolerance n) ∧
      eLpNorm (fun y : PositiveHeight => f i y - g n i (y : ℝ)) 2
        (volume : Measure PositiveHeight) ≤ ENNReal.ofReal (tolerance n) := by
  let μ := bandRealMeasure heightMeasure a b ha hab
  let ν := bandRealMeasure (volume : Measure PositiveHeight) a b ha hab
  obtain ⟨g, hg⟩ := exists_common_height_sequence μ ν ha hab
    (fun i => extendHeight (f i))
    (fun i => extendHeight_memLp_band ha hab (hw i))
    (fun i => extendHeight_memLp_band ha hab (hr i))
    (fun i => extendHeight_support (hs i))
  refine ⟨g, fun n i => ?_⟩
  obtain ⟨hgs, hgc, hgt, hgw, hgr⟩ := hg n i
  have hgb : tsupport (g n i) ⊆ Icc (a / 2) (b + a / 2) :=
    hgt.trans (bandCutoff_tsupport_band a b ha hab)
  have hsupport : Function.support (fun y : PositiveHeight => g n i (y : ℝ)) ⊆
      outerBand a b ha hab := fun y hy => hgb (subset_tsupport _ hy)
  have hfsupport : Function.support (f i) ⊆ outerBand a b ha hab :=
    fun y hy => originalBand_subset_outerBand ha hab (hs i hy)
  have hdiff := support_sub_subset hfsupport hsupport
  have hm (κ : Measure PositiveHeight) [IsFiniteMeasureOnCompacts κ] :
      MemLp (fun y : PositiveHeight => g n i (y : ℝ)) 2 κ := by
    apply memLp_of_restrict_of_support_subset (outerBand_measurable a b ha hab) hsupport
    exact real_band_memLp_restrict ha hab
      (hgs.continuous.memLp_of_hasCompactSupport hgc)
  refine ⟨hgs, hgc, hgb, hm heightMeasure, hm volume, ?_, ?_⟩
  · rw [eLpNorm_eq_restrict_of_support_subset (outerBand_measurable a b ha hab) hdiff]
    exact (real_error_eq_restricted_error ha hab (f i) (g n i)) ▸ hgw
  · rw [eLpNorm_eq_restrict_of_support_subset (outerBand_measurable a b ha hab) hdiff]
    exact (real_error_eq_restricted_error ha hab (f i) (g n i)) ▸ hgr

end
end ImbalancedChen.Part3.PhysicalHeightCommonSmoothing20261026b
