import ImbalancedChen.Certificates.P2SemanticGainSetIntegral
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds

/-!
SOURCE ONLY; uncompiled. The semantic set-integral supplier is the adjacent
candidate. Its generic coordinate-Fubini dependency was read on disk and
has exactly the API used in that candidate.

The density majorant is explicit: (K/8)/a^5. It comes from the actual pinned
Buchstab upper bound omega <= 1 on arguments >= 1, the true paired argument
>= 7/3, and the original positive denominator cutoff a. The pinned supplier
is goldbach 09b97db5764ade1246bfb77206baa1b124760958,
MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.lean, buchstab_le_one.

For any measurable retained subset of the original adopted region, the
loss is exactly the integral on the omitted set, and its upper bound uses
only the volume of that actual omitted set. No parent retention, domain
equality, gain dominance, or final lower bound is an input premise.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError

noncomputable section

open MeasureTheory Set
open P2HistoricalFibreBinding P2AdoptedUnion P2SemanticGainSetIntegral

/-- Explicit majorant for the actual semantic density on FullMask.region. -/
def densityBound : ℝ := ((K : ℝ) / 8) / (a : ℝ) ^ 5

theorem densityBound_nonneg : 0 ≤ densityBound := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := by norm_num [K]
  have ha : (0 : ℝ) < (a : ℝ) := a_pos
  unfold densityBound
  positivity

theorem densityBound_explicit : densityBound =
    ((8452171 / 1250000 : ℝ) / 8) / (417 / 5000 : ℝ) ^ 5 := by
  norm_num [densityBound, K, a]

theorem region_gain_le_half {x : Point} (hx : x ∈ region) : gain x ≤ 1 / 2 := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  have harg : (7 / 3 : ℝ) ≤
      (1 - x 0 - x 1 - x 2 - x 3) / x 2 :=
    (row_fibre_argument r hr).2.2.2.2.2.2
  have hb := LiLiuPrereqBuchstab.buchstab_le_one
    (show (1 : ℝ) ≤ (1 - x 0 - x 1 - x 2 - x 3) / x 2 by linarith)
  unfold gain pairedSemanticBuchstabGain
  linarith

theorem region_weight_nonneg {x : Point} (hx : x ∈ region) : 0 ≤ weight x := by
  rw [weight_eq_raw]
  have hK : (0 : ℝ) ≤ (K : ℝ) / 4 := by norm_num [K]
  exact mul_nonneg hK (rawKernel_nonneg (region_subset_box hx))

/-- Actual omega, original K/4 weight, and positive a denominators give the
explicit pointwise bound without a numerical sampling assertion. -/
theorem region_semanticKernel_le {x : Point} (hx : x ∈ region) :
    semanticKernel x ≤ densityBound := by
  have hraw := rawKernel_le (region_subset_box hx)
  have hK : (0 : ℝ) ≤ (K : ℝ) / 4 := by norm_num [K]
  calc
    semanticKernel x = weight x * gain x := rfl
    _ ≤ weight x * (1 / 2) :=
      mul_le_mul_of_nonneg_left (region_gain_le_half hx) (region_weight_nonneg hx)
    _ = ((K : ℝ) / 4 * rawKernel x) * (1 / 2) := by rw [weight_eq_raw]
    _ ≤ ((K : ℝ) / 4 * (1 / (a : ℝ) ^ 5)) * (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hraw hK) (by norm_num)
    _ = densityBound := by unfold densityBound; ring

theorem region_semanticKernel_norm_le {x : Point} (hx : x ∈ region) :
    ‖semanticKernel x‖ ≤ densityBound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (semanticKernel_nonneg_region hx)]
  exact region_semanticKernel_le hx

/-- The omitted set is geometrically observable; its definition makes no
assumption about how a historical arithmetic parent was constructed. -/
def removed (s : Set Point) : Set Point := region \ s

def retainedGain (s : Set Point) : ℝ := ∫ x : Point in s, semanticKernel x

def lostGain (s : Set Point) : ℝ := ∫ x : Point in removed s, semanticKernel x

theorem removed_measurable {s : Set Point} (hs : MeasurableSet s) :
    MeasurableSet (removed s) := region_measurable.diff hs

theorem removed_subset_region (s : Set Point) : removed s ⊆ region := sdiff_subset

theorem removed_volume_lt_top (s : Set Point) : volume (removed s) < ∞ := by
  have hb : volume box < ∞ := isCompact_Icc.measure_lt_top
  exact (measure_mono ((removed_subset_region s).trans region_subset_box)).trans_lt hb

theorem integrableOn_removed (s : Set Point) :
    IntegrableOn semanticKernel (removed s) (volume : Measure Point) :=
  integrableOn_semanticKernel_region.mono_set (removed_subset_region s)

theorem integrableOn_retained {s : Set Point} (hsub : s ⊆ region) :
    IntegrableOn semanticKernel s (volume : Measure Point) :=
  integrableOn_semanticKernel_region.mono_set hsub

/-- Exact full-minus-retained identity, with all integrability discharged. -/
theorem full_sub_retained_eq_lost {s : Set Point} (hs : MeasurableSet s)
    (hsub : s ⊆ region) : unionSemanticIntegral - retainedGain s = lostGain s := by
  exact (setIntegral_sdiff hs integrableOn_semanticKernel_region hsub).symm

theorem lostGain_nonneg {s : Set Point} (hs : MeasurableSet s) : 0 ≤ lostGain s := by
  exact setIntegral_nonneg (removed_measurable hs)
    (fun x hx => semanticKernel_nonneg_region ((removed_subset_region s) hx))

/-- Explicit upper bound using only the actual omitted volume. The finite
measure hypothesis is proved from the genuine common compact box. -/
theorem lostGain_le_volume (s : Set Point) :
    lostGain s ≤ densityBound * (volume (removed s)).toReal := by
  have h := norm_setIntegral_le_of_norm_le_const (removed_volume_lt_top s)
    (fun x hx => region_semanticKernel_norm_le ((removed_subset_region s) hx))
  change ‖lostGain s‖ ≤ densityBound * (volume (removed s)).toReal at h
  exact (le_abs_self (lostGain s)).trans (by simpa only [Real.norm_eq_abs] using h)

theorem lostGain_bounds {s : Set Point} (hs : MeasurableSet s) :
    0 ≤ lostGain s ∧ lostGain s ≤ densityBound * (volume (removed s)).toReal :=
  ⟨lostGain_nonneg hs, lostGain_le_volume s⟩

theorem retainedGain_le_full {s : Set Point} (hs : MeasurableSet s)
    (hsub : s ⊆ region) : retainedGain s ≤ unionSemanticIntegral := by
  have he := full_sub_retained_eq_lost hs hsub
  have hp := lostGain_nonneg hs
  linarith

theorem retainedGain_ge_full_sub_error {s : Set Point} (hs : MeasurableSet s)
    (hsub : s ⊆ region) :
    unionSemanticIntegral - densityBound * (volume (removed s)).toReal ≤ retainedGain s := by
  have he := full_sub_retained_eq_lost hs hsub
  have hb := lostGain_le_volume s
  linarith

/-- The unchanged rational lower endpoint is reduced by a proved explicit
geometric loss term; full gain is never assumed to survive restriction. -/
theorem retainedGain_original_lower_sub_error {s : Set Point} (hs : MeasurableSet s)
    (hsub : s ⊆ region) :
    (55858378943374979 / 100000000000000000000 : ℝ) -
      densityBound * (volume (removed s)).toReal ≤ retainedGain s := by
  have hfull := unionSemanticIntegral_lower
  have he := retainedGain_ge_full_sub_error hs hsub
  linarith

/-- A supplied volume reserve is an observable geometric input, rather
than a premise asserting retained gain or arithmetic parent ownership. -/
theorem retainedGain_lower_of_volume_reserve {s : Set Point} (hs : MeasurableSet s)
    (hsub : s ⊆ region) {ε : ℝ} (hvol : (volume (removed s)).toReal ≤ ε) :
    (55858378943374979 / 100000000000000000000 : ℝ) - densityBound * ε ≤
      retainedGain s := by
  have hm := mul_le_mul_of_nonneg_left hvol densityBound_nonneg
  have hr := retainedGain_original_lower_sub_error hs hsub
  linarith

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError
