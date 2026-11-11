import ImbalancedChen.Certificates.P2AdoptedRowsActualEnclosure
import ImbalancedChen.P2PairedBoundaryCollarReserve

/-!
SOURCE ONLY; uncompiled. Reuses the complete 17572-row certificate and
the existing genuine product-volume/Fubini and semantic-gain suppliers.
This is the directed-error consumer for the manuscript paired-v2 gain,
not a new certificate evaluator or a new history/parent licence.

In particular the small certificate width bounds the constant 1/20 gain
minorant, NOT the difference between that minorant and actual Buchstab.
The latter receives only a separate coarse bound from omega <= 1.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedRoundingLedger

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open P2AdoptedRows P2AdoptedUnion P2SemanticGainSetIntegral
open P2PairedSemanticRestrictionError

def lowerEndpoint : ℝ := 55858378943374979 / 100000000000000000000
def upperEndpoint : ℝ := 55858409959907296 / 100000000000000000000
def adoptedFloor : ℝ := 558583 / 1000000000
def enclosureWidth : ℝ := 31016532317 / 100000000000000000000
def roundingReserve : ℝ := 78943374979 / 100000000000000000000

theorem endpoint_width : upperEndpoint - lowerEndpoint = enclosureWidth := by
  norm_num [upperEndpoint, lowerEndpoint, enclosureWidth]

theorem endpoint_rounding_reserve : lowerEndpoint - adoptedFloor = roundingReserve := by
  norm_num [lowerEndpoint, adoptedFloor, roundingReserve]

theorem roundingReserve_pos : 0 < roundingReserve := by
  norm_num [roundingReserve]

/-- The accumulated width is the exact sum of all directed row widths.
No uniform-per-row estimate or sampled subset replaces the adopted mask. -/
theorem sum_row_widths :
    (∑ r : Row, (((makeCertificate r (approximation r)).upper : ℝ) -
      ((makeCertificate r (approximation r)).lower : ℝ))) = enclosureWidth := by
  have hl : (∑ r : Row, ((makeCertificate r (approximation r)).lower : ℝ)) =
      lowerEndpoint := by
    change (∑ r : Row, ((makeCertificate r (approximation r)).lower : ℝ)) =
      (55858378943374979 / 100000000000000000000 : ℝ)
    exact_mod_cast lower_sum
  have hu : (∑ r : Row, ((makeCertificate r (approximation r)).upper : ℝ)) =
      upperEndpoint := by
    change (∑ r : Row, ((makeCertificate r (approximation r)).upper : ℝ)) =
      (55858409959907296 / 100000000000000000000 : ℝ)
    exact_mod_cast upper_sum
  rw [Finset.sum_sub_distrib, hu, hl, endpoint_width]

/-- Both one-sided errors are nonnegative and sum to exactly the stored
width. Integrals are the actual row integrals, not endpoint surrogates. -/
theorem partial_error_accounting (s : Finset Row) :
    0 ≤ (∑ r ∈ s, gridIntegral (indices r) -
      ((makeCertificate r (approximation r)).lower : ℝ)) ∧
    0 ≤ (∑ r ∈ s, ((makeCertificate r (approximation r)).upper : ℝ) -
      gridIntegral (indices r)) ∧
    (∑ r ∈ s, gridIntegral (indices r) -
      ((makeCertificate r (approximation r)).lower : ℝ)) +
      (∑ r ∈ s, ((makeCertificate r (approximation r)).upper : ℝ) -
      gridIntegral (indices r)) =
      ∑ r ∈ s, (((makeCertificate r (approximation r)).upper : ℝ) -
        ((makeCertificate r (approximation r)).lower : ℝ)) := by
  refine ⟨Finset.sum_nonneg (fun r _ => sub_nonneg.mpr (row_actual_enclosure r).1),
    Finset.sum_nonneg (fun r _ => sub_nonneg.mpr (row_actual_enclosure r).2), ?_⟩
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The exact global width encloses the genuine normalized union integral. -/
theorem union_rounding_error :
    roundingReserve ≤ unionIntegral - adoptedFloor ∧
      unionIntegral - adoptedFloor ≤ roundingReserve + enclosureWidth := by
  have hl : lowerEndpoint ≤ unionIntegral := P2PairedSupportFubini.union_actual_enclosure.1
  have hu : unionIntegral ≤ upperEndpoint := P2PairedSupportFubini.union_actual_enclosure.2
  have hw := endpoint_width
  have hr := endpoint_rounding_reserve
  constructor <;> linarith

/-- A coarse actual-Buchstab upper bound, deliberately NOT the narrow
certificate upper endpoint: omega-1/2 <= 1/2 gives factor ten. -/
theorem semanticKernel_le_ten_certificate {x : Point} (hx : x ∈ region) :
    semanticKernel x ≤ 10 * (((K : ℝ) / 80) * rawKernel x) := by
  have hg := mul_le_mul_of_nonneg_left (region_gain_le_half hx)
    (region_weight_nonneg hx)
  change weight x * gain x ≤ weight x * (1 / 2) at hg
  change weight x * gain x ≤ _
  calc
    _ ≤ weight x * (1 / 2) := hg
    _ = _ := by rw [weight_eq_raw]; ring

theorem unionSemanticIntegral_le_ten :
    unionSemanticIntegral ≤ 10 * unionIntegral := by
  have h := setIntegral_mono_on integrableOn_semanticKernel_region
    ((integrableOn_region.const_mul ((K : ℝ) / 80)).const_mul 10)
    region_measurable (fun x hx => semanticKernel_le_ten_certificate hx)
  simpa only [unionIntegral, unionSemanticIntegral, integral_const_mul] using h

/-- A rational enclosure for the actual semantic gain, with its honestly
coarse upper side. This is a lower-ledger paired input, not an All22
upper-policy saving or a licence to charge the same mass again. -/
theorem actual_semantic_enclosure :
    lowerEndpoint ≤ unionSemanticIntegral ∧
      unionSemanticIntegral ≤ 10 * upperEndpoint := by
  refine ⟨unionSemanticIntegral_lower, ?_⟩
  exact unionSemanticIntegral_le_ten.trans
    (mul_le_mul_of_nonneg_left P2PairedSupportFubini.union_actual_enclosure.2 (by norm_num))

/-- The literal safe decimal survives restriction whenever the genuine
omitted-volume loss fits the proved rounding reserve. No historical
containment or numerical volume estimate is silently assumed. -/
theorem retained_adopted_floor_of_volume_reserve {s : Set Point}
    (hs : MeasurableSet s) (hsub : s ⊆ region)
    (hbudget : densityBound * (volume (removed s)).toReal ≤ roundingReserve) :
    adoptedFloor ≤ retainedGain s := by
  have h := retainedGain_original_lower_sub_error hs hsub
  change lowerEndpoint - densityBound * (volume (removed s)).toReal ≤ retainedGain s at h
  have hr := endpoint_rounding_reserve
  linarith

/-- There is a positive seven-wall buffer retaining the manuscript's
rounded gain strictly. Reuses the proved collar limit; no rate or parent
licence is manufactured, and none of the saved87 obligations is replaced. -/
theorem exists_positive_buffer_above_adopted_floor :
    ∃ δ : ℝ, 0 < δ ∧
      adoptedFloor < retainedGain (P2PairedBoundaryCollarReserve.shrunkRegion δ) := by
  obtain ⟨δ, hδ, hret⟩ :=
    P2PairedBoundaryCollarReserve.exists_positive_buffer_retained_lower
      (half_pos roundingReserve_pos)
  refine ⟨δ, hδ, ?_⟩
  change lowerEndpoint - roundingReserve / 2 ≤ _ at hret
  have hr := endpoint_rounding_reserve
  have hp := roundingReserve_pos
  linarith

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedRoundingLedger
