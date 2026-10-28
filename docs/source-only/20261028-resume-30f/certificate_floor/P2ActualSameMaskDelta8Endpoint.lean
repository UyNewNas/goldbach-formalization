import ImbalancedChen.P2ActualSameMaskFloorFibreAccounting
import ImbalancedChen.P2PairedBoundaryCollarReserve

/-!
SOURCE ONLY; uncompiled.  Attach the original delta/8 bookkeeping and
current-c rational chain to the actual stored loss and actual same-mask
Buchstab gain, rather than to an unrelated pair of numbers.

One actual positive collar is constructed within one extra allowance.
The second allowance is still BOOKED, not a proved bound on an arithmetic
compiler/count error.  Neither this file nor the numerical baseline ledger
identifies the endpoint expression with an actual Chen mean or count.
-/

namespace ImbalancedChen.P2ActualSameMaskDelta8Endpoint

noncomputable section

open MeasureTheory Set
open P5OriginalCoefficientArithmetic P2ActualSameMaskFloorFibreAccounting
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
open Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError
open Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve

def extraReserve : ℝ := sameMaskIncrement / 8
def bookedNetDelta : ℝ := sameMaskIncrement - 2 * extraReserve
def originalEndpointSlack : ℝ := adoptedReconstruction - 2 * eachReserve - currentC

theorem original_loss_recovery_value :
    oldSavedFloorPayment - replacementSavedFloorPayment = 37209 / 1000000000 := by
  norm_num [oldSavedFloorPayment, replacementSavedFloorPayment]

theorem original_delta_value : sameMaskIncrement = 37237 / 62500000 :=
  sameMaskIncrement_value

theorem extraReserve_value : extraReserve = 37237 / 500000000 := by
  unfold extraReserve
  rw [sameMaskIncrement_value]
  norm_num

theorem extraReserve_pos : 0 < extraReserve := by rw [extraReserve_value]; norm_num

theorem original_eachReserve_eq : eachReserve = baselineReserve + extraReserve := rfl

theorem bookedNetDelta_value : bookedNetDelta = 111711 / 250000000 := by
  unfold bookedNetDelta
  rw [sameMaskIncrement_value, extraReserve_value]
  norm_num

theorem bookedNetDelta_eq_three_quarters : bookedNetDelta = 3 * sameMaskIncrement / 4 := by
  unfold bookedNetDelta extraReserve
  ring

theorem actual_increment_after_booked_reserves_gt_net :
    bookedNetDelta < actualSameMaskIncrement - 2 * extraReserve := by
  have h := actual_increment_gt_original_delta
  unfold bookedNetDelta
  linarith

/-- Same original cutoff walls and actual Buchstab density, after the
proved inward geometric collar restriction.  No arithmetic parent or
modulus-wall payment is silently supplied by this definition. -/
def bufferedActualIncrement (δ : ℝ) : ℝ :=
  retainedGain (shrunkRegion δ) + (oldSavedFloorPayment - actualStoredLoss)

def bufferedSourceEndpoint (δ : ℝ) : ℝ :=
  adoptedAtK0 + baselineContinuation + bufferedActualIncrement δ

/-- The first delta/8 is paid by a PROVED actual integral loss, not by an
assumed retained-gain bound. The remaining delta/8 is shown explicitly. -/
theorem exists_positive_collar_net_room :
    ∃ δ : ℝ, 0 < δ ∧ bookedNetDelta < bufferedActualIncrement δ - extraReserve := by
  obtain ⟨δ, hδ, hloss⟩ := exists_positive_buffer_loss_le extraReserve_pos
  have he := full_sub_retained_eq_lost (shrunkRegion_measurable δ)
    (shrunkRegion_subset_region hδ.le)
  have hretain : actualSameMaskIncrement - extraReserve ≤ bufferedActualIncrement δ := by
    dsimp [actualSameMaskIncrement, actualExtraFibreGain, bufferedActualIncrement]
    linarith
  have hraw := actual_increment_gt_original_delta
  refine ⟨δ, hδ, ?_⟩
  unfold bookedNetDelta
  linarith

/-- Exact arithmetic on the ORIGINAL complete endpoint ledger.  The
baseline continuation's E0/E1 crop and old payment each occur once. -/
theorem source_endpoint_net_change_exact :
    (refinedSourceEndpoint - 2 * eachReserve) -
      (adoptedAtK0 + baselineContinuation - 2 * baselineReserve) =
        actualSameMaskIncrement - 2 * extraReserve := by
  unfold refinedSourceEndpoint eachReserve extraReserve
  ring

theorem original_endpoint_net_change_exact :
    (adoptedReconstruction - 2 * eachReserve) -
      (adoptedAtK0 + baselineContinuation - 2 * baselineReserve) = bookedNetDelta := by
  unfold adoptedReconstruction eachReserve bookedNetDelta extraReserve
  ring

theorem source_endpoint_after_reserves_gt_original :
    adoptedReconstruction - 2 * eachReserve < refinedSourceEndpoint - 2 * eachReserve := by
  have h := refined_source_endpoint_gt_adopted
  linarith

theorem originalEndpointSlack_value :
    originalEndpointSlack =
      13457260926863633771775678584711245753 /
        2742952509978644604793778369418231808000000000 :=
  exact_currentC_slack

theorem originalEndpointSlack_pos : 0 < originalEndpointSlack := by
  have h := currentC_lt_adopted_after_reserves
  unfold originalEndpointSlack
  linarith

theorem originalEndpointSlack_gt_displayed_safe_margin :
    (49061 / 10000000000000 : ℝ) < originalEndpointSlack := by
  rw [originalEndpointSlack_value]
  norm_num

/-- Genuine new local source objects have strictly more endpoint room than
the old adopted reconstruction. This is NOT a theorem about D12 or a mean. -/
theorem original_currentC_and_slack_lt_source_endpoint :
    currentC + originalEndpointSlack < refinedSourceEndpoint - 2 * eachReserve := by
  have h := source_endpoint_after_reserves_gt_original
  unfold originalEndpointSlack
  linarith

theorem source_endpoint_after_reserves_gt_currentC :
    currentC < refinedSourceEndpoint - 2 * eachReserve := by
  have h := original_currentC_and_slack_lt_source_endpoint
  have hp := originalEndpointSlack_pos
  linarith

theorem source_endpoint_after_reserves_gt_original_c_literal :
    (49044063 / 25000000 : ℝ) < refinedSourceEndpoint - 2 * eachReserve :=
  source_endpoint_after_reserves_gt_currentC

/-- After spending one extra reserve through the actual collar, subtract
only the REMAINING extra reserve. Subtracting both again would double-pay
the collar. Both original baseline reserves are retained exactly once. -/
theorem exists_positive_collar_currentC_endpoint_room :
    ∃ δ : ℝ, 0 < δ ∧ currentC + originalEndpointSlack <
      bufferedSourceEndpoint δ - 2 * baselineReserve - extraReserve := by
  obtain ⟨δ, hδ, hnet⟩ := exists_positive_collar_net_room
  have he := original_endpoint_net_change_exact
  refine ⟨δ, hδ, ?_⟩
  dsimp [bufferedSourceEndpoint]
  unfold originalEndpointSlack
  linarith

end

end ImbalancedChen.P2ActualSameMaskDelta8Endpoint
