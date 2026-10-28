import ImbalancedChen.P2HistoricalFullSourceRowWitness
import ImbalancedChen.Certificates.P2SemanticGainSetIntegral
import ImbalancedChen.P5OriginalCoefficientArithmetic

/-!
SOURCE ONLY; uncompiled.  All finite source-output/proxy decisions are
reused from the frozen predecessors, never repeated or evaluated here.

The stored lower-estimator loss and the genuine extra Buchstab fibre read
the SAME original dependent Row and exact indices/cutoff.  A projection
lemma identifies their geometric owner without confusing a two-dimensional
saved-floor mask with the four-dimensional fibre.  No count upper bound,
arithmetic parent injection or baseline-mean identity is assumed/proved.
-/

namespace ImbalancedChen.P2ActualSameMaskFloorFibreAccounting

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorSelectedUnion P2HistoricalOrdinaryProxyIntegral
open P2HistoricalOrdinaryProxySourceUpper P2HistoricalDefectClosedProxy
open P2HistoricalFullFloorProxyChain P2HistoricalFullSourceRowWitness
open P2IndependentFullProxyFiniteCertificate
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
open P5OriginalCoefficientArithmetic

def actualStoredLoss : ℝ := ∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4
def actualOrdinaryStoredLoss : ℝ := ∑ r : Row, decodeQ80 (rowOrdinaryOutput actualSf actualLog r) / 4
def actualDefectStoredLoss : ℝ := ∑ r : Row, decodeQ80 (rowDefectCredit actualLog r) / 4

theorem actual_stored_loss_components :
    actualStoredLoss = actualOrdinaryStoredLoss + actualDefectStoredLoss := by
  unfold actualStoredLoss actualOrdinaryStoredLoss actualDefectStoredLoss
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [original_frozen_full_components r, decodeQ80_add]
  ring

theorem actual_stored_minus_defect_eq_ordinary :
    actualStoredLoss - actualDefectStoredLoss = actualOrdinaryStoredLoss := by
  rw [actual_stored_loss_components]
  ring

/-- Direction preserved: saved MINUS its positive defect credit <= the
ordinary upper proxy <= the true ordinary integral. Neither arrow reverses. -/
theorem actual_ordinary_proxy_chain :
    actualStoredLoss - actualDefectStoredLoss ≤ selectedOrdinaryProxy ∧
      selectedOrdinaryProxy ≤ selectedOrdinaryIntegral / 4 := by
  rw [actual_stored_minus_defect_eq_ordinary]
  exact ⟨Finset.sum_le_sum (fun r _hr => actual_saved_ordinary_le_proxy r),
    selectedOrdinaryProxy_le_actual_integral⟩

theorem actual_stored_loss_le_full_proxy : actualStoredLoss ≤ selectedFullProxy :=
  original_stored_sum_le_full_proxy

theorem actual_stored_loss_lt_lambda : actualStoredLoss < (lambda : ℝ) :=
  original_stored_sum_lt_lambda

theorem lambda_eq_original_payment : (lambda : ℝ) = replacementSavedFloorPayment := by
  norm_num [lambda, replacementSavedFloorPayment]

/-- This replacement is an endpoint on the historical saved L6 estimator,
not an identification with an ordinary-only or actual arithmetic L6 mean. -/
def retainedFrozenL6Endpoint : ℝ := savedL6 - 4 * actualStoredLoss

theorem retained_frozen_L6_gt_original_paid_endpoint :
    savedL6 - 4 * replacementSavedFloorPayment < retainedFrozenL6Endpoint := by
  have hl := actual_stored_loss_lt_lambda
  rw [lambda_eq_original_payment] at hl
  unfold retainedFrozenL6Endpoint
  linarith

theorem retained_frozen_L6_gt_original_literal_endpoint :
    1421673188323272382945058469141 / 472236648286964521369600000000 <
      retainedFrozenL6Endpoint := by
  rw [← retained_savedL6_value]
  exact retained_frozen_L6_gt_original_paid_endpoint

theorem currentK_eq_actual_fibre_K : currentK = (Certificates.PairedV2.K : ℝ) := by
  norm_num [currentK, Certificates.PairedV2.K]

theorem same_row_cutoff (r : Row) :
    cutoff r = min (rowUL r) (3 * (1 - rowTR r - rowUR r) / 13) := rfl

/-- Every point of the original actual fibre projects to the floor pair
cell with the SAME owner. Upper-endpoint convention only enlarges that
pair cell; no four-dimensional region is equated with a pair rectangle. -/
theorem same_row_fibre_projects {r : Row} {x : Fin 4 → ℝ}
    (hx : x ∈ Certificates.PairedV2.FullMask.support r) :
    (x 0, x 1) ∈ P2HistoricalSavedFloorSelectedUnion.pairCell r :=
  ⟨⟨hx.1, hx.2.1.le⟩, ⟨hx.2.2.1, hx.2.2.2.1.le⟩⟩

theorem same_mask_fibre_projects {x : Fin 4 → ℝ}
    (hx : x ∈ Certificates.PairedV2.FullMask.region) :
    (x 0, x 1) ∈ selectedPairRegion := by
  obtain ⟨r, hr⟩ := mem_iUnion.mp hx
  exact mem_iUnion.mpr ⟨r, same_row_fibre_projects hr⟩

def constantExtraRow (r : Row) : ℝ :=
  pairedLocalIntegral (Certificates.PairedV2.K : ℝ) Certificates.PairedV2.a
    (rowTL r) (rowTR r) (rowUL r) (rowUR r) (cutoff r)

theorem same_mask_constant_extra_sum :
    (∑ r : Row, constantExtraRow r) = Certificates.PairedV2.FullMask.integral := rfl

/-- Actual omega-minus-half gain on the original four-dimensional union,
with the original K/4 weight and variable triangular inner w endpoint. -/
def actualExtraFibreGain : ℝ := unionSemanticIntegral

theorem actual_extra_eq_new_minus_old_half :
    actualExtraFibreGain = unionBuchstabIntegral - unionHalfBaselineIntegral :=
  unionBuchstabIntegral_sub_halfBaseline.symm

theorem actual_extra_ge_same_row_constant_fibres :
    (∑ r : Row, constantExtraRow r) ≤ actualExtraFibreGain := by
  rw [same_mask_constant_extra_sum,
    ← Certificates.PairedV2.FullMask.P2PairedSupportFubini.unionIntegral_eq_integral]
  exact unionSemanticIntegral_ge_constant

/-- Existing genuine integral/certificate bound, reused rather than a new
finite number or an assumed gain. Its source-only checker chain is held. -/
theorem actual_extra_ge_original_g : extraSameMaskGross ≤ actualExtraFibreGain :=
  unionSemanticIntegral_adopted_lower

/-- New actual local contribution to the OLD endpoint ledger: genuine
same-mask omega gain plus recovery of the overpaid saved-estimator loss. -/
def actualSameMaskIncrement : ℝ :=
  actualExtraFibreGain + (oldSavedFloorPayment - actualStoredLoss)

theorem actual_increment_gt_original_delta : sameMaskIncrement < actualSameMaskIncrement := by
  have hg := actual_extra_ge_original_g
  have hl := actual_stored_loss_lt_lambda
  rw [lambda_eq_original_payment] at hl
  unfold actualSameMaskIncrement sameMaskIncrement
  linarith

/-- Both terms occur once, with no second division by four and no second
addition of either E0/E1 baseline crop or the old saved payment. -/
def refinedSourceEndpoint : ℝ := adoptedAtK0 + baselineContinuation + actualSameMaskIncrement

theorem refined_source_endpoint_original_components :
    refinedSourceEndpoint = adoptedAtK0 + originalFeedbackSlope * (K0 - currentK) +
      table248to312 + table312to430 + E0Gross + E1Gross +
      actualExtraFibreGain - actualStoredLoss := by
  unfold refinedSourceEndpoint baselineContinuation actualSameMaskIncrement
  ring

theorem refined_source_endpoint_gt_adopted : adoptedReconstruction < refinedSourceEndpoint := by
  have h := actual_increment_gt_original_delta
  unfold refinedSourceEndpoint adoptedReconstruction
  linarith

end

end ImbalancedChen.P2ActualSameMaskFloorFibreAccounting
