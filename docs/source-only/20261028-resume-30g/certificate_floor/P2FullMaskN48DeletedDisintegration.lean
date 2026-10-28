import ImbalancedChen.P2FullMaskN48DeletedOwner
import ImbalancedChen.P2ActualSameMaskDelta8Endpoint

/-!
SOURCE ONLY; uncompiled.  Genuine intersection disintegration of the
same17572 deleted fibres by their archived n48 FULL parents.  Both the
fine/coarse row measures and all empty intersections are retained.

The parent archive/key/incidence decisions remain unexecuted proposals.
No old parent saving-floor licence, true baseline mean or arithmetic
reserve cost is inferred from geometric coverage or method0 metadata.
-/

namespace ImbalancedChen.P2FullMaskN48DeletedDisintegration

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2N48ActualSixteenCostRowAttachment P2FullMaskN48DeletedOwner
open P2ActualSameMaskFloorFibreAccounting P2ActualSameMaskDelta8Endpoint
open P5OriginalCoefficientArithmetic
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
open Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError
open Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve

def archivedPiece (r : Row) (s : ArchivedRow) : Set (Fin 4 → ℝ) :=
  FullMask.support r ∩ fullParent s.val

def archivedPieceGain (r : Row) (s : ArchivedRow) : ℝ :=
  ∫ x in archivedPiece r s, semanticKernel x

theorem archivedPiece_measurable (r : Row) (s : ArchivedRow) :
    MeasurableSet (archivedPiece r s) :=
  (P2AdoptedUnion.support_measurable r).inter (measurableSet_fullParent s.val)

theorem support_eq_archived_union (r : Row) :
    FullMask.support r = ⋃ s : ArchivedRow, archivedPiece r s := by
  ext x
  constructor
  · intro hf
    obtain ⟨s, hs⟩ := exists_archived_full_parent hf
    exact mem_iUnion.mpr ⟨s, hf, hs⟩
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact hs.1

theorem archivedPieces_pairwise_disjoint (r : Row) :
    Pairwise (fun s t : ArchivedRow => Disjoint (archivedPiece r s) (archivedPiece r t)) := by
  intro s t hne
  apply Set.disjoint_left.mpr
  intro x hs ht
  exact hne (archived_full_parent_unique hs.2 ht.2)

theorem integrable_semantic_archivedPiece (r : Row) (s : ArchivedRow) :
    IntegrableOn semanticKernel (archivedPiece r s) :=
  (integrableOn_semanticKernel_support r).mono_set (fun _ hx => hx.1)

theorem support_integral_eq_archived_sum (r : Row) :
    (∫ x in FullMask.support r, semanticKernel x) = ∑ s : ArchivedRow, archivedPieceGain r s := by
  rw [support_eq_archived_union r]
  exact integral_iUnion_fintype (archivedPiece_measurable r) (archivedPieces_pairwise_disjoint r)
    (integrable_semantic_archivedPiece r)

/-- The true omega-minus-half gain, with original quarter weight, equals
the actual fine-row/coarse-source intersection matrix. No row-to-one-parent
map, independent-volume surrogate or parent density premise is used. -/
theorem actual_gain_eq_row_parent_sum :
    actualExtraFibreGain = ∑ r : Row, ∑ s : ArchivedRow, archivedPieceGain r s := by
  unfold actualExtraFibreGain
  rw [unionSemanticIntegral_eq_sum]
  exact Finset.sum_congr rfl (fun r _hr => support_integral_eq_archived_sum r)

def archivedExtraCoefficient : ℝ := ∑ s : ArchivedRow, ∑ r : Row, archivedPieceGain r s

theorem actual_gain_eq_archived_coefficient : actualExtraFibreGain = archivedExtraCoefficient := by
  rw [actual_gain_eq_row_parent_sum]
  exact Finset.sum_comm

def collaredArchivedPiece (δ : ℝ) (r : Row) (s : ArchivedRow) : Set (Fin 4 → ℝ) :=
  shrunkSupport r δ ∩ fullParent s.val

theorem collaredArchivedPiece_measurable (δ : ℝ) (r : Row) (s : ArchivedRow) :
    MeasurableSet (collaredArchivedPiece δ r s) :=
  (shrunkSupport_isOpen r δ).measurableSet.inter (measurableSet_fullParent s.val)

theorem shrunk_support_eq_archived_union (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    shrunkSupport r δ = ⋃ s : ArchivedRow, collaredArchivedPiece δ r s := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := exists_archived_full_parent (shrunkSupport_subset_support r hδ hx)
    exact mem_iUnion.mpr ⟨s, hx, hs⟩
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact hs.1

theorem collaredArchivedPieces_pairwise_disjoint (δ : ℝ) (r : Row) :
    Pairwise (fun s t : ArchivedRow =>
      Disjoint (collaredArchivedPiece δ r s) (collaredArchivedPiece δ r t)) := by
  intro s t hne
  apply Set.disjoint_left.mpr
  intro x hs ht
  exact hne (archived_full_parent_unique hs.2 ht.2)

theorem shrunk_support_integral_eq_archived_sum (r : Row) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ x in shrunkSupport r δ, semanticKernel x) =
      ∑ s : ArchivedRow, ∫ x in collaredArchivedPiece δ r s, semanticKernel x := by
  rw [shrunk_support_eq_archived_union r hδ]
  apply integral_iUnion_fintype (collaredArchivedPiece_measurable δ r)
    (collaredArchivedPieces_pairwise_disjoint δ r)
  intro s
  exact (integrableOn_semanticKernel_support r).mono_set
    (fun _ hx => shrunkSupport_subset_support r hδ hx.1)

/-- The very same positive collar is disintegrated by the same full source
parents. Thus a geometric reserve is not paid again after reindexing. -/
theorem retained_gain_eq_collared_archived_sum {δ : ℝ} (hδ : 0 ≤ δ) :
    retainedGain (shrunkRegion δ) =
      ∑ s : ArchivedRow, ∑ r : Row, ∫ x in collaredArchivedPiece δ r s, semanticKernel x := by
  have hdisj : Pairwise (fun r q : Row => Disjoint (shrunkSupport r δ) (shrunkSupport q δ)) := by
    intro r q hrq
    exact (FullMask.supports_pairwise_disjoint hrq).mono
      (shrunkSupport_subset_support r hδ) (shrunkSupport_subset_support q hδ)
  have hi (r : Row) : IntegrableOn semanticKernel (shrunkSupport r δ) :=
    (integrableOn_semanticKernel_support r).mono_set (shrunkSupport_subset_support r hδ)
  unfold retainedGain shrunkRegion
  rw [integral_iUnion_fintype (fun r => (shrunkSupport_isOpen r δ).measurableSet) hdisj hi]
  simp_rw [shrunk_support_integral_eq_archived_sum _ hδ]
  exact Finset.sum_comm

theorem actual_increment_eq_archived_source :
    actualSameMaskIncrement = archivedExtraCoefficient + (oldSavedFloorPayment - actualStoredLoss) := by
  unfold actualSameMaskIncrement
  rw [actual_gain_eq_archived_coefficient]

theorem refined_endpoint_eq_archived_source :
    refinedSourceEndpoint = adoptedAtK0 + baselineContinuation +
      archivedExtraCoefficient + (oldSavedFloorPayment - actualStoredLoss) := by
  unfold refinedSourceEndpoint
  rw [actual_increment_eq_archived_source]
  ring

/-- Local SOURCE ENDPOINT arithmetic only. The baseline ledger has not
become an actual mean, nor has an old saving floor acquired a licence. -/
theorem archived_source_endpoint_booked_room :
    currentC < adoptedAtK0 + baselineContinuation + archivedExtraCoefficient +
      (oldSavedFloorPayment - actualStoredLoss) - 2 * eachReserve := by
  have h := source_endpoint_after_reserves_gt_currentC
  rw [refined_endpoint_eq_archived_source] at h
  exact h

theorem exists_archived_collared_source_room :
    ∃ δ : ℝ, 0 < δ ∧ currentC + originalEndpointSlack <
      adoptedAtK0 + baselineContinuation +
        (∑ s : ArchivedRow, ∑ r : Row, ∫ x in collaredArchivedPiece δ r s, semanticKernel x) +
          (oldSavedFloorPayment - actualStoredLoss) - 2 * baselineReserve - extraReserve := by
  obtain ⟨δ, hδ, hroom⟩ := exists_positive_collar_currentC_endpoint_room
  refine ⟨δ, hδ, ?_⟩
  unfold bufferedSourceEndpoint bufferedActualIncrement at hroom
  rw [retained_gain_eq_collared_archived_sum hδ.le] at hroom
  convert hroom using 1 <;> ring

end

end ImbalancedChen.P2FullMaskN48DeletedDisintegration
