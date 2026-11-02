import ImbalancedChen.P2ActualCropOrdinaryExclusion
import ImbalancedChen.P2N48WholePriorityOmegaFunctional

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual17572 extra fibre is charged to the same original unreplaced
n48 parent ledger used by the complete joint negative functional. The
fine/coarse intersection matrix is retained; no fine row is identified
with an n48 box. The ordinary exclusion is used to identify the extra
as actual cost above its half baseline, not to reverse min <= switched.

The resulting improvement applies to the complete U10+retained-U11
harmonic coefficient, including every priority/complement owner. It is
not an arithmetic count-to-kernel or numerical h1011 supplier. All old
closed archive/query/floor proposals remain unverified dependencies.
-/

namespace ImbalancedChen.P5OriginalJointSameMaskParentGainPayment

noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48TiedParentMassReduction
open P2N48LiteralDirectedFunctional P2N48OriginalPointwiseSavedMajorant
open OriginalPairedN48ArchivedOwnership P2FullMaskN48DeletedOwner
open P2FullMaskN48DeletedDisintegration P2ActualCropOrdinaryExclusion
open P2N48WholePriorityOmegaFunctional P2ActualSameMaskFloorFibreAccounting
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalSixteenAnchorFeedback
open Certificates.PairedV2.FullMask
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral

/-- The old fine-fibre intersections are now grouped by their actual
coarse owner, rather than replacing either index family by the other. -/
def parentExtraRegion (s : ArchivedRow) : Set LogFour :=
  region ∩ fullParent s.val

def deletedParent (r : SourceRow) : Set LogFour :=
  fullParent r \ selectedParent r actualMask

def switchedWeight (v : LogFour) : ℝ :=
  switchedKernel ImbalancedChen.currentK LiLiuPrereqBuchstab.buchstab v * harmonicDensity v

def deletedSwitchCost (r : SourceRow) : ℝ := ∫ v in deletedParent r, switchedWeight v

theorem actualRetainedRows_eq_archivedRows : actualRetainedRows = archivedRows := by
  exact actual_retainedMethodZero_eq_archivedRows

theorem archived_sum_eq_retained_sum (F : SourceRow → ℝ) :
    (∑ s : ArchivedRow, F s.val) = ∑ r ∈ actualRetainedRows, F r := by
  rw [actualRetainedRows_eq_archivedRows]
  exact Finset.sum_coe_sort archivedRows F

theorem parentExtraRegion_measurable (s : ArchivedRow) :
    MeasurableSet (parentExtraRegion s) :=
  P2AdoptedUnion.region_measurable.inter (measurableSet_fullParent s.val)

theorem deletedParent_measurable (r : SourceRow) : MeasurableSet (deletedParent r) :=
  (measurableSet_fullParent r).diff (measurableSet_selectedParent r)

theorem parentExtraRegion_eq_fine_union (s : ArchivedRow) :
    parentExtraRegion s = ⋃ r : Row, archivedPiece r s := by
  ext v
  simp only [parentExtraRegion, region, archivedPiece, mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨r, hr⟩, hs⟩
    exact ⟨r, hr, hs⟩
  · rintro ⟨r, hr, hs⟩
    exact ⟨⟨r, hr⟩, hs⟩

/-- Disjointness here is between fine rows inside one coarse parent;
the independent coarse disintegration was already proved in G. -/
theorem parentExtraRegion_integral (s : ArchivedRow) :
    (∫ v in parentExtraRegion s, semanticKernel v) =
      ∑ r : Row, archivedPieceGain r s := by
  rw [parentExtraRegion_eq_fine_union]
  apply integral_iUnion_fintype (fun r => archivedPiece_measurable r s)
  · intro r q hrq
    exact (supports_pairwise_disjoint hrq).mono
      (fun _ h => h.1) (fun _ h => h.1)
  · intro r
    exact integrable_semantic_archivedPiece r s

/-- Exact actual17572 gain, with its original Chen quarter, now indexed
by the ORIGINAL retained n48 owners. No one-row-to-one-parent map. -/
theorem actual_gain_eq_parent_integrals :
    actualExtraFibreGain = ∑ s : ArchivedRow,
      ∫ v in parentExtraRegion s, semanticKernel v := by
  simp_rw [parentExtraRegion_integral]
  exact actual_gain_eq_archived_coefficient

theorem parentExtraRegion_subset_deleted (s : ArchivedRow) :
    parentExtraRegion s ⊆ deletedParent s.val := by
  intro v hv
  obtain ⟨r, hr⟩ := mem_iUnion.mp hv.1
  exact ⟨hv.2, fun hs => Set.disjoint_left.mp (fibre_disjoint_retained_parent r s) hr hs⟩

theorem archived_fullParent_subset_high (s : ArchivedRow) :
    fullParent s.val ⊆ originalDomain ∅ := by
  intro v hv
  have ht : s.val.term.val ≠ 0 := by
    have h := (archived_row_facts s.val s.property).1
    omega
  exact (show v ∈ nativeBox s.val ∩ originalDomain ∅ by
    simpa only [fullParent, if_neg ht] using hv).2

theorem integrable_switchedWeight_fullParent (r : SourceRow) :
    IntegrableOn switchedWeight (fullParent r) := by
  have h := (integrable_switch_fullParent r).const_mul ImbalancedChen.currentK
  convert h using 1
  ext v
  rw [switchedWeight, switchedKernel_eq_mul_base]
  ring

theorem switchedWeight_nonneg_archived (s : ArchivedRow) {v : LogFour}
    (hv : v ∈ fullParent s.val) : 0 ≤ switchedWeight v := by
  have hd := archived_fullParent_subset_high s hv
  rw [switchedWeight, switchedKernel_eq_mul_base]
  exact mul_nonneg
    (mul_nonneg (by norm_num [ImbalancedChen.currentK]) (switchBase_nonneg ∅ v hd))
    (P5Z.U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hd)

/-- The proof uses actual ordinary exclusion and subtracts a positive
half baseline. Thus the extra is affordable on this deleted source. -/
theorem four_semanticKernel_le_switch {v : LogFour} (hv : v ∈ region) :
    4 * semanticKernel v ≤ switchedWeight v := by
  obtain ⟨r, hr⟩ := mem_iUnion.mp hv
  have hd := fibre_mem_full_high_domain hr
  have hden := P5Z.U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original ∅ v hd
  have hz : 0 < v 2 := by linarith [hd.1, hd.2.1]
  have hhalf : 0 ≤ (ImbalancedChen.currentK / (2 * v 2)) * harmonicDensity v :=
    mul_nonneg (div_nonneg (by norm_num [ImbalancedChen.currentK])
      (mul_nonneg (by norm_num) hz.le)) hden
  rw [semanticKernel_eq_actual_cost_extra r hr,
    cost_eq_switched_on_actual_row ImbalancedChen.currentK r (extra_fibre_mem_actual_row r hr)]
  dsimp only [switchedWeight]
  nlinarith only [hhalf]

/-- A true subset-integral payment, with no supplied enclosure, parent
cost bound or joint upper estimate. All points outside the extra fibre
retain their nonnegative switched cost. -/
theorem parent_extra_paid_from_deleted (s : ArchivedRow) :
    4 * (∫ v in parentExtraRegion s, semanticKernel v) ≤ deletedSwitchCost s.val := by
  have hsub := parentExtraRegion_subset_deleted s
  have hEF : parentExtraRegion s ⊆ fullParent s.val := fun _ h => h.2
  have hDF : deletedParent s.val ⊆ fullParent s.val := fun _ h => h.1
  have hiW := integrable_switchedWeight_fullParent s.val
  have hiG := (integrableOn_semanticKernel_region.mono_set
    (show parentExtraRegion s ⊆ region from fun _ h => h.1)).const_mul (4 : ℝ)
  have hpoint := setIntegral_mono_on hiG (hiW.mono_set hEF)
    (parentExtraRegion_measurable s)
    (fun v hv => four_semanticKernel_le_switch hv.1)
  have hmono : (∫ v in parentExtraRegion s, switchedWeight v) ≤
      ∫ v in deletedParent s.val, switchedWeight v := by
    apply setIntegral_mono_set (hiW.mono_set hDF)
    · filter_upwards [ae_restrict_mem (deletedParent_measurable s.val)] with v hv
      exact switchedWeight_nonneg_archived s hv.1
    · exact Eventually.of_forall (fun _ hv => hsub hv)
  rw [integral_const_mul] at hpoint
  exact hpoint.trans hmono

/-- The factor4 converts the original Chen-quarter gain to the raw
joint coefficient. The exact fine/coarse ownership pays it only once. -/
theorem actual_gain_paid_from_deleted :
    4 * actualExtraFibreGain ≤ ∑ r ∈ actualRetainedRows, deletedSwitchCost r := by
  rw [actual_gain_eq_parent_integrals, Finset.mul_sum,
    ← archived_sum_eq_retained_sum deletedSwitchCost]
  exact Finset.sum_le_sum (fun s _ => parent_extra_paid_from_deleted s)

/-- I's pointwise licence is applied before integration, then the actual
extra is charged from the deleted switched mass of those same parents. -/
theorem retained_parent_gain_payment_proposal :
    (∑ r ∈ actualRetainedRows,
      parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
        4 * actualExtraFibreGain ≤ retainedLiteralUpper := by
  have hlic := actual_retained_same_mask_payment_proposal
  have hgain := actual_gain_paid_from_deleted
  change (∑ r ∈ actualRetainedRows,
    parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
    (∑ r ∈ actualRetainedRows, deletedSwitchCost r) ≤ retainedLiteralUpper at hlic
  linarith only [hlic, hgain]

/-- COMPLETE negative coefficient: priority children, ordinary remaining
owners and the whole U10 low band stay in the unchanged complement. -/
theorem whole_joint_gain_payment_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient +
      4 * actualExtraFibreGain ≤ wholePriorityOmegaUpper := by
  have hsplit := actualSelectedCoefficient_eq_rows_add_uncovered actualRetainedRows
    P2N48ActualGeometricKeyDecoder.actualRetainedRows_distinctGeometricKeys
  have hret := retained_parent_gain_payment_proposal
  have hrest := uncovered_priority_omega_upper_proposal
  rw [whole_priority_upper_exact_retained_complement]
  linarith only [hsplit, hret, hrest]

/-- The correct sign and the original quarter appear at the negative
functional consumer. This is not a scalar h1011 endpoint certificate. -/
theorem signed_joint_gain_lower_proposal :
    -(wholePriorityOmegaUpper / 4) + actualExtraFibreGain ≤
      -(P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient / 4) := by
  linarith only [whole_joint_gain_payment_proposal]

/-- The unspent deleted mass is explicit and nonnegative. It is where
the older half-baseline/crop payment belongs, rather than a second copy
of the new omega-minus-half gain. No numerical baseline is asserted. -/
def remainingDeletedPayment : ℝ :=
  (∑ r ∈ actualRetainedRows, deletedSwitchCost r) / 4 - actualExtraFibreGain

theorem remainingDeletedPayment_nonneg : 0 ≤ remainingDeletedPayment := by
  dsimp only [remainingDeletedPayment]
  linarith only [actual_gain_paid_from_deleted]

theorem whole_joint_gain_and_remaining_payment_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient / 4 +
      actualExtraFibreGain + remainingDeletedPayment ≤ wholePriorityOmegaUpper / 4 := by
  have hsplit := actualSelectedCoefficient_eq_rows_add_uncovered actualRetainedRows
    P2N48ActualGeometricKeyDecoder.actualRetainedRows_distinctGeometricKeys
  have hlic := actual_retained_same_mask_payment_proposal
  change (∑ r ∈ actualRetainedRows,
    parentCost ImbalancedChen.currentK (selectedParent r actualMask)) +
    (∑ r ∈ actualRetainedRows, deletedSwitchCost r) ≤ retainedLiteralUpper at hlic
  have hrest := uncovered_priority_omega_upper_proposal
  rw [whole_priority_upper_exact_retained_complement]
  dsimp only [remainingDeletedPayment]
  linarith only [hsplit, hlic, hrest]

/-- Both terms are the ORIGINAL finite native sources. Their proved
limits and the parent payment supply one threshold after epsilon is fixed.
This is harmonic approximation only; the signed AP/compiler gap remains. -/
theorem eventually_native_joint_with_actual_native_gain_proposal
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      -(wholePriorityOmegaUpper / 4) + P2FullMaskActualNativeGain.nativeGain 0 N - ε <
        -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
          (P1E0E1.deletionMask (N : ℝ))
          P5Z.U1011OriginalJointHarmonic.actualMinimum / 4) := by
  have ht := ((P5Z.U1011OriginalJointHarmonic.tendsto_nativeJoint_actual_adopted_mask.div_const
    (4 : ℝ)).neg).sub P2FullMaskActualNativeGain.tendsto_nativeGain_full
  have hlt : -(wholePriorityOmegaUpper / 4) - ε <
      -(P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient / 4) -
        actualExtraFibreGain := by
    linarith only [signed_joint_gain_lower_proposal, hε]
  have he := ht.eventually (Ioi_mem_nhds hlt)
  filter_upwards [he] with N hN
  linarith only [hN]

end
end ImbalancedChen.P5OriginalJointSameMaskParentGainPayment
