import ImbalancedChen.P2N48CompleteHighPhysicalCover
import ImbalancedChen.P2N48PriorityActualCostExpansion
import ImbalancedChen.OriginalPairedN48WholeHighQ112Evidence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The independently transcribed COMPLETE high-band payload is attached to
the actual whole high physical cover. Method-zero rows outside the old
crop now feed the same-parent current-K receiver. Priority rows expand
to their true same-mask half-grid costs. Ordinary costs and U10 remain
explicit; no missing priority saving certificate is manufactured.
All inherited finite field/producer/log/floor terms remain UNEXECUTED.
-/
namespace ImbalancedChen.P2N48WholeHighLiteralFunctional
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48PriorityHalfGridDictionary P2N48PriorityActualCostExpansion
open P2N48CompleteHighPhysicalCover OriginalPairedN48ArchiveData
open OriginalPairedN48WholeHighArchive OriginalPairedN48WholeHighQ112Evidence
open P5Z.U11Canonical P5Z.U1011OriginalSixteenU10Geometry

def keyActualRow (k : HighKey) : SourceRow := archiveRowForKey k.1 k.2.1 k.2.2.1 k.2.2.2

private theorem key_order (k : HighKey) (hk : k∈highKeys) :
    k.2.2.2≤k.2.2.1 ∧ k.2.2.1≤k.2.1 := (Finset.mem_filter.mp hk).2

theorem actual_key_parent_geometry_proposal (k : HighKey) (hk : k∈highKeys) :
    selectedParent (keyActualRow k) actualMask=selectedParent (highGeometryRow k) actualMask := by
  obtain ⟨ht,hx,hy,hz,hw,_⟩ := archiveRowForKey_fields_proposal
    k.1 k.2.1 k.2.2.1 k.2.2.2 (key_order k hk).1 (key_order k hk).2
  simp [keyActualRow,highGeometryRow,selectedParent,nativeBox,leftEnd,rightEnd,width,
    ht,hx,hy,hz,hw]

theorem actual_key_is_high_proposal (k : HighKey) (hk : k∈highKeys) :
    (keyActualRow k).term.val=1 := by
  have h := (archiveRowForKey_fields_proposal
    k.1 k.2.1 k.2.2.1 k.2.2.2 (key_order k hk).1 (key_order k hk).2).1
  simpa only [keyActualRow] using congrArg Fin.val h

def keyActualCost (k : HighKey) : ℝ :=
  parentCost ImbalancedChen.currentK (selectedParent (keyActualRow k) actualMask)

theorem complete_high_actual_row_cost_sum_proposal :
    (∑ r∈highGeometryRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))=
      ∑ k∈highKeys,keyActualCost k := by
  rw [highGeometryRows,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [keyActualCost,actual_key_parent_geometry_proposal k hk]
  · intro k hk l hl hrow
    have h := congrArg (fun r : SourceRow => (r.ix,r.iy,r.iz,r.iw)) hrow
    simpa only [highGeometryRow] using h

theorem actual_key_method_zero_current_cost_proposal (k : HighKey) (hk : k∈highKeys)
    (hm : (keyActualRow k).method=0) :
    keyActualCost k≤savedParent (keyActualRow k)
      (parentUnweightedMass (fullParent (keyActualRow k)))-rowGainLower (keyActualRow k) := by
  obtain ⟨ht,hx,hy,hz,hw,_⟩ := archiveRowForKey_fields_proposal
    k.1 k.2.1 k.2.2.1 k.2.2.2 (key_order k hk).1 (key_order k hk).2
  have hmass : massLower (keyActualRow k)≤parentUnweightedMass (fullParent (keyActualRow k)) := by
    apply P2N48TermOneAllPatternClosedVolumes.term1_massLower_le_true_parent
      (keyActualRow k) (actual_key_is_high_proposal k hk)
    simpa only [keyActualRow,hy,hz,hw] using key_order k hk
  have hold := archiveRowForKey_original_cost_proposal
    k.1 k.2.1 k.2.2.1 k.2.2.2 (key_order k hk).1 (key_order k hk).2 hm
  exact archived_method_zero_current_cost (keyActualRow k) actualMask hmass hold

/-- This is an upper EXPRESSION, not a numeral. Priority true cost is not
replaced by a guessed saved-floor maximum; ordinary costs remain actual. -/
def keyCurrentUpper (k : HighKey) : ℝ :=
  if (keyActualRow k).ordinal∈rawPriorityOrdinals.toFinset then
    ∑ b∈originalHighChildren (keyActualRow k),childActualCost (keyActualRow k) b
  else if (keyActualRow k).method=0 then
    savedParent (keyActualRow k) (parentUnweightedMass (fullParent (keyActualRow k)))-
      rowGainLower (keyActualRow k)
  else keyActualCost k

def lowActualCost : ℝ := ∫ v in domain10,actualKernel v
def completeNegativeUpper : ℝ := (∑ k∈highKeys,keyCurrentUpper k)+lowActualCost

theorem actual_key_current_upper_proposal (k : HighKey) (hk : k∈highKeys) :
    keyActualCost k≤keyCurrentUpper k := by
  by_cases hp : (keyActualRow k).ordinal∈rawPriorityOrdinals.toFinset
  · rw [keyCurrentUpper,if_pos hp]
    exact (original_high_parent_actual_cost (keyActualRow k) (actual_key_is_high_proposal k hk)).le
  · by_cases hm : (keyActualRow k).method=0
    · rw [keyCurrentUpper,if_neg hp,if_pos hm]
      exact actual_key_method_zero_current_cost_proposal k hk hm
    · simp only [keyCurrentUpper,if_neg hp,if_neg hm,le_refl]

/-- Complete actual physical high domain, independently attached to all
seven literal fields. The full U10 cost is retained as its own occurrence. -/
theorem whole_actual_coefficient_literal_high_identity_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient=
      (∑ k∈highKeys,keyActualCost k)+lowActualCost := by
  rw [whole_actual_coefficient_complete_high_grid,complete_high_actual_row_cost_sum_proposal]
  rfl

theorem whole_negative_functional_upper_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient≤completeNegativeUpper := by
  rw [whole_actual_coefficient_literal_high_identity_proposal]
  exact add_le_add_right (Finset.sum_le_sum actual_key_current_upper_proposal) _

theorem whole_signed_functional_lower_proposal :
    -completeNegativeUpper≤-P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient :=
  neg_le_neg whole_negative_functional_upper_proposal

/-- Same adopted mask before N and same actual minimum. This exact mean
is not an ordinary-rho=H248 identity and supplies no new AP count theorem. -/
theorem tendsto_same_mask_negative_whole_high_literal_proposal :
    Tendsto (fun N : ℕ =>
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
        (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
        P5Z.U1011OriginalJointHarmonic.actualMinimum)) atTop
      (𝓝 (-(∑ k∈highKeys,keyActualCost k)-lowActualCost)) := by
  have h := tendsto_negative_nativeJoint_rows_uncovered highGeometryRows complete_high_distinct_keys
  unfold uncoveredCost at h
  rw [complete_high_uncovered_is_low,complete_high_actual_row_cost_sum_proposal] at h
  exact h

end
end ImbalancedChen.P2N48WholeHighLiteralFunctional
