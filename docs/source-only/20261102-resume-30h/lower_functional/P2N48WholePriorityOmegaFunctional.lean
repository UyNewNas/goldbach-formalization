import ImbalancedChen.P2N96PrioritySameMaskCost
import ImbalancedChen.OriginalPairedN48RetainedNativeFunctional

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The whole negative term and its original retained-crop uncoveredCost now
consume genuine same-mask n96 priority Omega costs. All old method0 fields
come from the complete original high archive. Ordinary costs and all U10
remain explicit; this is not the historical final numerical enclosure.
-/
namespace ImbalancedChen.P2N48WholePriorityOmegaFunctional
noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48CompleteHighPhysicalCover P2N48WholeHighLiteralFunctional
open P2N48LiteralDirectedFunctional OriginalPairedN48ArchiveData
open OriginalPairedN48RetainedNativeFunctional P2N96PrioritySameMaskCost

/-- Priority replacement is tested BEFORE the nonpriority fixed-K slope. -/
def refinedKeyUpper (k : HighKey) : ℝ :=
  if (keyActualRow k).ordinal∈rawPriorityOrdinals.toFinset then keyPriorityUpper k
  else if (keyActualRow k).method=0 then
    savedParent (keyActualRow k) (parentUnweightedMass (fullParent (keyActualRow k)))-
      rowGainLower (keyActualRow k)
  else keyActualCost k

def complementKeys : Finset HighKey := highKeys \ retainedNativeKeys

def priorityUncoveredUpper : ℝ :=
  (∑ k∈complementKeys,refinedKeyUpper k)+lowActualCost

def wholePriorityOmegaUpper : ℝ :=
  (∑ k∈highKeys,refinedKeyUpper k)+lowActualCost

theorem refined_key_upper_sound_proposal (k : HighKey) (hk : k∈highKeys) :
    keyActualCost k≤refinedKeyUpper k := by
  by_cases hp : (keyActualRow k).ordinal∈rawPriorityOrdinals.toFinset
  · rw [refinedKeyUpper,if_pos hp]
    exact key_priority_upper_sound_proposal k hk
  · by_cases hm : (keyActualRow k).method=0
    · rw [refinedKeyUpper,if_neg hp,if_pos hm]
      exact actual_key_method_zero_current_cost_proposal k hk hm
    · simp only [refinedKeyUpper,if_neg hp,if_neg hm,le_refl]

/-- No retained crop parent can also receive a priority replacement. -/
theorem retained_key_not_priority (k : HighKey) (hk : k∈retainedNativeKeys) :
    (keyActualRow k).ordinal∉rawPriorityOrdinals.toFinset := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
  rw [retained_row_at_key r hr]
  exact (actualRetainedRows_policy r hr).2.2

theorem priority_key_in_complement (k : HighKey) (hk : k∈highKeys)
    (hp : (keyActualRow k).ordinal∈rawPriorityOrdinals.toFinset) : k∈complementKeys := by
  exact Finset.mem_sdiff.mpr ⟨hk,fun hr => retained_key_not_priority k hr hp⟩

private theorem full_sum_partition (F : HighKey→ℝ) :
    (∑ k∈highKeys,F k)=(∑ k∈retainedNativeKeys,F k)+(∑ k∈complementKeys,F k) := by
  have hsplit : highKeys=retainedNativeKeys∪complementKeys := by
    ext k
    simp only [Finset.mem_union,complementKeys,Finset.mem_sdiff]
    constructor
    · intro hk
      by_cases hr : k∈retainedNativeKeys
      · exact Or.inl hr
      · exact Or.inr ⟨hk,hr⟩
    · rintro (hr | ⟨hk,_⟩)
      · exact retained_native_keys_subset hr
      · exact hk
  have hd : Disjoint retainedNativeKeys complementKeys := by
    apply Finset.disjoint_left.mpr
    intro k hr hc
    exact (Finset.mem_sdiff.mp hc).2 hr
  calc
    (∑ k∈highKeys,F k)=(∑ k∈retainedNativeKeys∪complementKeys,F k) :=
      congrArg (fun S : Finset HighKey => ∑ k∈S,F k) hsplit
    _ = _ := Finset.sum_union hd

theorem retained_refined_upper_eq_literal :
    (∑ k∈retainedNativeKeys,refinedKeyUpper k)=retainedLiteralUpper := by
  rw [←retained_key_upper_sum_eq_literal]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [refinedKeyUpper,keyCurrentUpper,if_neg (retained_key_not_priority k hk)]

/-- This is the ORIGINAL crop uncoveredCost. The full-high literal source
and injective retained key dictionary remove the earlier outside-crop
geometry placeholder, leaving every actual complementary high owner and
the entire unmasked low band. No equality of deleted and retained fibres. -/
theorem uncovered_exact_complete_high_complement :
    uncoveredCost actualRetainedRows=
      (∑ k∈complementKeys,keyActualCost k)+lowActualCost := by
  have hwhole := whole_actual_coefficient_literal_high_identity_proposal
  rw [full_sum_partition] at hwhole
  have hcrop := actualSelectedCoefficient_eq_rows_add_uncovered actualRetainedRows
    actualRetainedRows_distinctGeometricKeys
  have hsame : (∑ k∈retainedNativeKeys,keyActualCost k)=
      ∑ r∈actualRetainedRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask) :=
    retained_sum_reindex (fun r => parentCost ImbalancedChen.currentK (selectedParent r actualMask))
  rw [hsame] at hwhole
  linarith only [hwhole,hcrop]

theorem uncovered_priority_omega_upper_proposal :
    uncoveredCost actualRetainedRows≤priorityUncoveredUpper := by
  rw [uncovered_exact_complete_high_complement]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro k hk
  exact refined_key_upper_sound_proposal k (Finset.mem_sdiff.mp hk).1

theorem whole_priority_upper_exact_retained_complement :
    wholePriorityOmegaUpper=retainedLiteralUpper+priorityUncoveredUpper := by
  unfold wholePriorityOmegaUpper priorityUncoveredUpper
  rw [full_sum_partition,retained_refined_upper_eq_literal]
  ring

/-- Actual complete-high data, original parent floors, complete priority
children, ordinary owners and U10 all occur once with the correct sign. -/
theorem whole_priority_omega_upper_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient≤wholePriorityOmegaUpper := by
  rw [whole_actual_coefficient_literal_high_identity_proposal]
  exact add_le_add_right (Finset.sum_le_sum refined_key_upper_sound_proposal) _

theorem whole_signed_priority_omega_lower_proposal :
    -wholePriorityOmegaUpper≤-P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient :=
  neg_le_neg whole_priority_omega_upper_proposal

/-- The existing mean is evaluated with exactly the adopted deletionMask,
fixed before N tends to infinity, and exactly the nonlinear actualMinimum.
This equality is not a limit to an upper bound or a new AP estimate. -/
theorem tendsto_same_mask_exact_complement :
    Tendsto (fun N : ℕ =>
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
        (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
        P5Z.U1011OriginalJointHarmonic.actualMinimum)) atTop
      (𝓝 (-(∑ r∈actualRetainedRows,
        parentCost ImbalancedChen.currentK (selectedParent r actualMask))-
          ((∑ k∈complementKeys,keyActualCost k)+lowActualCost))) := by
  have h := tendsto_negative_nativeJoint_rows_uncovered actualRetainedRows
    actualRetainedRows_distinctGeometricKeys
  rw [uncovered_exact_complete_high_complement] at h
  exact h

/-- A genuine same-mask consequence of the exact mean and the independently
paid upper. The arbitrary epsilon is the convergence error, not a new
uniform distribution budget or claimed historical numeric slack. -/
theorem eventually_same_mask_signed_priority_lower_proposal (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      -wholePriorityOmegaUpper-ε<
        -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
          (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
          P5Z.U1011OriginalJointHarmonic.actualMinimum) := by
  have ht := P5Z.U1011OriginalJointHarmonic.tendsto_nativeJoint_actual_adopted_mask.neg
  have hlt : -wholePriorityOmegaUpper-ε<
      -P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient := by
    linarith only [whole_signed_priority_omega_lower_proposal,hε]
  exact ht.eventually (Ioi_mem_nhds hlt)

end
end ImbalancedChen.P2N48WholePriorityOmegaFunctional
