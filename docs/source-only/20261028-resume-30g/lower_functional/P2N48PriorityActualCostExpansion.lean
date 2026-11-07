import ImbalancedChen.P2N48PriorityHalfGridDictionary
import ImbalancedChen.P2N48LiteralDirectedFunctional

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
True same-mask priority half-grid costs expand the actual uncovered term.
This is genuine domain/integral disintegration, not the still missing
numerical max(old saving,sum child floors) replacement certificate.
No child cost bound, check=true or claimed complete table is a premise.
-/
namespace ImbalancedChen.P2N48PriorityActualCostExpansion
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48RetainedPriorityRemainder P2N48LiteralDirectedFunctional
open P2N48PriorityHalfGridDictionary OriginalPairedN48ArchiveData

def childActualCost (r : SourceRow) (b : HalfBits) : ℝ :=
  ∫ v in childSelectedParent r b,actualKernel v

def halfChildUnion (r : SourceRow) (B : Finset HalfBits) : Set LogFour :=
  ⋃ b∈B,childSelectedParent r b

private theorem halfChildUnion_measurable (r : SourceRow) (B : Finset HalfBits) :
    MeasurableSet (halfChildUnion r B) :=
  Finset.measurableSet_biUnion B (fun b _ => measurableSet_childSelectedParent r b)

private theorem halfChildUnion_subset (r : SourceRow) (B : Finset HalfBits) :
    halfChildUnion r B⊆actualDomain := by
  intro v hv
  obtain ⟨b,hb⟩ := mem_iUnion.mp hv
  obtain ⟨_,hbv⟩ := mem_iUnion.mp hb
  exact selectedParent_subset_actualDomain r (childSelectedParent_subset_parent r b hbv)

theorem actual_half_children_integral (r : SourceRow) (B : Finset HalfBits) :
    (∫ v in halfChildUnion r B,actualKernel v)=∑ b∈B,childActualCost r b := by
  induction B using Finset.induction_on with
  | empty => simp [halfChildUnion]
  | @insert b B hb ih =>
    have hu : halfChildUnion r (insert b B)=childSelectedParent r b∪halfChildUnion r B := by
      ext v
      simp [halfChildUnion]
    have hd : Disjoint (childSelectedParent r b) (halfChildUnion r B) := by
      apply Set.disjoint_left.mpr
      intro v hvb hvB
      obtain ⟨c,hc⟩ := mem_iUnion.mp hvB
      obtain ⟨hcB,hcv⟩ := mem_iUnion.mp hc
      have hbc : b≠c := fun h => hb (h.symm ▸ hcB)
      exact Set.disjoint_left.mp (half_children_disjoint r hbc) hvb hcv
    have hib := integrable_actualKernel.mono_set
      (fun v hv => selectedParent_subset_actualDomain r (childSelectedParent_subset_parent r b hv))
    have hiB := integrable_actualKernel.mono_set (halfChildUnion_subset r B)
    rw [hu,setIntegral_union hd (halfChildUnion_measurable r B) hib hiB,ih,Finset.sum_insert hb]
    rfl

/-- The source's weak-child filter discards only empty physical children,
so this is an exact integral equality, including every tied parent. -/
theorem original_high_parent_actual_cost (r : SourceRow) (ht : r.term.val=1) :
    parentCost ImbalancedChen.currentK (selectedParent r actualMask)=
      ∑ b∈originalHighChildren r,childActualCost r b := by
  rw [P2N48ActualSelectedRhoCoefficient.row_selected_cost_eq_actual_kernel]
  rw [high_parent_eq_original_children r ht]
  exact actual_half_children_integral r (originalHighChildren r)

def priorityCropRows : Finset SourceRow :=
  excludedRawRows.filter (fun r => r.ordinal∈rawPriorityOrdinals.toFinset)

def otherExcludedRows : Finset SourceRow :=
  excludedRawRows.filter (fun r => r.ordinal∉rawPriorityOrdinals.toFinset)

def priorityActualChildCost : ℝ :=
  ∑ r∈priorityCropRows,∑ b∈originalHighChildren r,childActualCost r b

def otherExcludedActualCost : ℝ :=
  ∑ r∈otherExcludedRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask)

theorem priority_crop_rows_are_high (r : SourceRow) (hr : r∈priorityCropRows) : r.term.val=1 := by
  have hraw := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr).1).1
  exact (decoded_of_mem_rawSelectedRows r (List.mem_toFinset.mp hraw)).1

theorem excluded_rows_priority_partition :
    excludedRawRows=priorityCropRows∪otherExcludedRows := by
  ext r
  simp [priorityCropRows,otherExcludedRows]
  tauto

theorem priority_other_disjoint : Disjoint priorityCropRows otherExcludedRows := by
  apply Finset.disjoint_left.mpr
  intro r hp ho
  exact (Finset.mem_filter.mp ho).2 (Finset.mem_filter.mp hp).2

/-- No parent is charged twice, and no cost outside this archive crop is
discarded. The dictionary uses original source ordinals, not mask row IDs. -/
theorem uncovered_exact_priority_children_other_outside :
    uncoveredCost actualRetainedRows=
      priorityActualChildCost+otherExcludedActualCost+outsideRawCropCost := by
  rw [uncoveredCost_exact_excluded_and_outside,excluded_rows_priority_partition,
    Finset.sum_union priority_other_disjoint]
  have hp : (∑ r∈priorityCropRows,
      parentCost ImbalancedChen.currentK (selectedParent r actualMask))=priorityActualChildCost := by
    unfold priorityActualChildCost
    apply Finset.sum_congr rfl
    intro r hr
    exact original_high_parent_actual_cost r (priority_crop_rows_are_high r hr)
  rw [hp]
  rfl

theorem whole_actual_coefficient_priority_children :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient=
      (∑ r∈actualRetainedRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))+
      priorityActualChildCost+otherExcludedActualCost+outsideRawCropCost := by
  rw [actual_selected_coefficient_eq_rows_add_uncovered,
    uncovered_exact_priority_children_other_outside]
  ring

/-- Source-proposal upper from F retained payload/query evidence; the
actual priority children and every other remaining cost stay explicit.
No numerical gain from these priority children is asserted here. -/
theorem whole_actual_upper_with_true_priority_children_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient≤
      retainedLiteralUpper+priorityActualChildCost+otherExcludedActualCost+outsideRawCropCost := by
  rw [whole_actual_coefficient_priority_children]
  exact add_le_add_right (add_le_add_right
    (add_le_add_right retained_actual_cost_upper_proposal _) _) _

/-- The same fixed adopted-mask native mean sees these exact priority
children, with all negative signs and original multiplicities preserved. -/
theorem tendsto_negative_nativeJoint_true_priority_children :
    Tendsto (fun N : ℕ =>
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
        (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
        P5Z.U1011OriginalJointHarmonic.actualMinimum)) atTop
      (𝓝 (-(∑ r∈actualRetainedRows,
        parentCost ImbalancedChen.currentK (selectedParent r actualMask))-
          priorityActualChildCost-otherExcludedActualCost-outsideRawCropCost)) := by
  have h := tendsto_negative_nativeJoint_rows_uncovered actualRetainedRows
    actualRetainedRows_distinctGeometricKeys
  rw [uncovered_exact_priority_children_other_outside] at h
  convert h using 1 <;> congr 1 <;> ring

end
end ImbalancedChen.P2N48PriorityActualCostExpansion
