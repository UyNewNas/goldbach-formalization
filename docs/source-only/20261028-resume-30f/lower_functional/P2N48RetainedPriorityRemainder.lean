import ImbalancedChen.P2N48ActualGeometricKeyDecoder

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The retained method-zero parents and the excluded archive parents use
the same adopted physical mask. Priority exclusions cannot silently
disappear from a negative upper integral. This file identifies precisely
where their cost remains, without asserting the child replacement cost.
-/
namespace ImbalancedChen.P2N48RetainedPriorityRemainder
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open OriginalPairedN48ArchiveData

def excludedRawRows : Finset SourceRow := rawSelectedRows.toFinset \ actualRetainedRows

def outsideRawCrop : Set LogFour := actualDomain \ selectedUnion rawSelectedRows.toFinset

def outsideRawCropCost : ℝ := ∫ v in outsideRawCrop,actualKernel v

theorem retained_subset_raw : actualRetainedRows⊆rawSelectedRows.toFinset := by
  intro r hr
  exact List.mem_toFinset.mpr (actualRetainedRows_policy r hr).1

theorem excluded_of_method_or_priority (r : SourceRow) (hr : r∈rawSelectedRows)
    (hex : r.method≠0 ∨ r.ordinal∈rawPriorityOrdinals.toFinset) :
    r∈excludedRawRows := by
  refine Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hr,?_⟩
  intro hret
  have hp := actualRetainedRows_policy r hret
  exact hex.elim (fun hm => hm hp.2.1) (fun hpri => hp.2.2 hpri)

/-- Original ordinal/geometry decoding proves actual non-overlap; a
NoDup ordinal assertion on its own would not justify this step. -/
theorem excluded_parent_subset_uncovered (r : SourceRow) (hr : r∈excludedRawRows) :
    selectedParent r actualMask⊆uncoveredDomain actualRetainedRows := by
  obtain ⟨hrRaw,hrNot⟩ := Finset.mem_sdiff.mp hr
  intro v hv
  refine ⟨selectedParent_subset_actualDomain r hv,?_⟩
  intro hcovered
  obtain ⟨s,hs⟩ := mem_iUnion.mp hcovered
  obtain ⟨hsRet,hsv⟩ := mem_iUnion.mp hs
  have hkey := rowKey_eq_of_mem_selectedParent hv hsv
  have heq := rawSelectedRows_rowKey_injective r s
    (List.mem_toFinset.mp hrRaw) (actualRetainedRows_policy s hsRet).1 hkey
  exact hrNot (heq.symm ▸ hsRet)

theorem actual_priority_parent_subset_uncovered (r : SourceRow)
    (hr : r∈rawSelectedRows) (hp : r.ordinal∈rawPriorityOrdinals.toFinset) :
    selectedParent r actualMask⊆uncoveredDomain actualRetainedRows :=
  excluded_parent_subset_uncovered r (excluded_of_method_or_priority r hr (Or.inr hp))

/-- The entire remainder is exactly the excluded raw archive parents
plus the part of the actual domain outside this crop. Neither is dropped. -/
theorem uncovered_exact_excluded_union_outside :
    uncoveredDomain actualRetainedRows=selectedUnion excludedRawRows∪outsideRawCrop := by
  ext v
  constructor
  · intro hv
    by_cases hcrop : v∈selectedUnion rawSelectedRows.toFinset
    · obtain ⟨r,hr⟩ := mem_iUnion.mp hcrop
      obtain ⟨hrRaw,hrv⟩ := mem_iUnion.mp hr
      have hrNot : r∉actualRetainedRows := by
        intro hrRet
        exact hv.2 (mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hrRet,hrv⟩⟩)
      exact Or.inl (mem_iUnion.mpr ⟨r,mem_iUnion.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hrRaw,hrNot⟩,hrv⟩⟩)
    · exact Or.inr ⟨hv.1,hcrop⟩
  · rintro (hex|hout)
    · obtain ⟨r,hr⟩ := mem_iUnion.mp hex
      obtain ⟨hrEx,hrv⟩ := mem_iUnion.mp hr
      exact excluded_parent_subset_uncovered r hrEx hrv
    · refine ⟨hout.1,?_⟩
      intro hret
      obtain ⟨r,hr⟩ := mem_iUnion.mp hret
      obtain ⟨hrRet,hrv⟩ := mem_iUnion.mp hr
      exact hout.2 (mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨retained_subset_raw hrRet,hrv⟩⟩)

theorem excluded_union_disjoint_outside :
    Disjoint (selectedUnion excludedRawRows) outsideRawCrop := by
  apply Set.disjoint_left.mpr
  intro v hex hout
  obtain ⟨r,hr⟩ := mem_iUnion.mp hex
  obtain ⟨hrEx,hrv⟩ := mem_iUnion.mp hr
  have hrRaw := (Finset.mem_sdiff.mp hrEx).1
  exact hout.2 (mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨hrRaw,hrv⟩⟩)

theorem excludedRawRows_distinct_keys : DistinctGeometricKeys excludedRawRows := by
  intro r hr s hs hkey
  exact rawSelectedRows_rowKey_injective r s
    (List.mem_toFinset.mp (Finset.mem_sdiff.mp hr).1)
    (List.mem_toFinset.mp (Finset.mem_sdiff.mp hs).1) hkey

/-- Exact actual-kernel cost accounting on the same mask. This theorem
does not identify a priority child maximum with its parent integral. -/
theorem uncoveredCost_exact_excluded_and_outside :
    uncoveredCost actualRetainedRows=
      (∑ r∈excludedRawRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))+
        outsideRawCropCost := by
  have hOutside : MeasurableSet outsideRawCrop :=
    measurableSet_actualDomain.diff (measurableSet_selectedUnion rawSelectedRows.toFinset)
  have hiEx := integrable_actualKernel.mono_set (selectedUnion_subset_actualDomain excludedRawRows)
  have hiOut := integrable_actualKernel.mono_set
    (show outsideRawCrop⊆actualDomain from fun _ hv => hv.1)
  unfold uncoveredCost
  rw [uncovered_exact_excluded_union_outside,
    setIntegral_union excluded_union_disjoint_outside hOutside hiEx hiOut,
    integral_selectedUnion_eq_sum excludedRawRows excludedRawRows_distinct_keys]
  rfl

theorem actual_coefficient_exact_three_costs :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient=
      (∑ r∈actualRetainedRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))+
      (∑ r∈excludedRawRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask))+
        outsideRawCropCost := by
  rw [actual_selected_coefficient_eq_rows_add_uncovered,uncoveredCost_exact_excluded_and_outside]
  ring

end
end ImbalancedChen.P2N48RetainedPriorityRemainder
