import ImbalancedChen.P2N48WholeHighLiteralFunctional

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The retained crop and the independently defined complete high-key functional
must use the same literal SourceRow, including its method, ordinal and Q80
floor.  This file proves that correspondence, reindexes the actual retained
finite sum, and splits the complete negative upper into that contribution
and its exact complementary keys. No new literals or finite decisions.
All inherited literal/producer/log/floor proposals remain unexecuted.
-/
namespace ImbalancedChen.OriginalPairedN48RetainedNativeFunctional

noncomputable section
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48CompleteHighPhysicalCover P2N48WholeHighLiteralFunctional
open P2N48LiteralDirectedFunctional OriginalPairedN48ArchiveData
open OriginalPairedN48WholeHighArchive OriginalPairedN48WholeHighQ112Evidence
open OriginalPairedN48AllNativeQueryGeometry OriginalPairedN48RequiredRowQ112Bridge
open P2N48OriginalHighBlockWeights

/-- Erase only the already-known high term; retain every native bin index. -/
def retainedNativeKey (r : SourceRow) : HighKey := (r.ix,r.iy,r.iz,r.iw)

def retainedNativeKeys : Finset HighKey := actualRetainedRows.image retainedNativeKey

/-- Complete equality, including saved method and floor, rather than equality
of placeholder geometry rows. It uses the frozen crop/full literal proposal. -/
theorem retained_row_at_key (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    keyActualRow (retainedNativeKey r) = r := by
  exact (actual_retained_same_whole_source r hr).symm

theorem retained_native_key_mem_high (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    retainedNativeKey r ∈ highKeys := by
  have hd := decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hd.2.1, hd.2.2.1⟩

theorem retained_native_keys_subset : retainedNativeKeys ⊆ highKeys := by
  intro k hk
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hk
  exact retained_native_key_mem_high r hr

/-- The retained key family is defined from the genuine crop. Membership
cannot be inferred merely from method0 or from a favorable query. -/
theorem mem_retained_native_keys (k : HighKey) :
    k ∈ retainedNativeKeys ↔ ∃ r ∈ actualRetainedRows, retainedNativeKey r = k := by
  exact Finset.mem_image

theorem retained_native_key_injective (r s : SourceRow)
    (hr : r ∈ actualRetainedRows) (hs : s ∈ actualRetainedRows)
    (hkey : retainedNativeKey r = retainedNativeKey s) : r = s := by
  calc
    r = keyActualRow (retainedNativeKey r) := (retained_row_at_key r hr).symm
    _ = keyActualRow (retainedNativeKey s) := congrArg keyActualRow hkey
    _ = s := retained_row_at_key s hs

/-- Original raw-array numerator, J112 weight, directed endpoints, max-clamp
check and Q80 floor all come from the same full literal row at the consumer. -/
theorem retained_original_fields_at_key (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    rowOriginalNumerator (keyActualRow (retainedNativeKey r)) = rowOriginalNumerator r ∧
    rowOriginalQueryToken (keyActualRow (retainedNativeKey r)) = rowOriginalQueryToken r ∧
    originalRowZToken (keyActualRow (retainedNativeKey r)) = originalRowZToken r ∧
    originalRowEndpoint (keyActualRow (retainedNativeKey r)) = originalRowEndpoint r ∧
    originalRequiredRowFloorCheck (keyActualRow (retainedNativeKey r)) =
      originalRequiredRowFloorCheck r ∧
    (keyActualRow (retainedNativeKey r)).floorQ = r.floorQ := by
  rw [retained_row_at_key r hr]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The producer-field/query identity is the actual original-vs-canonical
array theorem, transported to the native key without a supplied numerator. -/
theorem retained_key_original_canonical_numerator (r : SourceRow)
    (hr : r ∈ actualRetainedRows) :
    rowOriginalNumerator (keyActualRow (retainedNativeKey r)) = rowCanonicalNumerator r := by
  rw [retained_row_at_key r hr]
  exact row_original_query_identity r

/-- This evidence entry belongs to the original whole-high method0 list,
not to a fabricated maximum-cover list or a geometry-only replacement. -/
theorem retained_key_in_whole_high_evidence (r : SourceRow)
    (hr : r ∈ actualRetainedRows) :
    wholeHighDirectedFields (keyActualRow (retainedNativeKey r)) ∈
      wholeHighMethodZeroEvidence := by
  rw [retained_row_at_key r hr]
  apply whole_high_evidence_contains
  apply List.mem_filter.mpr
  have hd := decoded_of_mem_rawSelectedRows r (actualRetainedRows_policy r hr).1
  have hm := actualRetainedRows_policy r hr
  have hfull : r ∈ fullHighArchiveRows := by
    rw [actual_retained_same_whole_source r hr]
    exact archiveRowForKey_mem_full r.ix r.iy r.iz r.iw hd.2.1 hd.2.2.1
  exact ⟨hfull, by simpa only [decide_eq_true_eq] using hm.2.1⟩

/-- Arbitrary real row observables reindex along the genuine injective key
map. Specializations below use actual costs and original saved majorants. -/
theorem retained_sum_reindex (F : SourceRow → ℝ) :
    (∑ k ∈ retainedNativeKeys, F (keyActualRow k)) =
      ∑ r ∈ actualRetainedRows, F r := by
  rw [retainedNativeKeys,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [retained_row_at_key r hr]
  · intro r hr s hs hkey
    exact retained_native_key_injective r s hr hs hkey

/-- The original priority exclusion and saved method are taken from the
literal row. Thus the real functional chooses its method0 Q80 branch. -/
theorem retained_key_current_upper (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    keyCurrentUpper (retainedNativeKey r) =
      savedParent r (parentUnweightedMass (fullParent r)) - rowGainLower r := by
  have hp := actualRetainedRows_policy r hr
  simp only [keyCurrentUpper,retained_row_at_key r hr,if_neg hp.2.2,if_pos hp.2.1]

theorem retained_key_upper_sum_eq_literal :
    (∑ k ∈ retainedNativeKeys,keyCurrentUpper k) = retainedLiteralUpper := by
  have hsum : (∑ k ∈ retainedNativeKeys,keyCurrentUpper k) =
      ∑ r ∈ actualRetainedRows,
        (savedParent r (parentUnweightedMass (fullParent r)) - rowGainLower r) := by
    rw [retainedNativeKeys,Finset.sum_image]
    · exact Finset.sum_congr rfl retained_key_current_upper
    · intro r hr s hs hkey
      exact retained_native_key_injective r s hr hs hkey
  rw [hsum,Finset.sum_sub_distrib]
  rfl

/-- Exact complement: this is not an assertion that retained keys cover
U11, and U10 remains its separate full actual integral occurrence. -/
theorem complete_negative_upper_exact_retained_complement :
    completeNegativeUpper = retainedLiteralUpper +
      (∑ k ∈ highKeys \ retainedNativeKeys,keyCurrentUpper k) + lowActualCost := by
  have hsplit : highKeys = retainedNativeKeys ∪ (highKeys \ retainedNativeKeys) := by
    ext k
    have hs := retained_native_keys_subset
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · intro hk
      by_cases hr : k ∈ retainedNativeKeys
      · exact Or.inl hr
      · exact Or.inr ⟨hk,hr⟩
    · rintro (hr | ⟨hk,_⟩)
      · exact hs hr
      · exact hk
  have hd : Disjoint retainedNativeKeys (highKeys \ retainedNativeKeys) := by
    apply Finset.disjoint_left.mpr
    intro k hr hc
    exact (Finset.mem_sdiff.mp hc).2 hr
  have hsum : (∑ k ∈ highKeys,keyCurrentUpper k) =
      (∑ k ∈ retainedNativeKeys,keyCurrentUpper k) +
        ∑ k ∈ highKeys \ retainedNativeKeys,keyCurrentUpper k := by
    calc
      (∑ k ∈ highKeys,keyCurrentUpper k) =
          ∑ k ∈ retainedNativeKeys ∪ (highKeys \ retainedNativeKeys),keyCurrentUpper k :=
        congrArg (fun S : Finset HighKey => ∑ k ∈ S,keyCurrentUpper k) hsplit
      _ = _ := Finset.sum_union hd
  unfold completeNegativeUpper
  rw [hsum,retained_key_upper_sum_eq_literal]

/-- The independent negative-functional consumer, with no new cost premise
and all inherited unexecuted finite obligations still present. -/
theorem whole_negative_upper_retained_complement_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient ≤
      retainedLiteralUpper +
        (∑ k ∈ highKeys \ retainedNativeKeys,keyCurrentUpper k) + lowActualCost := by
  rw [← complete_negative_upper_exact_retained_complement]
  exact whole_negative_functional_upper_proposal

theorem signed_negative_lower_retained_complement_proposal :
    -(retainedLiteralUpper +
        (∑ k ∈ highKeys \ retainedNativeKeys,keyCurrentUpper k) + lowActualCost) ≤
      -P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient :=
  neg_le_neg whole_negative_upper_retained_complement_proposal

end
end ImbalancedChen.OriginalPairedN48RetainedNativeFunctional

