import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
import ImbalancedChen.P1HistoricalFifthIndexedBankError
import ImbalancedChen.P1FifthGrid400UnitBoxPartition
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
Original-index uniqueness is proved from a closed sorted-code witness on
the SAME literal list. Sorting is used only to certify uniqueness; it does
not replace the original order, masks, opaque fields or source indices.
The full finite decision is NOT RUN and its resource feasibility is unknown.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedKeyPartition
open P1OriginalPrefixRowDecodeSoundness P1FifthGrid400UnitBoxPartition
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthIndexedBankError
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank

/-- A function of the FIVE original geometry keys only. No converse code
injectivity premise is needed: equal geometry keys necessarily give equal
codes. The closed decision below concerns the full independent source list. -/
def codeOfKey (key : Fin 5 → ℤ) : ℕ :=
  ((((key 0).toNat * 400 + (key 1).toNat) * 400 + (key 2).toNat) * 400 +
    (key 3).toNat) * 400 + (key 4).toNat

def typedCodes : List ℕ :=
  Data.P1HistoricalFifthSavedTableData.rows.toList.map (fun raw => codeOfKey (rowKey raw))

def sortedCodes : List ℕ := typedCodes.mergeSort (fun a b => decide (a ≤ b))

/-- Linear adjacent comparisons after mergeSort; unlike a direct Nodup
decision on the unsorted list, this does not compare every pair of rows. -/
def AdjacentStrict : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => a < b ∧ AdjacentStrict (b :: tail)

instance adjacentStrictDecidable (xs : List ℕ) : Decidable (AdjacentStrict xs) := by
  induction xs with
  | nil => exact isTrue trivial
  | cons a xs ih =>
    cases xs with
    | nil => exact isTrue trivial
    | cons b tail =>
      change Decidable (a < b ∧ AdjacentStrict (b :: tail))
      letI : Decidable (AdjacentStrict (b :: tail)) := ih
      infer_instance

theorem adjacentStrict_tail (a : ℕ) (xs : List ℕ) (h : AdjacentStrict (a :: xs)) :
    AdjacentStrict xs := by
  cases xs with
  | nil => trivial
  | cons b tail => exact h.2

theorem adjacentStrict_head_lt (a : ℕ) (xs : List ℕ) (h : AdjacentStrict (a :: xs)) :
    ∀ b ∈ xs, a < b := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    intro c hc
    rcases List.mem_cons.mp hc with heq | hc
    · subst c
      exact h.1
    · exact lt_trans h.1 (ih b h.2 c hc)

theorem adjacentStrict_nodup (xs : List ℕ) (h : AdjacentStrict xs) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (adjacentStrict_tail a xs h)⟩
    intro ha
    exact (lt_irrefl a) (adjacentStrict_head_lt a xs h a ha)

/-- This is a closed term about all292633 actual typed source positions.
It is neither a supplied checker flag nor an archived-byte identity.
No decision reduction, checker or compiler was invoked by the author. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem actual_sorted_codes_strict : AdjacentStrict sortedCodes := by
  decide

theorem actual_typed_codes_nodup : typedCodes.Nodup := by
  exact (List.mergeSort_perm typedCodes (fun a b => decide (a ≤ b))).nodup_iff.mp
    (adjacentStrict_nodup sortedCodes actual_sorted_codes_strict)

/-- The uniqueness conclusion is for the ORIGINAL unsorted geometry keys. -/
theorem actual_typed_keys_nodup :
    (Data.P1HistoricalFifthSavedTableData.rows.toList.map rowKey).Nodup := by
  apply List.Nodup.of_map codeOfKey
  simpa only [List.map_map, Function.comp_def, typedCodes] using actual_typed_codes_nodup

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

def actualRecords : Finset FifthWireRow := Data.P1HistoricalFifthSavedTableData.rows.toList.toFinset

theorem actual_records_key_injective : KeyInjective actualRecords := by
  intro a ha b hb hkey
  exact List.inj_on_of_nodup_map actual_typed_keys_nodup a
    (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) hkey

theorem archiveIndex_eq_of_key_eq (i j : ArchiveIndex)
    (hkey : rowKey (archiveRow i) = rowKey (archiveRow j)) : i = j := by
  let keys := Data.P1HistoricalFifthSavedTableData.rows.toList.map rowKey
  have hi : i.val < keys.length := by simpa [keys] using i.isLt
  have hj : j.val < keys.length := by simpa [keys] using j.isLt
  have heq : keys[i.val]'hi = keys[j.val]'hj := by
    simpa only [keys, List.getElem_map, archiveRow] using hkey
  apply Fin.ext
  exact actual_typed_keys_nodup.getElem_inj_iff.mp heq

theorem archiveRow_injective : Function.Injective archiveRow := by
  intro i j h
  exact archiveIndex_eq_of_key_eq i j (congrArg rowKey h)

theorem actual_records_card : actualRecords.card = 292633 := by
  have hn : Data.P1HistoricalFifthSavedTableData.rows.toList.Nodup :=
    List.Nodup.of_map rowKey actual_typed_keys_nodup
  simpa only [actualRecords, List.toFinset_card_of_nodup hn] using
    P1HistoricalFifthTypedArchiveShape.rows_toList_length

theorem indexed_raw_boxes_disjoint (i j : ArchiveIndex) (hne : i ≠ j) :
    Disjoint (archiveRow i).originalBox (archiveRow j).originalBox := by
  apply unit_boxes_disjoint_of_key_ne _ _ (archiveRow_grid i) (archiveRow_grid j)
  exact fun hkey => hne (archiveIndex_eq_of_key_eq i j hkey)

theorem common_raw_point_index_unique (i j : ArchiveIndex) (t : Fin 5 → ℝ)
    (hi : t ∈ (archiveRow i).originalBox) (hj : t ∈ (archiveRow j).originalBox) : i = j :=
  archiveIndex_eq_of_key_eq i j
    (common_point_keys_eq _ _ (archiveRow_grid i) (archiveRow_grid j) t hi hj)

/-- Every raw coordinate is inside the actual0..19/96 compact ambient;
no clipping or lost source mass is hidden in fixedParent on this table. -/
theorem archive_originalBox_subset_ambient (i : ArchiveIndex) :
    (archiveRow i).originalBox ⊆
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  intro t ht
  apply mem_logPrimeBox.mpr
  intro k
  have hb := rows_lower_key_bounds (archiveRow i) (archiveRow_source_member i) k
  have hlo : (1 : ℝ) ≤ ((archiveRow i).lo k : ℝ) := by exact_mod_cast hb.1
  have hhi : ((archiveRow i).lo k : ℝ) ≤ 77 := by exact_mod_cast hb.2
  have hk : ((archiveRow i).lo k : ℝ) / 400 ≤ t k ∧
      t k < (((archiveRow i).lo k : ℝ) + 1) / 400 := by
    simpa [FifthWireRow.lower, FifthWireRow.upper, archiveRow_grid i] using ht k
  constructor <;> linarith

theorem archive_fixedParent_eq_originalBox (i : ArchiveIndex) :
    fixedParent (archiveRow i) = (archiveRow i).originalBox :=
  Set.inter_eq_left.mpr (archive_originalBox_subset_ambient i)

/-- Actual complete finite refined partition, for EACH original source
index. It is not replaced by the strict retained-owner subfamily. -/
theorem archive_fixedParent_eq_full_decoded_union (i : ArchiveIndex) (q : ℕ) (hq : 0 < q) :
    fixedParent (archiveRow i) =
      ⋃ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q),
        logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell :=
  refined_originalBox_inter_ambient_eq_decode_union q hq (archiveRow i)
    (archiveRow_grid i) (archiveRow_mask_nonnegative i)

/-- Strict adopted retention and the exact actual omitted region exhaust
the source parent. The latter is not set to zero by baseGeometry. -/
theorem indexed_parent_exact_partition (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    fixedParent (archiveRow i) =
      indexedDomain i e q chi omega 0 ∪ indexedOmitted i e q chi omega := by
  ext t
  have hs := indexedDomain_subset_parent i e q chi omega 0
  simp only [indexedOmitted, mem_union, mem_diff]
  constructor
  · intro hp
    by_cases hr : t ∈ indexedDomain i e q chi omega 0
    · exact Or.inl hr
    · exact Or.inr ⟨hp, hr⟩
  · rintro (hr | ho)
    · exact hs hr
    · exact ho.1

theorem indexed_retained_omitted_disjoint (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Disjoint (indexedDomain i e q chi omega 0) (indexedOmitted i e q chi omega) :=
  Set.disjoint_left.mpr (fun _ hr ho => ho.2 hr)

/-- The ACTUAL strict selected/firstStop/full/complement owner domains are
disjoint across original source indices, including every half-open face. -/
theorem indexed_domains_pairwise_disjoint (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    Set.PairwiseDisjoint (Set.univ : Set ArchiveIndex)
      (fun i => indexedDomain i e q chi omega z) := by
  intro i _hi j _hj hne
  exact (indexed_raw_boxes_disjoint i j hne).mono
    (fun _ ht => (indexedDomain_subset_parent i e q chi omega z ht).1)
    (fun _ ht => (indexedDomain_subset_parent j e q chi omega z ht).1)

theorem indexed_omitted_pairwise_disjoint (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set.PairwiseDisjoint (Set.univ : Set ArchiveIndex)
      (fun i => indexedOmitted i e q chi omega) := by
  intro i _hi j _hj hne
  exact (indexed_raw_boxes_disjoint i j hne).mono
    (fun _ ht => ht.1.1) (fun _ ht => ht.1.1)

end
end ImbalancedChen.P1HistoricalFifthTypedKeyPartition
