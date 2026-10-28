import ImbalancedChen.P1HistoricalFifthOriginalBlockContributions
import ImbalancedChen.P5OldFifthExact64ChildTiling
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The carrier is the original ArchiveIndex times the original script's
(2,2,2,2,4) ChildIndex. Its18728512 members have distinct TRUE child
left-numerator keys and disjoint half-open child boxes. The original
parent/mask/opaque fields and64 children PER parent are retained.
-/
namespace ImbalancedChen.P1HistoricalFifthOriginalIndexedChildren
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1FifthGrid400UnitBoxPartition
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1HistoricalFifthTypedKeyPartition P1HistoricalFifthIndexedBankError
open P5OldFifthExact64ChildTiling

/-- Product of the two ALREADY independent original source carriers.
This introduces no replacement data bank or new child geometry. -/
abbrev ArchiveChild := ArchiveIndex × ChildIndex

theorem archiveChild_card : Fintype.card ArchiveChild = 18728512 := by
  rw [Fintype.card_prod, archiveIndex_card, childIndex_card]
  norm_num

def archiveChildKey (p : ArchiveChild) : Fin 5 → ℤ := childLeftNumer (archiveRow p.1) p.2

/-- The actual grid1600 mixed-radix numerator recovers both its grid400
parent geometry and its original2/2/2/2/4 digit. No opaque wire field is
used to manufacture child ownership. -/
theorem child_left_key_recovers_parent_and_digit
    (a b : FifthWireRow) (c d : ChildIndex)
    (hkey : childLeftNumer a c = childLeftNumer b d) : a.lo = b.lo ∧ c = d := by
  have hcoord : ∀ k : Fin 5, a.lo k = b.lo k ∧ (c k).val = (d k).val := by
    intro k
    have heq := congrFun hkey k
    by_cases hk : k.val < 4
    · have hc : (c k).val < 2 := by simpa [divisions, hk] using (c k).isLt
      have hd : (d k).val < 2 := by simpa [divisions, hk] using (d k).isLt
      simp only [childLeftNumer, width, if_pos hk, Nat.cast_ofNat] at heq
      constructor <;> omega
    · have hc : (c k).val < 4 := by simpa [divisions, hk] using (c k).isLt
      have hd : (d k).val < 4 := by simpa [divisions, hk] using (d k).isLt
      simp only [childLeftNumer, width, if_neg hk, Nat.cast_ofNat, one_mul] at heq
      constructor <;> omega
  refine ⟨funext (fun k => (hcoord k).1), ?_⟩
  funext k
  exact Fin.ext (hcoord k).2

theorem archiveChildKey_injective : Function.Injective archiveChildKey := by
  rintro ⟨i, c⟩ ⟨j, d⟩ hkey
  obtain ⟨hparents, hchildren⟩ := child_left_key_recovers_parent_and_digit
    (archiveRow i) (archiveRow j) c d hkey
  have hij := archiveIndex_eq_of_key_eq i j hparents
  exact Prod.ext hij hchildren

def archiveChildBox (p : ArchiveChild) : Set (Fin 5 → ℝ) := childBox (archiveRow p.1) p.2

theorem archiveChildBox_subset_original_parent (p : ArchiveChild) :
    archiveChildBox p ⊆ (archiveRow p.1).originalBox :=
  child_subset_parent _ (archiveRow_grid p.1) p.2

theorem archiveChildBox_measurable (p : ArchiveChild) : MeasurableSet (archiveChildBox p) :=
  childBox_measurable _ _

theorem archiveChild_common_point_unique (p r : ArchiveChild) (t : Fin 5 → ℝ)
    (hp : t ∈ archiveChildBox p) (hr : t ∈ archiveChildBox r) : p = r := by
  have hij := common_raw_point_index_unique p.1 r.1 t
    (archiveChildBox_subset_original_parent p hp) (archiveChildBox_subset_original_parent r hr)
  rcases p with ⟨i, c⟩
  rcases r with ⟨j, d⟩
  dsimp only at hij
  subst j
  exact Prod.ext rfl (common_child_point_eq (archiveRow i) c d t hp hr)

theorem archiveChildBoxes_pairwise_disjoint :
    Set.PairwiseDisjoint (Set.univ : Set ArchiveChild) archiveChildBox := by
  intro p _hp r _hr hne
  exact Set.disjoint_left.mpr (fun t ht hu => hne (archiveChild_common_point_unique p r t ht hu))

/-- Full original raw parent union, exactly once, equals its actual
18728512 half-open children. This is not128 children for each parent. -/
theorem original_parent_union_eq_all_indexed_children :
    (⋃ i : ArchiveIndex, (archiveRow i).originalBox) = ⋃ p : ArchiveChild, archiveChildBox p := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨c, hc⟩ := parent_covered_by_child (archiveRow i) (archiveRow_grid i) t hi
    exact mem_iUnion.mpr ⟨(i, c), hc⟩
  · intro ht
    obtain ⟨p, hp⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨p.1, archiveChildBox_subset_original_parent p hp⟩

def indexedChildRetained (p : ArchiveChild) (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    Set (Fin 5 → ℝ) := archiveChildBox p ∩ indexedDomain p.1 e q chi omega z

def indexedChildOmitted (p : ArchiveChild) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Set (Fin 5 → ℝ) := archiveChildBox p ∩ indexedOmitted p.1 e q chi omega

/-- No strict owner reject is lost at child boundaries. The independent
actual adopted domain is intersected with every original child. -/
theorem indexed_parent_retention_eq_union_children (i : ArchiveIndex)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (z : ℚ) :
    indexedDomain i e q chi omega z = ⋃ c : ChildIndex, indexedChildRetained (i, c) e q chi omega z := by
  ext t
  constructor
  · intro ht
    have hr := (indexedDomain_subset_parent i e q chi omega z ht).1
    obtain ⟨c, hc⟩ := parent_covered_by_child (archiveRow i) (archiveRow_grid i) t hr
    exact mem_iUnion.mpr ⟨c, hc, ht⟩
  · intro ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp ht
    exact hc.2

theorem indexed_parent_omission_eq_union_children (i : ArchiveIndex)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedOmitted i e q chi omega = ⋃ c : ChildIndex, indexedChildOmitted (i, c) e q chi omega := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, hc⟩ := parent_covered_by_child (archiveRow i) (archiveRow_grid i) t ht.1.1
    exact mem_iUnion.mpr ⟨c, hc, ht⟩
  · intro ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp ht
    exact hc.2

theorem indexed_child_retained_omitted_partition (p : ArchiveChild)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    archiveChildBox p = indexedChildRetained p e q chi omega 0 ∪ indexedChildOmitted p e q chi omega := by
  ext t
  have hparent : t ∈ archiveChildBox p → t ∈ P1OriginalFifthAdoptedOwnerBank.fixedParent (archiveRow p.1) := by
    intro ht
    rw [archive_fixedParent_eq_originalBox]
    exact archiveChildBox_subset_original_parent p ht
  constructor
  · intro ht
    by_cases hr : t ∈ indexedDomain p.1 e q chi omega 0
    · exact Or.inl ⟨ht, hr⟩
    · exact Or.inr ⟨ht, hparent ht, hr⟩
  · rintro (ht | ht) <;> exact ht.1

end
end ImbalancedChen.P1HistoricalFifthOriginalIndexedChildren
