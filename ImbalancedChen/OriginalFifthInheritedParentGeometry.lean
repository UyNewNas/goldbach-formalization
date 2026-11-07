import ImbalancedChen.OriginalFullFourthPriorityOwnership
import ImbalancedChen.P1ActualVariableFifthPositiveCellLimit

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The actual selected fifth owner inherits the ordered fourth parent through
the literal first-four projection. The fourth owner is reused, not chosen
again from a surrogate envelope. Its slot zero is the actual selected raw-Q3
seed; later slots are original fourth input positions, including duplicates.
The fifth maximum still contains every eligible decoded fifth row.

This is geometric parent inheritance for explicit input records. It does
not recover a historical dynamic-parent field from the fifth statistics,
assert coverage of a complete binary payload, or supply the 22 licenses.
-/

namespace ImbalancedChen.OriginalFifthInheritedParentGeometry20261026b

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1CorrectedFifthDensityDictionary
open P1ActualVariableFourthFifthCellTestLimit

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

/-- Constant only on an actually selected fifth mesh owner. -/
def parentOwner (records : List FourthWireRow) (e : ℚ) (m : ℕ)
    (j : Label5 m) (licensed : ProducerRow → Prop) (t : Point5) :
    OriginalFullFourthPriorityOwnership20261026a.BankPosition records :=
  OriginalFullFourthPriorityOwnership20261026a.owner records (e : ℝ) (selectedSeed e m j) licensed (firstFour t)

def parentValue (records : List FourthWireRow) (e : ℚ) (m : ℕ)
    (j : Label5 m) (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records) (t : Point5) : ℝ :=
  OriginalFullFourthPriorityOwnership20261026a.slotValue records (e : ℝ) (selectedSeed e m j) (firstFour t) i

/-- The parent label is pulled back, with weak faces and priority intact. -/
def parentRegion (records : List FourthWireRow) (e : ℚ) (m : ℕ)
    (j : Label5 m) (licensed : ProducerRow → Prop) (R : Set Point5)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records) : Set Point5 :=
  {t | t ∈ R ∧ parentOwner records e m j licensed t = i}

theorem measurableSet_parentRegion (records : List FourthWireRow) (e : ℚ)
    (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (hR : MeasurableSet R) (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records) :
    MeasurableSet (parentRegion records e m j licensed R i) :=
  hR.inter ((OriginalFullFourthPriorityOwnership20261026a.measurableSet_owner records (e : ℝ) (selectedSeed e m j)
    licensed i).preimage firstFour.continuous.measurable)

theorem parentRegion_cover (records : List FourthWireRow) (e : ℚ) (m : ℕ)
    (j : Label5 m) (licensed : ProducerRow → Prop) (R : Set Point5) :
    (⋃ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records, parentRegion records e m j licensed R i) = R := by
  ext t
  simp only [mem_iUnion, parentRegion, mem_setOf_eq]
  exact ⟨fun ⟨_, ht, _⟩ => ht,
    fun ht => ⟨parentOwner records e m j licensed t, ht, rfl⟩⟩

theorem parentRegion_disjoint (records : List FourthWireRow) (e : ℚ) (m : ℕ)
    (j : Label5 m) (licensed : ProducerRow → Prop) (R : Set Point5)
    {i k : OriginalFullFourthPriorityOwnership20261026a.BankPosition records} (hik : i ≠ k) :
    Disjoint (parentRegion records e m j licensed R i)
      (parentRegion records e m j licensed R k) := by
  apply Set.disjoint_left.mpr
  intro t hi hk
  exact hik (hi.2.symm.trans hk.2)

/-- The actual rough activation and raw-Q3 seed are supplied by selected
cell geometry; they are not inferred from saved delta/A/B statistics. -/
theorem actualOld4_eq_parentValue
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (t : Point5)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records) (hi : parentOwner records e m j licensed t = i) :
    originalVariableFourthProfile e chi omega m j (fourthFamily records) licensed t =
      parentValue records e m j i t := by
  have hs := (original_seed_constant_on_selected_owner e chi m omega J5 j hj ht).2
  have hv := OriginalFullFourthPriorityOwnership20261026a.owner_value records (e : ℝ) (selectedSeed e m j) licensed (firstFour t)
  change OriginalFullFourthPriorityOwnership20261026a.owner records (e : ℝ) (selectedSeed e m j) licensed (firstFour t) = i at hi
  rw [hi] at hv
  unfold originalVariableFourthProfile
  rw [hs]
  exact hv.symm

/-- Positional geometric inheritance. The fourth source box is pulled
back through processing slots 0,1,2,3, without sorting or reversing. -/
theorem parentRegion_row_geometry (records : List FourthWireRow) (e : ℚ)
    (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (i : Fin records.length) (t : Point5)
    (ht : t ∈ parentRegion records e m j licensed R i.succ) :
    licensed (OriginalFullFourthPriorityOwnership20261026a.rowAt records i) ∧
      firstFour t ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records i).box := by
  have h := OriginalFullFourthPriorityOwnership20261026a.owned_row_is_actual_source records (e : ℝ) (selectedSeed e m j)
    licensed (firstFour t) i ht.2
  exact ⟨h.2.1, h.2.2.1⟩

theorem selected_seed_branch
    (records : List FourthWireRow) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (t : Point5)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    parentOwner records e m j licensed t = 0 ↔
      originalVariableFourthProfile e chi omega m j (fourthFamily records) licensed t =
        selectedSeed e m j := by
  have hs := (original_seed_constant_on_selected_owner e chi m omega J5 j hj ht).2
  have h := OriginalFullFourthPriorityOwnership20261026a.owner_zero_iff records (e : ℝ) (selectedSeed e m j) licensed (firstFour t)
  unfold originalVariableFourthProfile
  rw [hs]
  exact h

/-- The fifth family is unchanged; only the inherited fourth seed is
written using its actual owner. All fifth max overlaps remain present. -/
def nextFromParent (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (t : Point5) : ℝ :=
  finiteMax (fifthFamily records5 m) (ownerEligible e m j)
    (fun r => candidate (e : ℝ) r.selected t) (parentValue records4 e m j i t)

theorem actualNext5_eq_nextFromParent
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (t : Point5)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4) (hi : parentOwner records4 e m j licensed t = i) :
    actualNext5 e chi m omega j (fourthFamily records4) licensed (fifthFamily records5 m) t =
      nextFromParent records4 records5 e m j i t := by
  unfold actualNext5 nextFromParent
  rw [actualOld4_eq_parentValue records4 e chi m omega J5 j hj licensed t ht i hi]

/-- Binding to the actual target-deleted next-candidate charge. There is
no hypothesis that the fifth tuple passed its OLD own-cube test: the old
and new terms each keep their own indicator, allowing restored tuples. -/
theorem literalTupleCharge_eq_parent_replacement
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (N cap : ℕ) (hN : 1 < N)
    (p : Fin 5 → ℕ) (hp : ∀ k, 0 < p k)
    (ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (hi : parentOwner records4 e m j licensed (actualPrimeTupleLog N p) = i) :
    literalTupleCharge e chi m omega (fourthFamily records4) licensed J5
        (fifthFamily records5 m) N cap p =
      actualPrimeTupleOwnCubeMinus N cap
          (nextFromParent records4 records5 e m j i (actualPrimeTupleLog N p)) p -
        actualPrimeTupleOwnCubeMinus N cap
          (parentValue records4 e m j i (actualPrimeTupleLog N p)) p := by
  rw [literalTupleCharge_on_selected_owner e chi m omega (fourthFamily records4) licensed
    J5 (fifthFamily records5 m) N cap hN p hp j hj ht,
    actualNext5_eq_nextFromParent records4 records5 e chi m omega J5 j hj licensed
      (actualPrimeTupleLog N p) ht i hi,
    actualOld4_eq_parentValue records4 e chi m omega J5 j hj licensed
      (actualPrimeTupleLog N p) ht i hi]

/-- An eligible decoded child and its actual fourth parent have simultaneous
source geometry. The fifth witness is an original List.get position, not
a deduplicated row identifier; no unique archived parent field is claimed. -/
theorem decoded_child_inherits_positional_parent
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (licensed : ProducerRow → Prop) (r : FifthRow m)
    (hr : r ∈ fifthFamily records5 m) (t : Point5)
    (he : eligible e chi m omega J5 r t) (i : Fin records4.length)
    (hi : parentOwner records4 e m r.cell licensed t = i.succ) :
    licensed (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 i) ∧ firstFour t ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt records4 i).box ∧
      ∃ k : Fin records5.length,
        r ∈ decodeFifthRows (records5.get k) m ∧
        r.selected = maskSlots 5 (records5.get k).mask.toNat ∧
        t ∈ (records5.get k).originalBox := by
  have hp := parentRegion_row_geometry records4 e m r.cell licensed univ i t ⟨mem_univ t, hi⟩
  obtain ⟨raw, hraw, hdecode⟩ := (mem_fifthFamily_iff records5 m r).mp hr
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hraw
  have hg := decodeFifthRows_source_geometry raw m r hdecode t he.2.2
  refine ⟨hp.1, hp.2, k, ?_⟩
  simpa only [hk] using (show r ∈ decodeFifthRows raw m ∧
    r.selected = maskSlots 5 raw.mask.toNat ∧ t ∈ raw.originalBox from
      ⟨hdecode, hg.2.2.1, hg.2.2.2⟩)

end
end ImbalancedChen.OriginalFifthInheritedParentGeometry20261026b
