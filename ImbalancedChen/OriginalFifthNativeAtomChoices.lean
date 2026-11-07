import ImbalancedChen.OriginalFifthLiteralAffineSignBank

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

The literal primitive guard fibers determine the native ordered fourth
parent, the native first raw fifth maximizer, and every final streaming
decision. The proof transports the complete sets of maximizers and then
uses their already established least-position property. No atom receives
an owner as input. Empty sign fibers cause no choice or archive assertion.

Both affine limbs, raw duplicates, weak box faces, and strict/weak guard
bits are those of the frozen literal bank. The resulting labels are fixed
from raw records and original selected Gamma data before N. Candidate cap
values remain variable on an atom. Original archive chronology, external
row licenses, and the complete original 22-successor theorem remain OPEN.
-/

namespace ImbalancedChen.OriginalFifthNativeAtomChoices20261026b

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1ActualVariableFourthFifthCellTestLimit
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b
open OriginalFifthRawStreamingOwner20261026b
open OriginalFifthLiteralAffineSignBank20261026b

private def parentKey (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (p : ParentPosition R4) : CandidateKey R4 R5 :=
  Fin.cases seedKey fourthKey p

private def successorKey (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (p : ParentPosition R4) (q : FifthPosition R5) : CandidateKey R4 R5 :=
  Fin.cases (parentKey R4 R5 p) fifthKey q

private theorem parentKey_value (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (p : ParentPosition R4)
    (t : Fin 5 → ℝ) :
    literalValue R4 R5 e m j (parentKey R4 R5 p) t = parentValue R4 e m j p t := by
  refine Fin.cases ?_ (fun k => ?_) p
  · exact literal_seed R4 R5 e m j t
  · exact literal_fourth R4 R5 e m j k t

private theorem successorKey_value (R4 : List FourthWireRow) (R5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) (p : ParentPosition R4)
    (q : FifthPosition R5) (t : Fin 5 → ℝ) :
    literalValue R4 R5 e m j (successorKey R4 R5 p q) t = slotValue R4 R5 e m j p t q := by
  refine Fin.cases ?_ (fun k => ?_) q
  · exact parentKey_value R4 R5 e m j p t
  · exact literal_fifth R4 R5 e m j k t

/-- This uses only primitive signs, including the projected CLOSED faces. -/
theorem parent_eligibility_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p : ParentPosition R4) :
    OriginalFullFourthPriorityOwnership20261026a.slotEligible R4 L (firstFour t) p ↔
      OriginalFullFourthPriorityOwnership20261026a.slotEligible R4 L (firstFour u) p := by
  refine Fin.cases ?_ (fun k => ?_) p
  · exact Iff.rfl
  · change (L (OriginalFullFourthPriorityOwnership20261026a.rowAt R4 k) ∧
        firstFour t ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt R4 k).box) ↔
      (L (OriginalFullFourthPriorityOwnership20261026a.rowAt R4 k) ∧
        firstFour u ∈ (OriginalFullFourthPriorityOwnership20261026a.rowAt R4 k).box)
    exact and_congr Iff.rfl (atom_fourth_box_iff R4 R5 e m j w ht hu k)

theorem parent_comparison_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p q : ParentPosition R4) :
    parentValue R4 e m j p t ≤ parentValue R4 e m j q t ↔
      parentValue R4 e m j p u ≤ parentValue R4 e m j q u := by
  simpa only [parentKey_value] using
    atom_literal_le_iff R4 R5 e m j w ht hu (parentKey R4 R5 p) (parentKey R4 R5 q)

private theorem fourth_maximizer_iff
    (R4 : List FourthWireRow) (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1))
    (L : ProducerRow → Prop) (t : Fin 5 → ℝ) (p : ParentPosition R4) :
    p ∈ OriginalFullFourthPriorityOwnership20261026a.winningSlots
        R4 (e : ℝ) (selectedSeed e m j) L (firstFour t) ↔
      OriginalFullFourthPriorityOwnership20261026a.slotEligible R4 L (firstFour t) p ∧
        ∀ q, OriginalFullFourthPriorityOwnership20261026a.slotEligible R4 L (firstFour t) q →
          parentValue R4 e m j q t ≤ parentValue R4 e m j p t := by
  rw [OriginalFullFourthPriorityOwnership20261026a.mem_winningSlots]
  constructor
  · rintro ⟨hp, hv⟩
    refine ⟨hp, fun q hq => ?_⟩
    change OriginalFullFourthPriorityOwnership20261026a.slotValue R4 (e : ℝ)
      (selectedSeed e m j) (firstFour t) q ≤ _
    rw [show parentValue R4 e m j p t = _ from hv]
    exact OriginalFullFourthPriorityOwnership20261026a.eligible_slot_le_profile
      R4 (e : ℝ) (selectedSeed e m j) L (firstFour t) q hq
  · rintro ⟨hp, hd⟩
    exact ⟨hp, le_antisymm
      (OriginalFullFourthPriorityOwnership20261026a.eligible_slot_le_profile
        R4 (e : ℝ) (selectedSeed e m j) L (firstFour t) p hp)
      (OriginalFullFourthPriorityOwnership20261026a.profile_le_of_slots
        R4 (e : ℝ) (selectedSeed e m j) _ L (firstFour t) hd)⟩

/-- ALL maximizers are preserved, before taking their least raw position. -/
theorem fourth_maximizer_set_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) :
    OriginalFullFourthPriorityOwnership20261026a.winningSlots
        R4 (e : ℝ) (selectedSeed e m j) L (firstFour t) =
      OriginalFullFourthPriorityOwnership20261026a.winningSlots
        R4 (e : ℝ) (selectedSeed e m j) L (firstFour u) := by
  ext p
  simp only [fourth_maximizer_iff]
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨(parent_eligibility_transport R4 R5 e m j L w ht hu p).mp hp, ?_⟩
    intro q hq
    exact (parent_comparison_transport R4 R5 e m j w ht hu q p).mp
      (hd q ((parent_eligibility_transport R4 R5 e m j L w ht hu q).mpr hq))
  · rintro ⟨hp, hd⟩
    refine ⟨(parent_eligibility_transport R4 R5 e m j L w ht hu p).mpr hp, ?_⟩
    intro q hq
    exact (parent_comparison_transport R4 R5 e m j w ht hu q p).mpr
      (hd q ((parent_eligibility_transport R4 R5 e m j L w ht hu q).mp hq))

theorem native_parent_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) :
    parentOwner R4 e m j L t = parentOwner R4 e m j L u := by
  have hs := fourth_maximizer_set_transport R4 R5 e m j L w ht hu
  have htmem := OriginalFullFourthPriorityOwnership20261026a.owner_mem
    R4 (e : ℝ) (selectedSeed e m j) L (firstFour t)
  have humem := OriginalFullFourthPriorityOwnership20261026a.owner_mem
    R4 (e : ℝ) (selectedSeed e m j) L (firstFour u)
  rw [hs] at htmem
  rw [← hs] at humem
  exact le_antisymm
    (OriginalFullFourthPriorityOwnership20261026a.owner_le
      R4 (e : ℝ) (selectedSeed e m j) L (firstFour t) _ humem)
    (OriginalFullFourthPriorityOwnership20261026a.owner_le
      R4 (e : ℝ) (selectedSeed e m j) L (firstFour u) _ htmem)

theorem successor_comparison_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p : ParentPosition R4) (q r : FifthPosition R5) :
    slotValue R4 R5 e m j p t q ≤ slotValue R4 R5 e m j p t r ↔
      slotValue R4 R5 e m j p u q ≤ slotValue R4 R5 e m j p u r := by
  simpa only [successorKey_value] using atom_literal_le_iff R4 R5 e m j w ht hu
    (successorKey R4 R5 p q) (successorKey R4 R5 p r)

theorem fifth_maximizer_set_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p : ParentPosition R4) :
    winningSlots R4 R5 e m j p t = winningSlots R4 R5 e m j p u := by
  ext q
  simp only [winning_iff_dominates]
  constructor
  · rintro ⟨hq, hd⟩
    exact ⟨hq, fun r hr => (successor_comparison_transport R4 R5 e m j w ht hu p r q).mp (hd r hr)⟩
  · rintro ⟨hq, hd⟩
    exact ⟨hq, fun r hr => (successor_comparison_transport R4 R5 e m j w ht hu p r q).mpr (hd r hr)⟩

theorem native_successor_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p : ParentPosition R4) :
    fifthOwner R4 R5 e m j p t = fifthOwner R4 R5 e m j p u := by
  have hs := fifth_maximizer_set_transport R4 R5 e m j w ht hu p
  have htmem := owner_mem R4 R5 e m j p t
  have humem := owner_mem R4 R5 e m j p u
  rw [hs] at htmem
  rw [← hs] at humem
  exact le_antisymm (owner_le R4 R5 e m j p t _ humem)
    (owner_le R4 R5 e m j p u _ htmem)

theorem native_joint_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) :
    jointOwner R4 R5 e m j L t = jointOwner R4 R5 e m j L u := by
  have hp := native_parent_constant R4 R5 e m j L w ht hu
  change (parentOwner R4 e m j L t, fifthOwner R4 R5 e m j (parentOwner R4 e m j L t) t) =
    (parentOwner R4 e m j L u, fifthOwner R4 R5 e m j (parentOwner R4 e m j L u) u)
  rw [hp]
  exact Prod.ext rfl (native_successor_constant R4 R5 e m j w ht hu _)

theorem native_stream_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) :
    streamJointOwner R4 R5 e m j L t = streamJointOwner R4 R5 e m j L u := by
  rw [streamJointOwner_eq_jointOwner, streamJointOwner_eq_jointOwner]
  exact native_joint_constant R4 R5 e m j L w ht hu

/-- The replacement predicate for EVERY incoming original raw occurrence,
including ties, is itself determined by primitive signs. -/
theorem replacement_predicate_transport
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (p : ParentPosition R4) (q r : FifthPosition R5) :
    (slotEligible R5 e m j r ∧
      (slotValue R4 R5 e m j p t q < slotValue R4 R5 e m j p t r ∨
        (slotValue R4 R5 e m j p t q = slotValue R4 R5 e m j p t r ∧ r < q))) ↔
    (slotEligible R5 e m j r ∧
      (slotValue R4 R5 e m j p u q < slotValue R4 R5 e m j p u r ∨
        (slotValue R4 R5 e m j p u q = slotValue R4 R5 e m j p u r ∧ r < q))) := by
  have hlt : slotValue R4 R5 e m j p t q < slotValue R4 R5 e m j p t r ↔
      slotValue R4 R5 e m j p u q < slotValue R4 R5 e m j p u r := by
    simpa only [successorKey_value] using atom_literal_lt_iff R4 R5 e m j w ht hu
      (successorKey R4 R5 p q) (successorKey R4 R5 p r)
  have heq : slotValue R4 R5 e m j p t q = slotValue R4 R5 e m j p t r ↔
      slotValue R4 R5 e m j p u q = slotValue R4 R5 e m j p u r := by
    simp only [le_antisymm_iff]
    exact and_congr (successor_comparison_transport R4 R5 e m j w ht hu p q r)
      (successor_comparison_transport R4 R5 e m j w ht hu p r q)
  exact and_congr Iff.rfl (or_congr hlt (and_congr heq Iff.rfl))

/-- Partial ORIGINAL raw stream, starting at the genuine inherited slot. -/
def nativeScanPrefix
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : ParentPosition R4) (n : ℕ) (t : Fin 5 → ℝ) :
    FifthPosition R5 :=
  ((rawPositions R5).take n).foldl (fun q r =>
    if slotEligible R5 e m j r ∧
      (slotValue R4 R5 e m j p t q < slotValue R4 R5 e m j p t r ∨
        (slotValue R4 R5 e m j p t q = slotValue R4 R5 e m j p t r ∧ r < q))
    then r else q) 0

theorem nativeScanPrefix_complete
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (p : ParentPosition R4) (t : Fin 5 → ℝ) :
    nativeScanPrefix R4 R5 e m j p (rawPositions R5).length t = streamOwner R4 R5 e m j p t := by
  simp only [nativeScanPrefix, List.take_length]
  rfl

theorem nativeScanPrefix_constant
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    {t u : Fin 5 → ℝ} (ht : t ∈ signAtom R4 R5 e m j w)
    (hu : u ∈ signAtom R4 R5 e m j w) (n : ℕ) :
    nativeScanPrefix R4 R5 e m j (parentOwner R4 e m j L t) n t =
      nativeScanPrefix R4 R5 e m j (parentOwner R4 e m j L u) n u := by
  rw [native_parent_constant R4 R5 e m j L w ht hu]
  unfold nativeScanPrefix
  congr 1
  funext q r
  rw [propext (replacement_predicate_transport R4 R5 e m j w ht hu _ q r)]

/-- A choice for each occupied fiber is CONSTRUCTED, never hypothesized. -/
def atomChoice (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (hw : (signAtom R4 R5 e m j w).Nonempty) : JointPosition R4 R5 :=
  jointOwner R4 R5 e m j L hw.choose

theorem atomChoice_spec
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (m : ℕ)
    (j : Fin 5 → Fin (m + 1)) (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (hw : (signAtom R4 R5 e m j w).Nonempty) {t : Fin 5 → ℝ}
    (ht : t ∈ signAtom R4 R5 e m j w) :
    jointOwner R4 R5 e m j L t = atomChoice R4 R5 e m j L w hw :=
  native_joint_constant R4 R5 e m j L w ht hw.choose_spec

/-- On the original selected cell, the exact variable caps equal the
constructed raw slots. Only their labels are frozen on a sign fiber. -/
theorem actual_caps_from_atomChoice
    (R4 : List FourthWireRow) (R5 : List FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J)
    (L : ProducerRow → Prop) (w : SignWord R4 R5)
    (hw : (signAtom R4 R5 e m j w).Nonempty) {t : Fin 5 → ℝ}
    (ht : t ∈ signAtom R4 R5 e m j w) (hm : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    originalVariableFourthProfile e chi omega m j (fourthFamily R4) L t =
        parentValue R4 e m j (atomChoice R4 R5 e m j L w hw).1 t ∧
      actualNext5 e chi m omega j (fourthFamily R4) L (fifthFamily R5 m) t =
        slotValue R4 R5 e m j (atomChoice R4 R5 e m j L w hw).1 t
          (atomChoice R4 R5 e m j L w hw).2 := by
  have hc := atomChoice_spec R4 R5 e m j L w hw ht
  have hp := congrArg Prod.fst hc
  have hq := congrArg Prod.snd hc
  change parentOwner R4 e m j L t = (atomChoice R4 R5 e m j L w hw).1 at hp
  change fifthOwner R4 R5 e m j (parentOwner R4 e m j L t) t =
    (atomChoice R4 R5 e m j L w hw).2 at hq
  refine ⟨actualOld4_eq_parentValue R4 e chi m omega J j hj L t hm _ hp, ?_⟩
  rw [actualNext5_eq_nextFromParent R4 R5 e chi m omega J j hj L t hm _ hp,
    ← owner_value R4 R5 e m j (atomChoice R4 R5 e m j L w hw).1 t]
  rw [hp] at hq
  rw [hq]

end
end ImbalancedChen.OriginalFifthNativeAtomChoices20261026b
