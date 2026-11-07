import ImbalancedChen.OriginalFifthRawPositionalJointOwnership

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Literal raw-record streaming computation of the fifth value and its first
maximizing position, with the genuine inherited fourth parent as slot zero.
The scan visits each List.get position once, including duplicate records;
it does not build a deduplicated fifth-family value set to choose a winner.
Decoded-cell eligibility and the actual whole-cell gate remain the precise
slot predicates. Equal values prefer the smaller ORIGINAL position.

Correctness reuses the already proved positional owner characterization.
This source executes no archived stream, verifies no payload, and recovers
no missing historical chronology or original all22 analytic license.
-/

namespace ImbalancedChen.OriginalFifthRawStreamingOwner20261026b

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open OriginalFifthInheritedParentGeometry20261026b
open OriginalFifthRawPositionalJointOwnership20261026b

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

/-- The later state is at least as good by value, and no later in the
original bank if values tie. This is the scan invariant, not a max oracle. -/
private def PriorityLE {n : ℕ} (value : Fin n → ℝ) (a b : Fin n) : Prop :=
  value a ≤ value b ∧ (value a = value b → b ≤ a)

private theorem priority_refl {n : ℕ} (value : Fin n → ℝ) (a : Fin n) :
    PriorityLE value a a := ⟨le_rfl, fun _ => le_rfl⟩

private theorem priority_trans {n : ℕ} (value : Fin n → ℝ) {a b c : Fin n}
    (hab : PriorityLE value a b) (hbc : PriorityLE value b c) : PriorityLE value a c := by
  refine ⟨hab.1.trans hbc.1, ?_⟩
  intro hac
  have habEq : value a = value b := le_antisymm hab.1 (by rw [hac]; exact hbc.1)
  have hbcEq : value b = value c := le_antisymm hbc.1 (by rw [← hac]; exact hab.1)
  exact (hbc.2 hbcEq).trans (hab.2 habEq)

/-- A raw row may replace the current state only when eligible and better;
the equal-value branch explicitly preserves earliest original position. -/
private def scanStep {n : ℕ} (eligible : Fin n → Prop) (value : Fin n → ℝ)
    (best candidate : Fin n) : Fin n :=
  if eligible candidate ∧ (value best < value candidate ∨
      (value best = value candidate ∧ candidate < best)) then candidate else best

private theorem scanStep_spec {n : ℕ} (eligible : Fin n → Prop) (value : Fin n → ℝ)
    (best candidate : Fin n) (hbest : eligible best) :
    eligible (scanStep eligible value best candidate) ∧
      PriorityLE value best (scanStep eligible value best candidate) ∧
      (eligible candidate → PriorityLE value candidate (scanStep eligible value best candidate)) := by
  unfold scanStep
  by_cases h : eligible candidate ∧ (value best < value candidate ∨
      (value best = value candidate ∧ candidate < best))
  · rw [if_pos h]
    refine ⟨h.1, ?_, fun _ => priority_refl value candidate⟩
    rcases h.2 with hv | ⟨hv, hpos⟩
    · exact ⟨hv.le, fun heq => (hv.ne heq).elim⟩
    · exact ⟨hv.le, fun _ => hpos.le⟩
  · rw [if_neg h]
    refine ⟨hbest, priority_refl value best, ?_⟩
    intro hc
    refine ⟨le_of_not_gt (fun hv => h ⟨hc, Or.inl hv⟩), ?_⟩
    intro heq
    apply le_of_not_gt
    intro hpos
    exact h ⟨hc, Or.inr ⟨heq.symm, hpos⟩⟩

private theorem scan_list_spec {n : ℕ} (eligible : Fin n → Prop) (value : Fin n → ℝ)
    (input : List (Fin n)) (best : Fin n) (hbest : eligible best) :
    eligible (input.foldl (scanStep eligible value) best) ∧
      PriorityLE value best (input.foldl (scanStep eligible value) best) ∧
      ∀ k ∈ input, eligible k → PriorityLE value k (input.foldl (scanStep eligible value) best) := by
  induction input generalizing best with
  | nil => exact ⟨hbest, priority_refl value best, by simp⟩
  | cons candidate input ih =>
    have hs := scanStep_spec eligible value best candidate hbest
    have ht := ih (scanStep eligible value best candidate) hs.1
    refine ⟨ht.1, priority_trans value hs.2.1 ht.2.1, ?_⟩
    intro k hk hel
    rcases List.mem_cons.mp hk with hkc | hk
    · subst k
      exact priority_trans value (hs.2.2 hel) ht.2.1
    · exact ht.2.2 k hk hel

/-- Succ maps original raw List.get index k to bank position k+1.
No raw occurrence is removed or reordered at this computation boundary. -/
def rawPositions (records : List FifthWireRow) : List (FifthPosition records) :=
  (List.finRange records.length).map Fin.succ

theorem rawPositions_length (records : List FifthWireRow) :
    (rawPositions records).length = records.length := by simp [rawPositions]

theorem rawPosition_mem (records : List FifthWireRow) (k : Fin records.length) :
    k.succ ∈ rawPositions records := by
  exact List.mem_map.mpr ⟨k, by simp, rfl⟩

def streamOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4)
    (t : Point5) : FifthPosition records5 :=
  (rawPositions records5).foldl
    (scanStep (slotEligible records5 e m j) (slotValue records4 records5 e m j parent t)) 0

/-- The streaming state is the existing canonical first maximizer.
The proof uses its established characterization, not another min construction. -/
theorem streamOwner_eq_owner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    streamOwner records4 records5 e m j parent t = fifthOwner records4 records5 e m j parent t := by
  let value := slotValue records4 records5 e m j parent t
  have hs := scan_list_spec (slotEligible records5 e m j) value (rawPositions records5) 0 True.intro
  have hall (k : FifthPosition records5) : slotEligible records5 e m j k →
      PriorityLE value k (streamOwner records4 records5 e m j parent t) := by
    refine Fin.cases ?_ (fun l => ?_) k
    · intro _hel
      exact hs.2.1
    · intro hel
      exact hs.2.2 l.succ (rawPosition_mem records5 l) hel
  have hw : streamOwner records4 records5 e m j parent t ∈
      winningSlots records4 records5 e m j parent t :=
    (winning_iff_dominates records4 records5 e m j parent t _).mpr
      ⟨hs.1, fun k hk => (hall k hk).1⟩
  have hv := ((mem_winningSlots records4 records5 e m j parent t _).mp hw).2
  symm
  apply (owner_eq_iff_first_maximizer records4 records5 e m j parent t _).mpr
  refine ⟨hw, ?_⟩
  intro k hk
  have hkw := (mem_winningSlots records4 records5 e m j parent t k).mp hk
  exact (hall k hkw.1).2 (hkw.2.trans hv.symm)

def streamValue (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) : ℝ :=
  slotValue records4 records5 e m j parent t (streamOwner records4 records5 e m j parent t)

theorem streamValue_eq_parent_max (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    streamValue records4 records5 e m j parent t = nextFromParent records4 records5 e m j parent t := by
  unfold streamValue
  rw [streamOwner_eq_owner, owner_value]

theorem stream_seed_wins_tie (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (parent : ParentPosition records4) (t : Point5) :
    streamOwner records4 records5 e m j parent t = 0 ↔
      nextFromParent records4 records5 e m j parent t = parentValue records4 e m j parent t := by
  rw [streamOwner_eq_owner]
  exact parent_wins_tie records4 records5 e m j parent t

def streamJointOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (t : Point5) : JointPosition records4 records5 :=
  let parent := parentOwner records4 e m j licensed t
  (parent, streamOwner records4 records5 e m j parent t)

theorem streamJointOwner_eq_jointOwner (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop) (t : Point5) :
    streamJointOwner records4 records5 e m j licensed t = jointOwner records4 records5 e m j licensed t := by
  exact Prod.ext rfl (streamOwner_eq_owner records4 records5 e m j _ t)

/-- On the actual selected fifth owner, the scan computes actualNext5
with the inherited raw-Q3/variable-fourth parent, never a stored old cap. -/
theorem streamValue_eq_actualNext5
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Label5 m))
    (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (t : Point5)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    streamValue records4 records5 e m j (parentOwner records4 e m j licensed t) t =
      actualNext5 e chi m omega j (fourthFamily records4) licensed (fifthFamily records5 m) t := by
  rw [streamValue_eq_parent_max]
  exact (actualNext5_eq_nextFromParent records4 records5 e chi m omega J5 j hj licensed
    t ht _ rfl).symm

end
end ImbalancedChen.OriginalFifthRawStreamingOwner20261026b
