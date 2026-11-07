import ImbalancedChen.OriginalFourthBankAppendMaximum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Ordered occurrence semantics for literal raw fourth-bank append. Prefix
positions retain their original indices, including the seed at zero.
An appended suffix changes the owner exactly when its actual maximum
STRICTLY improves the prefix maximum. Thus all negative gaps, equality
faces, tied masks and repeated raw records retain the earlier owner.
These are bank-prefix facts; bank prefixes are NOT asserted to be the
missing chronological22 manuscript policies.
-/

namespace ImbalancedChen.OriginalFourthBankAppendOwnership20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankAppendMaximum20261026b

def prefixPosition (front tail : List FourthWireRow) (i : BankPosition front) :
    BankPosition (front ++ tail) := ⟨i.val, by have hi := i.isLt; simp; omega⟩

def prefixRowPosition (front tail : List FourthWireRow) (i : Fin front.length) :
    Fin (front ++ tail).length := ⟨i.val, by have hi := i.isLt; simp; omega⟩

theorem rowAt_prefix (front tail : List FourthWireRow) (i : Fin front.length) :
    rowAt (front ++ tail) (prefixRowPosition front tail i) = rowAt front i := by
  unfold rowAt
  congr 1
  exact List.getElem_append_left i.isLt

theorem slotValue_prefix (front tail : List FourthWireRow) (e seed : ℝ) (t : Point)
    (i : BankPosition front) :
    slotValue (front ++ tail) e seed t (prefixPosition front tail i) =
      slotValue front e seed t i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change (rowAt (front ++ tail) (prefixRowPosition front tail j)).bufferedCandidate e t =
      (rowAt front j).bufferedCandidate e t
    rw [rowAt_prefix]

theorem slotEligible_prefix (front tail : List FourthWireRow) (licensed : ProducerRow → Prop)
    (t : Point) (i : BankPosition front) :
    slotEligible (front ++ tail) licensed t (prefixPosition front tail i) =
      slotEligible front licensed t i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change producerEligible licensed (rowAt (front ++ tail) (prefixRowPosition front tail j)) t =
      producerEligible licensed (rowAt front j) t
    rw [rowAt_prefix]

theorem winningSlots_prefix_iff (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (hp : producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t =
      producerProfile4 e (fourthFamily front) licensed seed t) (i : BankPosition front) :
    prefixPosition front tail i ∈ winningSlots (front ++ tail) e seed licensed t ↔
      i ∈ winningSlots front e seed licensed t := by
  rw [mem_winningSlots, mem_winningSlots, slotEligible_prefix, slotValue_prefix, hp]

/-- The first maximizing prefix occurrence survives every losing or tied
suffix. The conclusion is equality of positions, not merely equal values. -/
theorem owner_append_of_nonimproving (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (ht : producerProfile4 e (fourthFamily tail) licensed seed t ≤
      producerProfile4 e (fourthFamily front) licensed seed t) :
    owner (front ++ tail) e seed licensed t =
      prefixPosition front tail (owner front e seed licensed t) := by
  have hp := producerProfile_append_eq_front front tail e seed licensed t ht
  have hw := (winningSlots_prefix_iff front tail e seed licensed t hp
    (owner front e seed licensed t)).mpr (owner_mem front e seed licensed t)
  have hle := owner_le (front ++ tail) e seed licensed t _ hw
  have hval : (owner (front ++ tail) e seed licensed t).val ≤
      (owner front e seed licensed t).val := hle
  let j : BankPosition front := ⟨(owner (front ++ tail) e seed licensed t).val, by
    have hi := (owner front e seed licensed t).isLt
    omega⟩
  have hj : owner (front ++ tail) e seed licensed t = prefixPosition front tail j := by
    apply Fin.ext
    rfl
  have hjwin : j ∈ winningSlots front e seed licensed t := by
    apply (winningSlots_prefix_iff front tail e seed licensed t hp j).mp
    rw [← hj]
    exact owner_mem (front ++ tail) e seed licensed t
  have hback : (owner front e seed licensed t).val ≤
      (owner (front ++ tail) e seed licensed t).val := owner_le front e seed licensed t j hjwin
  apply Fin.ext
  exact Nat.le_antisymm hval hback

/-- This form keeps the original row licences and box tests explicit.
Neither a saved winner mask nor a generic relation is used as a licence. -/
theorem owner_append_of_candidate_bounds (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (hrows : ∀ r ∈ fourthFamily tail, producerEligible licensed r t →
      r.bufferedCandidate e t ≤ producerProfile4 e (fourthFamily front) licensed seed t) :
    owner (front ++ tail) e seed licensed t =
      prefixPosition front tail (owner front e seed licensed t) :=
  owner_append_of_nonimproving front tail e seed licensed t
    ((suffix_nonimproving_iff front tail e seed licensed t).mpr hrows)

/-- A change to a newly appended occurrence is equivalent to STRICT
improvement over the current bank. Ties can never move ownership right. -/
theorem appended_owner_iff_strict_improvement (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    front.length < (owner (front ++ tail) e seed licensed t).val ↔
      producerProfile4 e (fourthFamily front) licensed seed t <
        producerProfile4 e (fourthFamily tail) licensed seed t := by
  constructor
  · intro hnew
    apply lt_of_not_ge
    intro ht
    have hs := owner_append_of_nonimproving front tail e seed licensed t ht
    have hv := congrArg Fin.val hs
    have hi := (owner front e seed licensed t).isLt
    dsimp [prefixPosition] at hv
    omega
  · intro hstrict
    apply lt_of_not_ge
    intro hold
    let j : BankPosition front := ⟨(owner (front ++ tail) e seed licensed t).val, by omega⟩
    have hj : owner (front ++ tail) e seed licensed t = prefixPosition front tail j := by
      apply Fin.ext
      rfl
    have hw := (mem_winningSlots (front ++ tail) e seed licensed t _).mp
      (owner_mem (front ++ tail) e seed licensed t)
    have he : slotEligible front licensed t j := by
      rw [← slotEligible_prefix front tail licensed t j, ← hj]
      exact hw.1
    have hv : slotValue front e seed t j =
        producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t := by
      rw [← slotValue_prefix front tail e seed t j, ← hj]
      exact hw.2
    have hle := eligible_slot_le_profile front e seed licensed t j he
    rw [hv, producerProfile_append, max_eq_right hstrict.le] at hle
    exact (not_le_of_gt hstrict) hle

/-- Repeated raw records remain genuine appended positions but cannot
steal the original position, even if they attain the current maximum. -/
theorem owner_append_repeated_record (front : List FourthWireRow) (raw : FourthWireRow)
    (hraw : raw ∈ front) (e seed : ℝ) (licensed : ProducerRow → Prop) (t : Point) :
    owner (front ++ [raw]) e seed licensed t =
      prefixPosition front [raw] (owner front e seed licensed t) := by
  apply owner_append_of_candidate_bounds
  intro r hr he
  obtain ⟨wire, hwire, hdecode⟩ := (mem_fourthFamily_iff [raw] r).mp hr
  have hwire' : wire = raw := by simpa only [List.mem_singleton] using hwire
  subst wire
  have hrfront : r ∈ fourthFamily front :=
    (mem_fourthFamily_iff front r).mpr ⟨raw, hraw, hdecode⟩
  exact finiteMax_row_le (fourthFamily front) _ _ seed r hrfront he

/-- Bind positional prefix stability to the same actual rank-four
rawQ3 parent used by the physical level producer. -/
theorem history_owner_append_of_nonimproving (front tail : List FourthWireRow)
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ)
    (ht : producerProfile4 e (fourthFamily tail) licensed (seedExponent e chi m omega N history)
        (primeHistoryLogCoordinates N 4 history) ≤
      producerProfile4 e (fourthFamily front) licensed (seedExponent e chi m omega N history)
        (primeHistoryLogCoordinates N 4 history)) :
    owner (front ++ tail) e (seedExponent e chi m omega N history) licensed
        (primeHistoryLogCoordinates N 4 history) =
      prefixPosition front tail (owner front e (seedExponent e chi m omega N history) licensed
        (primeHistoryLogCoordinates N 4 history)) ∧
      producerLevel4 e chi m omega N (fourthFamily (front ++ tail)) licensed history =
        producerLevel4 e chi m omega N (fourthFamily front) licensed history := by
  refine ⟨owner_append_of_nonimproving front tail e _ licensed _ ht, ?_⟩
  unfold producerLevel4 level4 exponent4
  split_ifs
  · rw [show profile4 (seedExponent e chi m omega N history) (fourthFamily (front ++ tail))
      (producerEligible licensed) (fun r => r.bufferedCandidate e)
      (primeHistoryLogCoordinates N 4 history) =
      profile4 (seedExponent e chi m omega N history) (fourthFamily front)
        (producerEligible licensed) (fun r => r.bufferedCandidate e)
        (primeHistoryLogCoordinates N 4 history) from
      producerProfile_append_eq_front front tail e _ licensed _ ht]
  · rfl

end
end ImbalancedChen.OriginalFourthBankAppendOwnership20261026b
