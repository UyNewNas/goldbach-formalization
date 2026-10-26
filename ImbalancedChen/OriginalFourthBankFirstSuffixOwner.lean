import ImbalancedChen.OriginalFourthBankAppendOwnership

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The strict branch of literal ordered fourth-bank append: its owner is
exactly the first suffix maximizer shifted past the prefix records.
Repeated records remain separate occurrences; no sorting/deduplication
or arbitrary newly chosen winner is used. The actual rawQ3 seed and all
original row licences/closed-box tests remain in every maximum.
No bank append order is claimed to encode the missing manuscript22 map.
-/

namespace ImbalancedChen.OriginalFourthBankFirstSuffixOwner20261026b

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthBankAppendMaximum20261026b
open OriginalFourthBankAppendOwnership20261026b

/-- Raw occurrence i in the suffix remains occurrence length(front)+i.
Its bank position has the additional one for the inherited seed slot. -/
def suffixRowPosition (front tail : List FourthWireRow) (i : Fin tail.length) :
    Fin (front ++ tail).length := ⟨front.length + i.val, by
  have hi := i.isLt
  simp only [List.length_append]
  omega⟩

def suffixPosition (front tail : List FourthWireRow) (i : Fin tail.length) :
    BankPosition (front ++ tail) := (suffixRowPosition front tail i).succ

theorem rowAt_suffix (front tail : List FourthWireRow) (i : Fin tail.length) :
    rowAt (front ++ tail) (suffixRowPosition front tail i) = rowAt tail i := by
  unfold rowAt
  congr 1
  simpa only [Nat.add_comm] using (List.getElem_append_right' front i.isLt).symm

theorem slotValue_suffix (front tail : List FourthWireRow) (e seed : ℝ) (t : Point)
    (i : Fin tail.length) :
    slotValue (front ++ tail) e seed t (suffixPosition front tail i) =
      slotValue tail e seed t i.succ := by
  simp only [suffixPosition, slotValue, Fin.cases_succ, rowAt_suffix]

theorem slotEligible_suffix (front tail : List FourthWireRow) (licensed : ProducerRow → Prop)
    (t : Point) (i : Fin tail.length) :
    slotEligible (front ++ tail) licensed t (suffixPosition front tail i) =
      slotEligible tail licensed t i.succ := by
  simp only [suffixPosition, slotEligible, Fin.cases_succ, rowAt_suffix]

/-- Strict suffix improvement excludes its seed slot constructively from
the attained maximum; the resulting witness is an actual raw occurrence. -/
theorem strict_suffix_owner_is_row (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (hstrict : producerProfile4 e (fourthFamily front) licensed seed t <
      producerProfile4 e (fourthFamily tail) licensed seed t) :
    ∃ i : Fin tail.length, owner tail e seed licensed t = i.succ := by
  have hn : owner tail e seed licensed t ≠ 0 := by
    intro hz
    have hs := (owner_zero_iff tail e seed licensed t).mp hz
    rw [hs] at hstrict
    exact (not_lt_of_ge (producerProfile4_seed_le e (fourthFamily front) licensed seed t)) hstrict
  have hpos : 0 < (owner tail e seed licensed t).val := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply hn
    apply Fin.ext
    exact hz
  let i : Fin tail.length := ⟨(owner tail e seed licensed t).val - 1, by
    have hi := (owner tail e seed licensed t).isLt
    omega⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  dsimp [i]
  omega

/-- The FIRST suffix maximizer is the FIRST whole-bank maximizer under
strict improvement. The proof compares the two attained minima; it does
not supply the desired owner as an unproved selection premise. -/
theorem owner_append_strict_suffix (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (hstrict : producerProfile4 e (fourthFamily front) licensed seed t <
      producerProfile4 e (fourthFamily tail) licensed seed t)
    (i : Fin tail.length) (hi : owner tail e seed licensed t = i.succ) :
    owner (front ++ tail) e seed licensed t = suffixPosition front tail i := by
  have hp : producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t =
      producerProfile4 e (fourthFamily tail) licensed seed t := by
    rw [producerProfile_append, max_eq_right hstrict.le]
  have ht := (mem_winningSlots tail e seed licensed t i.succ).mp
    (hi ▸ owner_mem tail e seed licensed t)
  have hw : suffixPosition front tail i ∈ winningSlots (front ++ tail) e seed licensed t := by
    apply (mem_winningSlots (front ++ tail) e seed licensed t _).mpr
    rw [slotEligible_suffix, slotValue_suffix, hp]
    exact ht
  have hle := owner_le (front ++ tail) e seed licensed t _ hw
  have hnew := (appended_owner_iff_strict_improvement front tail e seed licensed t).mpr hstrict
  let j : Fin tail.length :=
    ⟨(owner (front ++ tail) e seed licensed t).val - front.length - 1, by
      have hj := (owner (front ++ tail) e seed licensed t).isLt
      simp only [List.length_append] at hj
      omega⟩
  have hj : owner (front ++ tail) e seed licensed t = suffixPosition front tail j := by
    apply Fin.ext
    dsimp [suffixPosition, suffixRowPosition, j]
    omega
  have hjwin : j.succ ∈ winningSlots tail e seed licensed t := by
    have ha := (mem_winningSlots (front ++ tail) e seed licensed t _).mp
      (owner_mem (front ++ tail) e seed licensed t)
    rw [hj, slotEligible_suffix, slotValue_suffix, hp] at ha
    exact (mem_winningSlots tail e seed licensed t j.succ).mpr ha
  have hmin := owner_le tail e seed licensed t j.succ hjwin
  rw [hi] at hmin
  have hidx : i.val ≤ j.val := by
    change i.val + 1 ≤ j.val + 1 at hmin
    omega
  have hback : (suffixPosition front tail i).val ≤
      (owner (front ++ tail) e seed licensed t).val := by
    rw [hj]
    dsimp [suffixPosition, suffixRowPosition]
    omega
  apply Fin.ext
  exact Nat.le_antisymm hle hback

/-- No caller chooses the suffix winner: attainment supplies its first
position, plus the unchanged original row licence and original box. -/
theorem strict_append_actual_row (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (hstrict : producerProfile4 e (fourthFamily front) licensed seed t <
      producerProfile4 e (fourthFamily tail) licensed seed t) :
    ∃ i : Fin tail.length,
      owner tail e seed licensed t = i.succ ∧
      owner (front ++ tail) e seed licensed t = suffixPosition front tail i ∧
      licensed (rowAt tail i) ∧ t ∈ (rowAt tail i).box ∧
      producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t =
        (rowAt tail i).bufferedCandidate e t := by
  obtain ⟨i, hi⟩ := strict_suffix_owner_is_row front tail e seed licensed t hstrict
  have hr := owned_row_is_actual_source tail e seed licensed t i hi
  refine ⟨i, hi, owner_append_strict_suffix front tail e seed licensed t hstrict i hi,
    hr.2.1, hr.2.2.1, ?_⟩
  rw [producerProfile_append, max_eq_right hstrict.le]
  exact hr.2.2.2

/-- Physical original rank-four cap of the new FIRST suffix owner, with
the same inherited e/chi/m/omega rawQ3 branch and actual selected mask. -/
theorem strict_append_history_level (front tail : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hlen : history.length = 4)
    (hstrict : producerProfile4 e (fourthFamily front) licensed (seedExponent e chi m omega N history)
        (primeHistoryLogCoordinates N 4 history) <
      producerProfile4 e (fourthFamily tail) licensed (seedExponent e chi m omega N history)
        (primeHistoryLogCoordinates N 4 history)) :
    ∃ i : Fin tail.length,
      owner (front ++ tail) e (seedExponent e chi m omega N history) licensed
        (primeHistoryLogCoordinates N 4 history) = suffixPosition front tail i ∧
      licensed (rowAt tail i) ∧
      primeHistoryLogCoordinates N 4 history ∈ (rowAt tail i).box ∧
      producerLevel4 e chi m omega N (fourthFamily (front ++ tail)) licensed history =
        N ^ (v (∑ k ∈ (rowAt tail i).selected, primeHistoryLogCoordinates N 4 history k) - 2 * e) := by
  obtain ⟨i, _hi, hall, hl, hb, hv⟩ := strict_append_actual_row front tail e
    (seedExponent e chi m omega N history) licensed (primeHistoryLogCoordinates N 4 history) hstrict
  refine ⟨i, hall, hl, hb, ?_⟩
  rw [producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen, hv, ProducerRow.bufferedCandidate_eq]

end
end ImbalancedChen.OriginalFourthBankFirstSuffixOwner20261026b
