import ImbalancedChen.OriginalFullFourthPriorityOwnership

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal raw fourth-bank append recurrence. The seed is the actual inherited
rawQ3 exponent when evaluated on a history. Every eligible occurrence uses
its original lo/hi/subset-mask decoder, pointwise tent and common 2e loss.
No new licence, numerical pass, or manuscript chronological22 map is inferred.
The finite-set image computes a scalar maximum only; the ordered occurrence
owner, including repetitions and ties, is treated in the companion module.
-/

namespace ImbalancedChen.OriginalFourthBankAppendMaximum20261026b

noncomputable section
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation

theorem fourthFamily_append (front tail : List FourthWireRow) :
    fourthFamily (front ++ tail) = fourthFamily front ∪ fourthFamily tail := by
  simp [fourthFamily]

/-- Every licensed, contained original row participates in the update.
The suffix maximum uses the SAME seed, never a new ordinary parent. -/
theorem producerProfile_append (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t =
      max (producerProfile4 e (fourthFamily front) licensed seed t)
        (producerProfile4 e (fourthFamily tail) licensed seed t) := by
  apply le_antisymm
  · apply finiteMax_le
    · exact (producerProfile4_seed_le e (fourthFamily front) licensed seed t).trans
        (le_max_left _ _)
    · intro r hr he
      rw [fourthFamily_append] at hr
      rcases Finset.mem_union.mp hr with hf | ht
      · exact (finiteMax_row_le (fourthFamily front) _ _ seed r hf he).trans
          (le_max_left _ _)
      · exact (finiteMax_row_le (fourthFamily tail) _ _ seed r ht he).trans
          (le_max_right _ _)
  · apply max_le
    · apply finiteMax_le
      · exact producerProfile4_seed_le e (fourthFamily (front ++ tail)) licensed seed t
      · intro r hr he
        apply finiteMax_row_le (fourthFamily (front ++ tail)) _ _ seed r _ he
        rw [fourthFamily_append]
        exact Finset.mem_union_left _ hr
    · apply finiteMax_le
      · exact producerProfile4_seed_le e (fourthFamily (front ++ tail)) licensed seed t
      · intro r hr he
        apply finiteMax_row_le (fourthFamily (front ++ tail)) _ _ seed r _ he
        rw [fourthFamily_append]
        exact Finset.mem_union_right _ hr

/-- A suffix loses or ties precisely when EACH of its eligible original
row candidates is below the already attained prefix maximum. -/
theorem suffix_nonimproving_iff (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e (fourthFamily tail) licensed seed t ≤
        producerProfile4 e (fourthFamily front) licensed seed t ↔
      ∀ r ∈ fourthFamily tail, producerEligible licensed r t →
        r.bufferedCandidate e t ≤ producerProfile4 e (fourthFamily front) licensed seed t := by
  constructor
  · intro h r hr he
    exact (finiteMax_row_le (fourthFamily tail) _ _ seed r hr he).trans h
  · intro h
    exact finiteMax_le (fourthFamily tail) _ _ seed _
      (producerProfile4_seed_le e (fourthFamily front) licensed seed t) h

theorem producerProfile_append_eq_front (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point)
    (ht : producerProfile4 e (fourthFamily tail) licensed seed t ≤
      producerProfile4 e (fourthFamily front) licensed seed t) :
    producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t =
      producerProfile4 e (fourthFamily front) licensed seed t := by
  rw [producerProfile_append, max_eq_left ht]

theorem producerProfile_append_strict_iff (front tail : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    producerProfile4 e (fourthFamily front) licensed seed t <
        producerProfile4 e (fourthFamily (front ++ tail)) licensed seed t ↔
      producerProfile4 e (fourthFamily front) licensed seed t <
        producerProfile4 e (fourthFamily tail) licensed seed t := by
  rw [producerProfile_append, lt_max_iff]
  simp

/-- The actual original rank-four level, before freezing to descendants. -/
theorem producerLevel4_rank_four (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hlen : history.length = 4) :
    producerLevel4 e chi m omega N (fourthFamily records) licensed history =
      N ^ producerProfile4 e (fourthFamily records) licensed
        (seedExponent e chi m omega N history) (primeHistoryLogCoordinates N 4 history) := by
  change N ^ (if history.length = 4 then _ else _) = _
  rw [if_pos hlen]
  rfl

/-- The recurrence is a physical N-power level statement with the actual
e/chi/m/omega rawQ3 parent, not merely an abstract max identity. -/
theorem producerLevel4_append (front tail : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (hN : 1 ≤ N) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hlen : history.length = 4) :
    producerLevel4 e chi m omega N (fourthFamily (front ++ tail)) licensed history =
      max (producerLevel4 e chi m omega N (fourthFamily front) licensed history)
        (producerLevel4 e chi m omega N (fourthFamily tail) licensed history) := by
  rw [producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen,
    producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen,
    producerLevel4_rank_four _ _ _ _ _ _ _ _ hlen, producerProfile_append]
  by_cases h : producerProfile4 e (fourthFamily front) licensed
      (seedExponent e chi m omega N history) (primeHistoryLogCoordinates N 4 history) ≤
    producerProfile4 e (fourthFamily tail) licensed
      (seedExponent e chi m omega N history) (primeHistoryLogCoordinates N 4 history)
  · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow_of_exponent_le hN h)]
  · have h' := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (Real.rpow_le_rpow_of_exponent_le hN h')]

end
end ImbalancedChen.OriginalFourthBankAppendMaximum20261026b
