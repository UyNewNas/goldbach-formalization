import ImbalancedChen.P4AOriginalFull87ReceiverHarmonic
import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A NEW exact arithmetic pruning on the ORIGINAL fifth-exclusive sixth carrier.
The true receiver is positive and at most N. Every actual sixth candidate
p is smaller than all five earlier selected rough primes, so
  p^5 <= b5, hence p^6 <= p*b5 <= a*p*b5 (a>=1).
Therefore p^6>N forces receiverTest N (a*p*b5)=0, for EVERY original
Rosser a, including a=0 separately. No PP input, o(H_N) claim,
new parent, reordered suffix, deduplication or sixthFromBoth mask.

The root-pruned harmonic bill retains only ORIGINAL occurrences with
p^6<=N. It replaces the predecessor's unpruned harmonic invoice
in the SAME full-physical estimate, with the original three other
invoices counted once. It is NOT shown small relative to H_N.
-/

namespace ImbalancedChen.P4AOriginalFull87SixthRootReceiver
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_fifth_exclusive_sixth_power_bound)
open P4AOriginalFull87FifthRankPowerTail
  (actual_fifth_exclusive_length_five)
open P4AOriginalFull87ReceiverHarmonic
  (actual_receiver_fibre_le_floor
   actual_receiver_fibre_zero_of_large
   actual_large_plus_receiver_abs_le_harmonic)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue actual_event_large_value_eq_common)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The zero modulus fibre is empty, even though Nat division is total. -/
private theorem actual_receiver_zero_modulus (N : ℕ) :
    receiverTest N 0 = 0 := by
  have hle : receiverTest N 0 ≤ 0 := by
    simpa using actual_receiver_fibre_le_floor N 0
  have hnonneg : 0 ≤ receiverTest N 0 := by
    unfold receiverTest
    exact Nat.cast_nonneg _
  exact le_antisymm hle hnonneg

/-- NEW, for every actual fifth-exclusive occurrence and every sixth p
in its untouched original suffix: p^6 is bounded by the WHOLE rough
sixth product. This uses the previously proved real rank-five length,
not an arbitrary length-five tuple. -/
theorem actual_sixth_prime_sixth_power_le_rough
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    p ^ 6 ≤ (p :: fifth.selectedAfter).prod := by
  have hpow := actual_fifth_exclusive_sixth_power_bound
    delta n e q om N cap w z L X F state hstate fifth hfifth p hp
  have hlen := actual_fifth_exclusive_length_five
    delta n e q om N cap w z L X F state hstate fifth hfifth
  rw [hlen] at hpow
  calc
    p ^ 6 = p * p ^ 5 := by simp [pow_succ, Nat.mul_comm]
    _ ≤ p * fifth.selectedAfter.prod := Nat.mul_le_mul_left p hpow
    _ = (p :: fifth.selectedAfter).prod := by simp

/-- Full physical a*b6, not merely rough b6. A zero Rosser index is
handled separately instead of pretending that every a>=1. The actual
receiver is zero whenever the sixth candidate violates p^6<=N. -/
theorem actual_large_sixth_receiver_fibre_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (a : ℕ) (hlarge : N < p ^ 6) :
    receiverTest N (a * (p :: fifth.selectedAfter).prod) = 0 := by
  by_cases ha : a = 0
  · simpa [ha] using actual_receiver_zero_modulus N
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hrough := actual_sixth_prime_sixth_power_le_rough
      delta n e q om N cap w z L X F state hstate fifth hfifth p hp
    have hmod : N < a * (p :: fifth.selectedAfter).prod := by
      calc
        N < p ^ 6 := hlarge
        _ ≤ (p :: fifth.selectedAfter).prod := hrough
        _ = 1 * (p :: fifth.selectedAfter).prod := by simp
        _ ≤ a * (p :: fifth.selectedAfter).prod :=
          Nat.mul_le_mul_right _ ha1
    exact actual_receiver_fibre_zero_of_large N _ hmod

/-- Exact zero of the ORIGINAL PLUS-beta attachment for this literal
sixth p, for all original a occurrences. Not just a small-a cap. -/
theorem actual_large_sixth_plus_receiver_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hlarge : N < p ^ 6) :
    largeFifthPlusAttachment N cap w L X (receiverTest N)
      fifth.selectedAfter p = 0 := by
  unfold largeFifthPlusAttachment
  apply Finset.sum_eq_zero
  intro a ha
  have hz := actual_large_sixth_receiver_fibre_zero
    delta n e q om N cap w z L X (receiverTest N)
    state hstate fifth hfifth p hp a hlarge
  simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, hz]

/-- Finite List filter preserves the order and ALL repeated occurrences
of the actual suffix. It deletes only terms already proved zero. -/
private theorem list_sum_map_eq_filter_of_zero {α : Type*}
    (xs : List α) (keep : α → Prop) [DecidablePred keep] (f : α → ℝ)
    (h : ∀ x ∈ xs, ¬keep x → f x = 0) :
    (xs.map f).sum = ((xs.filter keep).map f).sum := by
  classical
  revert h
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      have ht : ∀ y ∈ xs, ¬keep y → f y = 0 := by
        intro y hy hn
        exact h y (by simp [hy]) hn
      by_cases hx : keep x
      · simp [hx, ih ht]
      · have hz : f x = 0 := h x (by simp) hx
        simp [hx, hz, ih ht]

/-- The actual signed kernel is EXACTLY its original sixth List with
the p^6>N zero terms removed. No artificial fifth state or new
sixth source is constructed. -/
theorem actual_common_sixth_receiver_eq_root_pruned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state) :
    commonLargeSixthKernel N cap w L X (receiverTest N) fifth =
      (((fifth.remainingAfter.filter (fun p => p ^ 6 ≤ N)).map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          largeFifthPlusAttachment N cap w L X (receiverTest N)
            fifth.selectedAfter p)).sum) := by
  unfold commonLargeSixthKernel
  apply list_sum_map_eq_filter_of_zero
  intro p hp hnot
  have hlarge : N < p ^ 6 := Nat.lt_of_not_ge hnot
  have hz := actual_large_sixth_plus_receiver_zero
    delta n e q om N cap w z L X state hstate fifth hfifth p hp hlarge
  simp [hz]

/-- The previous floor bound is now charged ONLY for p^6<=N.
This is a strictly more informative finite budget than paying for
every excluded sixth candidate with a positive floor estimate. -/
def rootPrunedSixthBudget (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (((fifth.remainingAfter.filter (fun p => p ^ 6 ≤ N)).map (fun p =>
    |signedTreeCoefficient true fifth.massAfter| *
      (∑ a ∈ largeFifthRosserIndices N cap w X fifth.selectedAfter,
        |actualSmallRosserPlus N cap w L a| *
          ((N / (a * (p :: fifth.selectedAfter).prod) : ℕ) : ℝ)))).sum)

private theorem list_abs_sum_le_map {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (h : ∀ x ∈ xs, |f x| ≤ b x) :
    |(xs.map f).sum| ≤ (xs.map b).sum := by
  revert h
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have hx : |f x| ≤ b x := h x (by simp)
      have ht : |(xs.map f).sum| ≤ (xs.map b).sum := by
        apply ih
        intro y hy
        exact h y (by simp [hy])
      exact (abs_add (f x) ((xs.map f).sum)).trans
        (add_le_add hx ht)

private theorem list_sum_map_le_map {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ b x) :
    (xs.map f).sum ≤ (xs.map b).sum := by
  revert h
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h x (by simp))
        (ih (by
          intro y hy
          exact h y (by simp [hy])))

/-- New true-source receiver kernel estimate after exact root pruning. -/
theorem actual_common_sixth_receiver_abs_le_root_pruned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state) :
    |commonLargeSixthKernel N cap w L X (receiverTest N) fifth| ≤
      rootPrunedSixthBudget N cap w L X fifth := by
  rw [actual_common_sixth_receiver_eq_root_pruned
    delta n e q om N cap w z L X state hstate fifth hfifth]
  unfold rootPrunedSixthBudget
  apply list_abs_sum_le_map
  intro p hp
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (actual_large_plus_receiver_abs_le_harmonic
      N cap w L X fifth.selectedAfter p)
    (abs_nonneg _)

/-- Only the actual true-source fifth-exclusive event can incur a
root-pruned bill. The impossible BOTH and direct-sixth syntactic cases
are zero, independently of any freshly invented policy mask. -/
def eventRootPrunedBudget (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly => rootPrunedSixthBudget N cap w L X fifth
      | .licensedOnly => rootPrunedSixthBudget N cap w L X fifth
      | .both => 0
  | .sixthFromBoth _ _ => 0

/-- Membership in the ORIGINAL reduced event source is essential here
to invoke actual fifth-rank history. -/
theorem actual_event_receiver_abs_le_root_pruned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state) :
    |commonSignedEventValue N cap w L X (receiverTest N) ev| ≤
      eventRootPrunedBudget N cap w L X ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, eventRootPrunedBudget, hk] using
            (actual_common_sixth_receiver_abs_le_root_pruned
              delta n e q om N cap w z L X state hstate fifth hev)
      | licensedOnly =>
          simpa [commonSignedEventValue, eventRootPrunedBudget, hk] using
            (actual_common_sixth_receiver_abs_le_root_pruned
              delta n e q om N cap w z L X state hstate fifth hev)
      | both =>
          simp [commonSignedEventValue, eventRootPrunedBudget, hk]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue, eventRootPrunedBudget]

def actualRootPrunedHarmonicBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state).map
        (eventRootPrunedBudget N cap w L X)).sum)).sum

/-- Replace the same ORIGINAL absolute stopped invoice; there is no
fourth outside invoice and no second copy of the stopped cost. -/
theorem actual_invoice_le_root_pruned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
      delta n e q om N cap w z L X (receiverTest N) ≤
    actualRootPrunedHarmonicBudget delta n e q om N cap w z L X := by
  unfold P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
    actualRootPrunedHarmonicBudget
  apply list_sum_map_le_map
  intro state hstate
  apply list_sum_map_le_map
  intro ev hev
  rw [actual_event_large_value_eq_common
    delta n e q om N cap w z L X (receiverTest N)
    state hstate ev hev]
  exact actual_event_receiver_abs_le_root_pruned
    delta n e q om N cap w z L X state hstate ev hev

/-- SAME physical signed rho and unchanged THREE old outside/producer
invoices, each paid exactly once. The only new improvement is the
proved p^6<=N carrier pruning in the first finite invoice. -/
theorem actual_full_physical_receiver_abs_le_root_pruned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon)
        (P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X
          (receiverTest N)) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon)
        (P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X
          (receiverTest N))| ≤
    actualRootPrunedHarmonicBudget delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X +
    ((P4AOriginalFull87RawTrimSignedHighQ.rawOutsideHighQInvoice
        delta e q om N cap w z ((N : ℝ) ^ epsilon) X (receiverTest N) +
      P4AOriginalFull87ThreeClassLeafInvoices.actualProducerThreeClassLeafBill
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X (receiverTest N)) +
      P4AOriginalFull87LicensedOutsideThreeInvoices.licensedOutsideHighQInvoice
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X (receiverTest N)) := by
  have hphys :=
    P4AOriginalFull87LargeTailInvoice.abs_full_physical_le_power_filtered_invoice
      delta n e q om N cap w z he hN epsilon heps X hX (receiverTest N)
  have hinvoice := actual_invoice_le_root_pruned
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
  linarith

end
end ImbalancedChen.P4AOriginalFull87SixthRootReceiver
