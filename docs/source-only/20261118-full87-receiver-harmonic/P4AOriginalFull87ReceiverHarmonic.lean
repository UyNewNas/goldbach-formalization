import ImbalancedChen.P4AOriginalFull87CommonSixthSignedKernel
import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A genuinely quantitative, elementary bound on the SAME original full-87
fifth-exclusive signed high-q continuation when its arithmetic test is
the ACTUAL target-deleted prime-receiver fibre, not an arbitrary F.

The key new payment is a sharp finite fibre count: for every FULL physical
modulus d (including d=0), receiverTest N d <= N / d (Nat floor division).
The map n |-> n/d - 1 injects the ACTUAL positive receiver fibre into
Finset.range (N/d). No AP equidistribution input, divisor majorant, new
tree producer or reserve is used.

The full beta, original sixth p occurrences, signed mass and three old
outside invoices are preserved. The result is an explicit finite harmonic
invoice, NOT yet o(H_N), a PP modulus licence, or a closed P1.4 node.
-/

namespace ImbalancedChen.P4AOriginalFull87ReceiverHarmonic
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue
   actual_event_large_value_eq_common
   actual_stopped_difference_eq_common_signed_sixth_kernel)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices
   largeFifthOneSidedEventValue)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- Each receiver is a strictly positive integer <= N. The map
n -> n/d - 1 is injective on the divisibility fibre and lands in
[0,N/d). This gives a floor bound, WITHOUT a prime distribution theorem.
The d=0 fibre is empty because the original receiver zero is deleted. -/
theorem actual_receiver_fibre_le_floor (N d : ℕ) :
    receiverTest N d ≤ ((N / d : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ :=
    (chenPrimeReceiverSource N).filter (fun n => d ∣ n)
  change (S.card : ℝ) ≤ ((N / d : ℕ) : ℝ)
  by_cases hd : d = 0
  · subst d
    have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      have hsrc : n ∈ chenPrimeReceiverSource N :=
        (Finset.mem_filter.mp hn).1
      have hdiv : 0 ∣ n := (Finset.mem_filter.mp hn).2
      have hnzero : n = 0 := by simpa using hdiv
      exact (Nat.ne_of_gt (chenPrimeReceiverSource_data hsrc).1) hnzero
    simp [hempty]
  · have hdata : ∀ n ∈ S,
        0 < n / d ∧ n / d ≤ N / d := by
      intro n hn
      obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnpos, hnle, _⟩ := chenPrimeReceiverSource_data hsrc
      have hmul : n / d * d = n := Nat.div_mul_cancel hdiv
      have hquotpos : 0 < n / d := by
        by_contra hnot
        have hz : n / d = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hz] at hmul
        simp at hmul
        omega
      exact ⟨hquotpos, Nat.div_le_div_right hnle⟩
    let f : ℕ → ℕ := fun n => n / d - 1
    have hinj : Set.InjOn f S := by
      intro x hx y hy hxy
      have hxpos := (hdata x hx).1
      have hypos := (hdata y hy).1
      have hquot : x / d = y / d := by
        change x / d - 1 = y / d - 1 at hxy
        omega
      calc
        x = x / d * d :=
          (Nat.div_mul_cancel (Finset.mem_filter.mp hx).2).symm
        _ = y / d * d := by rw [hquot]
        _ = y := Nat.div_mul_cancel (Finset.mem_filter.mp hy).2
    have hsub : S.image f ⊆ Finset.range (N / d) := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      have hbound := hdata n hn
      change n / d - 1 < N / d
      omega
    have hc : S.card ≤ N / d := by
      calc
        S.card = (S.image f).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (N / d)).card := Finset.card_le_card hsub
        _ = N / d := by simp
    exact_mod_cast hc

/-- The receiver fibre is also primitive at the full physical modulus:
if d divides an ACTUAL receiver then gcd(d,N)=1. This does not license
a fixed analytic theta or a smooth-singleton restriction. -/
theorem actual_receiver_fibre_zero_of_nonprimitive
    (N d : ℕ) (hbad : ¬Nat.Coprime d N) :
    receiverTest N d = 0 := by
  classical
  unfold receiverTest
  have hempty :
      (chenPrimeReceiverSource N).filter (fun n => d ∣ n) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
    exact hbad ((chenPrimeReceiverSource_data hsrc).2.2.of_dvd_left hdiv)
  simp [hempty]

/-- A nonzero receiver fibre has d<=N. The zero receiver has NOT been
included; otherwise this elementary conclusion would be false. -/
theorem actual_receiver_fibre_zero_of_large
    (N d : ℕ) (hlarge : N < d) :
    receiverTest N d = 0 := by
  classical
  unfold receiverTest
  have hempty :
      (chenPrimeReceiverSource N).filter (fun n => d ∣ n) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro n hn
    obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hpos, hle, _⟩ := chenPrimeReceiverSource_data hsrc
    have hdn : d ≤ n := Nat.le_of_dvd hpos hdiv
    omega
  simp [hempty]

private theorem receiver_nonneg (N d : ℕ) :
    0 ≤ receiverTest N d := by
  unfold receiverTest
  exact Nat.cast_nonneg _

/-- The strict high-q test contributes at most floor(N/d), including
its forbidden endpoint and the zero modulus. -/
theorem actual_highq_receiver_abs_le_floor (N X d : ℕ) :
    |highQTest X (receiverTest N) d| ≤ ((N / d : ℕ) : ℝ) := by
  by_cases h : X < d
  · simp only [highQTest, if_pos h]
    rw [abs_of_nonneg (receiver_nonneg N d)]
    exact actual_receiver_fibre_le_floor N d
  · simp [highQTest, h]

/-- The ORIGINAL PLUS-Rosser sum for one actual sixth-prime occurrence
is paid at full d=a*(p::pre).prod. No rough-only modulus substitution,
sign deletion, or occurrence-deduplication is made. -/
theorem actual_large_plus_receiver_abs_le_harmonic
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |largeFifthPlusAttachment N cap w L X (receiverTest N) pre p| ≤
      ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a| *
          ((N / (a * (p :: pre).prod) : ℕ) : ℝ) := by
  unfold largeFifthPlusAttachment
  calc
    |∑ a ∈ largeFifthRosserIndices N cap w X pre,
        actualSmallRosserPlus N cap w L a *
          highQTest X (receiverTest N) (a * (p :: pre).prod)|
      ≤ ∑ a ∈ largeFifthRosserIndices N cap w X pre,
          |actualSmallRosserPlus N cap w L a *
            highQTest X (receiverTest N) (a * (p :: pre).prod)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a| *
          ((N / (a * (p :: pre).prod) : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (actual_highq_receiver_abs_le_floor N X
            (a * (p :: pre).prod))
          (abs_nonneg _)

/-- A concrete *quantitative* bound for the original common sixth kernel,
with its real signed incoming mass and the untouched repeated p list.
No analytic estimate of the number of events is inferred. -/
def sixthHarmonicBudget (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (fifth.remainingAfter.map (fun p =>
    |signedTreeCoefficient true fifth.massAfter| *
      (∑ a ∈ largeFifthRosserIndices N cap w X fifth.selectedAfter,
        |actualSmallRosserPlus N cap w L a| *
          ((N / (a * (p :: fifth.selectedAfter).prod) : ℕ) : ℝ)))).sum

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

/-- The crucial new finite numerical inequality on the SAME sixth
kernel, not a re-expression of an old fifth-power zero condition. -/
theorem actual_common_sixth_receiver_abs_le_harmonic
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    |commonLargeSixthKernel N cap w L X (receiverTest N) fifth| ≤
      sixthHarmonicBudget N cap w L X fifth := by
  unfold commonLargeSixthKernel sixthHarmonicBudget
  apply list_abs_sum_le_map
  intro p hp
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (actual_large_plus_receiver_abs_le_harmonic
      N cap w L X fifth.selectedAfter p)
    (abs_nonneg _)

/-- Syntactic unreachable cases are charged zero only for the common
signed expression, whose equality to the REAL event requires the
earlier actual-source theorems. -/
def eventHarmonicBudget (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth => sixthHarmonicBudget N cap w L X fifth
  | .sixthFromBoth _ _ => 0

theorem common_event_receiver_abs_le_harmonic
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    |commonSignedEventValue N cap w L X (receiverTest N) ev| ≤
      eventHarmonicBudget N cap w L X ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, eventHarmonicBudget, hk] using
            (actual_common_sixth_receiver_abs_le_harmonic
              N cap w L X fifth)
      | licensedOnly =>
          simpa [commonSignedEventValue, eventHarmonicBudget, hk] using
            (actual_common_sixth_receiver_abs_le_harmonic
              N cap w L X fifth)
      | both =>
          simp [commonSignedEventValue, eventHarmonicBudget, hk,
            sixthHarmonicBudget]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue, eventHarmonicBudget]

/-- The actual shared-rank-four and reduced original fifth/sixth
occurrence lists; no new event population. All full a*b floor factors
are evaluated at the original literal sixth suffixes. -/
def actualReceiverHarmonicBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state).map
      (eventHarmonicBudget N cap w L X)).sum)).sum

/-- A new unconditional finite harmonic upper bound for the original
SAME-rho stopped signed discrepancy on the actual fifthExclusive band.
The only hypotheses are the FROZEN earlier stopped-reduction hypotheses. -/
theorem actual_stopped_receiver_abs_le_harmonic
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N)| ≤
    actualReceiverHarmonicBudget delta n e q om N cap w z
      ((N : ℝ) ^ epsilon) X := by
  rw [actual_stopped_difference_eq_common_signed_sixth_kernel
    delta n e q om N cap w z he hN epsilon heps X hX (receiverTest N)]
  apply list_abs_sum_le_map
  intro state hstate
  apply list_abs_sum_le_map
  intro ev hev
  exact common_event_receiver_abs_le_harmonic
    N cap w ((N : ℝ) ^ epsilon) X ev

/-- The preceding original absolute stopped invoice is bounded by
the SAME harmonic event bill. This is not a separate second invoice. -/
theorem actual_receiver_power_filtered_invoice_le_harmonic
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
      delta n e q om N cap w z L X (receiverTest N) ≤
    actualReceiverHarmonicBudget delta n e q om N cap w z L X := by
  unfold P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
    actualReceiverHarmonicBudget
  apply list_sum_map_le_map
  intro state hstate
  apply list_sum_map_le_map
  intro ev hev
  rw [actual_event_large_value_eq_common
    delta n e q om N cap w z L X (receiverTest N) state hstate ev hev]
  exact common_event_receiver_abs_le_harmonic N cap w L X ev

/-- Full physical high-q control with the THREE old outside/producer
invoices charged once. No fake o(H_N) or PP closure is asserted. -/
theorem actual_full_physical_receiver_abs_le_harmonic
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
        (highQTest X (receiverTest N)) -
      P4AOriginalLicensedSixthSignedLedger.physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z ((N : ℝ) ^ epsilon)
        (highQTest X (receiverTest N))| ≤
    actualReceiverHarmonicBudget delta n e q om N cap w z
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
  have hinvoice :=
    actual_receiver_power_filtered_invoice_le_harmonic
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
  linarith

end
end ImbalancedChen.P4AOriginalFull87ReceiverHarmonic
