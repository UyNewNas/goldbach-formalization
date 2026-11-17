import ImbalancedChen.P4AOriginalFull87ReceiverHarmonic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Genuine improvement of the actual receiver's full-modulus harmonic budget:
for every receiver n in the original target-deleted source with d|n,
the quotient k=n/d is NOT merely in 1..N/d; it is coprime to N.

This replaces each previous floor(N/d) cost by the smaller finite count
  #{k : 1<=k<=N/d AND Coprime k N}.
It is not a renamed floor bound: for N=12, d=5 it is 1 instead of 2.
Every full a*b modulus and all original fifth/sixth p occurrences, beta
coefficients, signed mass, fourth parent and old THREE outside bills
are preserved. No external prime distribution, new analytic axiom,
invented event source or density reserve is invoked.

This is an actual, strictly sharper finite arithmetic upper bound, not
a proof the complete bill is o(H_N), nor a PP theta admissibility claim.
-/

namespace ImbalancedChen.P4AOriginalFull87CoprimeQuotient
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87ReceiverHarmonic
  (actual_receiver_fibre_le_floor)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue actual_event_large_value_eq_common)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)

/-- Arithmetic quotient capacity at the actual centre N: no PNT,
coprime-density approximation or passage to N/phi(N). -/
def coprimeQuotientCount (N d : ℕ) : ℝ :=
  (((Finset.Icc 1 (N / d)).filter (fun k => Nat.Coprime k N)).card : ℝ)

/-- Actual receiver fibre injection into coprime positive quotients.
Unlike the previous injection into all 1..N/d, this uses the original
chenPrimeReceiverSource_data coprimality of n with N. The map
n |-> n/d is injective because d|n; the d=0 case is separate. -/
theorem actual_receiver_fibre_le_coprime_quotients (N d : ℕ) :
    receiverTest N d ≤ coprimeQuotientCount N d := by
  classical
  let S : Finset ℕ :=
    (chenPrimeReceiverSource N).filter (fun n => d ∣ n)
  let Q : Finset ℕ :=
    (Finset.Icc 1 (N / d)).filter (fun k => Nat.Coprime k N)
  change (S.card : ℝ) ≤ (Q.card : ℝ)
  by_cases hd : d = 0
  · subst d
    have hzero : receiverTest N 0 = 0 := by
      have hle : receiverTest N 0 ≤ 0 := by
        simpa using actual_receiver_fibre_le_floor N 0
      have hnonneg : 0 ≤ receiverTest N 0 := by
        unfold receiverTest
        exact Nat.cast_nonneg _
      exact le_antisymm hle hnonneg
    have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
      have h0 : n = 0 := by simpa using hdiv
      exact (Nat.ne_of_gt (chenPrimeReceiverSource_data hsrc).1) h0
    simp [hempty, Q]
  · have hdata : ∀ n ∈ S,
        0 < n / d ∧ n / d ≤ N / d ∧ Nat.Coprime (n / d) N := by
      intro n hn
      obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnpos, hnle, hcop⟩ := chenPrimeReceiverSource_data hsrc
      have hmul : n / d * d = n := Nat.div_mul_cancel hdiv
      have hqpos : 0 < n / d := by
        by_contra hnot
        have hz : n / d = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hz] at hmul
        simp at hmul
        omega
      have hqdiv : n / d ∣ n := by
        refine ⟨d, ?_⟩
        exact hmul.symm
      exact ⟨hqpos, Nat.div_le_div_right hnle,
        hcop.of_dvd_left hqdiv⟩
    have hinj : Set.InjOn (fun n : ℕ => n / d) S := by
      intro x hx y hy hxy
      calc
        x = x / d * d :=
          (Nat.div_mul_cancel (Finset.mem_filter.mp hx).2).symm
        _ = y / d * d := by rw [hxy]
        _ = y := Nat.div_mul_cancel (Finset.mem_filter.mp hy).2
    have hsubset : S.image (fun n : ℕ => n / d) ⊆ Q := by
      intro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hpos, hle, hcop⟩ := hdata n hn
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hcop⟩
    have hcard : S.card ≤ Q.card := by
      calc
        S.card = (S.image (fun n : ℕ => n / d)).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ Q.card := Finset.card_le_card hsubset
    exact_mod_cast hcard

/-- The new quotient capacity never exceeds the former floor capacity.
This is an actual Finset injection, not an asserted analytic density. -/
theorem coprimeQuotientCount_le_floor (N d : ℕ) :
    coprimeQuotientCount N d ≤ ((N / d : ℕ) : ℝ) := by
  classical
  let Q : Finset ℕ :=
    (Finset.Icc 1 (N / d)).filter (fun k => Nat.Coprime k N)
  change (Q.card : ℝ) ≤ ((N / d : ℕ) : ℝ)
  have hinj : Set.InjOn (fun k : ℕ => k - 1) Q := by
    intro x hx y hy hxy
    have hx1 : 1 ≤ x :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1
    have hy1 : 1 ≤ y :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1
    dsimp at hxy
    omega
  have hsub : Q.image (fun k : ℕ => k - 1) ⊆
      Finset.range (N / d) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hklo, hkle⟩ :=
      Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    change k - 1 < N / d
    omega
  have hc : Q.card ≤ N / d := by
    calc
      Q.card = (Q.image (fun k : ℕ => k - 1)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (N / d)).card := Finset.card_le_card hsub
      _ = N / d := by simp
  exact_mod_cast hc

private theorem receiver_nonneg (N d : ℕ) :
    0 ≤ receiverTest N d := by
  unfold receiverTest
  exact Nat.cast_nonneg _

/-- The strict original high-q terminal test is bounded at the
COMPLETE physical d by the more selective coprime quotient capacity. -/
theorem actual_highq_receiver_abs_le_coprime_quotients
    (N X d : ℕ) :
    |P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest
      X (receiverTest N) d| ≤ coprimeQuotientCount N d := by
  by_cases h : X < d
  · simp only [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, if_pos h]
    rw [abs_of_nonneg (receiver_nonneg N d)]
    exact actual_receiver_fibre_le_coprime_quotients N d
  · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, h,
      coprimeQuotientCount]

/-- The original PLUS beta at one actual sixth p, with full
d=a*(p::pre).prod and the existing strict high-q boundary. -/
theorem actual_large_plus_receiver_abs_le_coprime_quotients
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |largeFifthPlusAttachment N cap w L X (receiverTest N) pre p| ≤
      ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a| *
          coprimeQuotientCount N (a * (p :: pre).prod) := by
  unfold largeFifthPlusAttachment
  calc
    |∑ a ∈ largeFifthRosserIndices N cap w X pre,
        actualSmallRosserPlus N cap w L a *
          P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest
            X (receiverTest N) (a * (p :: pre).prod)| ≤
      ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a *
          P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest
            X (receiverTest N) (a * (p :: pre).prod)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ largeFifthRosserIndices N cap w X pre,
          |actualSmallRosserPlus N cap w L a| *
            coprimeQuotientCount N (a * (p :: pre).prod) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (actual_highq_receiver_abs_le_coprime_quotients
          N X (a * (p :: pre).prod))
        (abs_nonneg _)

/-- Non-duplicated sixth occurrence List with genuinely better full-q
weights than the prior floor invoice. -/
def sixthCoprimeQuotientBudget (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (fifth.remainingAfter.map (fun p =>
    |signedTreeCoefficient true fifth.massAfter| *
      (∑ a ∈ largeFifthRosserIndices N cap w X fifth.selectedAfter,
        |actualSmallRosserPlus N cap w L a| *
          coprimeQuotientCount N
            (a * (p :: fifth.selectedAfter).prod)))).sum

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

/-- A strictly tighter actual receiver bound on the SAME common
signed sixth kernel; no additional beta mask or source change. -/
theorem actual_common_sixth_receiver_abs_le_coprime_quotients
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    |commonLargeSixthKernel N cap w L X (receiverTest N) fifth| ≤
      sixthCoprimeQuotientBudget N cap w L X fifth := by
  unfold commonLargeSixthKernel sixthCoprimeQuotientBudget
  apply list_abs_sum_le_map
  intro p hp
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (actual_large_plus_receiver_abs_le_coprime_quotients
      N cap w L X fifth.selectedAfter p)
    (abs_nonneg _)

def eventCoprimeQuotientBudget
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly => sixthCoprimeQuotientBudget N cap w L X fifth
      | .licensedOnly => sixthCoprimeQuotientBudget N cap w L X fifth
      | .both => 0
  | .sixthFromBoth _ _ => 0

theorem common_event_receiver_abs_le_coprime_quotients
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    |commonSignedEventValue N cap w L X (receiverTest N) ev| ≤
      eventCoprimeQuotientBudget N cap w L X ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, eventCoprimeQuotientBudget, hk] using
            (actual_common_sixth_receiver_abs_le_coprime_quotients
              N cap w L X fifth)
      | licensedOnly =>
          simpa [commonSignedEventValue, eventCoprimeQuotientBudget, hk] using
            (actual_common_sixth_receiver_abs_le_coprime_quotients
              N cap w L X fifth)
      | both =>
          simp [commonSignedEventValue, eventCoprimeQuotientBudget, hk]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue, eventCoprimeQuotientBudget]

def actualCoprimeQuotientBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state).map
        (eventCoprimeQuotientBudget N cap w L X)).sum)).sum

/-- Old power-filtered stopped invoice replaced exactly ONCE by the
actual coprime-quotient budget on the identical ordered event source. -/
theorem actual_invoice_le_coprime_quotient_budget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
      delta n e q om N cap w z L X (receiverTest N) ≤
    actualCoprimeQuotientBudget delta n e q om N cap w z L X := by
  unfold P4AOriginalFull87LargeTailInvoice.actualPowerFilteredExclusiveAbsInvoice
    actualCoprimeQuotientBudget
  apply list_sum_map_le_map
  intro state hstate
  apply list_sum_map_le_map
  intro ev hev
  rw [actual_event_large_value_eq_common
    delta n e q om N cap w z L X (receiverTest N)
    state hstate ev hev]
  exact common_event_receiver_abs_le_coprime_quotients N cap w L X ev

/-- Same physical RAW-LICENSED rho with its THREE pre-existing
outside/producer/licensed-outside invoices charged once. This does
not infer a frozen H_N saving or fixed theta<1 from elementary counts. -/
theorem actual_full_physical_receiver_abs_le_coprime_quotients
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
    actualCoprimeQuotientBudget delta n e q om N cap w z
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
  have hinvoice := actual_invoice_le_coprime_quotient_budget
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
  linarith

/-- A genuine comparison with the PRECEDING original harmonic bill.
Unlike root pruning beyond p^6>N (where that bill is already zero),
the coprime quotient capacity can be strictly smaller for nonzero
retained moduli and its proof pays no new outside invoice. -/
theorem sixth_coprime_budget_le_old_harmonic
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    sixthCoprimeQuotientBudget N cap w L X fifth ≤
      P4AOriginalFull87ReceiverHarmonic.sixthHarmonicBudget
        N cap w L X fifth := by
  unfold sixthCoprimeQuotientBudget
    P4AOriginalFull87ReceiverHarmonic.sixthHarmonicBudget
  apply list_sum_map_le_map
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left
    (coprimeQuotientCount_le_floor N
      (a * (p :: fifth.selectedAfter).prod))
    (abs_nonneg _)

theorem event_coprime_budget_le_old_harmonic
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    eventCoprimeQuotientBudget N cap w L X ev ≤
      P4AOriginalFull87ReceiverHarmonic.eventHarmonicBudget
        N cap w L X ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [eventCoprimeQuotientBudget,
            P4AOriginalFull87ReceiverHarmonic.eventHarmonicBudget, hk] using
            (sixth_coprime_budget_le_old_harmonic N cap w L X fifth)
      | licensedOnly =>
          simpa [eventCoprimeQuotientBudget,
            P4AOriginalFull87ReceiverHarmonic.eventHarmonicBudget, hk] using
            (sixth_coprime_budget_le_old_harmonic N cap w L X fifth)
      | both => simp [eventCoprimeQuotientBudget,
          P4AOriginalFull87ReceiverHarmonic.eventHarmonicBudget, hk]
  | sixthFromBoth fifthSelected inner =>
      simp [eventCoprimeQuotientBudget,
        P4AOriginalFull87ReceiverHarmonic.eventHarmonicBudget]

theorem actual_coprime_budget_le_old_harmonic
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualCoprimeQuotientBudget delta n e q om N cap w z L X ≤
      P4AOriginalFull87ReceiverHarmonic.actualReceiverHarmonicBudget
        delta n e q om N cap w z L X := by
  unfold actualCoprimeQuotientBudget
    P4AOriginalFull87ReceiverHarmonic.actualReceiverHarmonicBudget
  apply list_sum_map_le_map
  intro state hstate
  apply list_sum_map_le_map
  intro ev hev
  exact event_coprime_budget_le_old_harmonic N cap w L X ev

end
end ImbalancedChen.P4AOriginalFull87CoprimeQuotient
