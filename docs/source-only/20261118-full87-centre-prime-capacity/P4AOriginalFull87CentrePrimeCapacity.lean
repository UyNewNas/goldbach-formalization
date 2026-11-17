import ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The original centre-prime AP correction has a finite genuine capacity
at each COMPLETE modulus d if the Goldbach centre N is not prime.
The P=N exception makes the assumption essential: at prime N the
centre AP correction equals one even for moduli larger than N.
All estimates use the SAME frozen receiver-generated actual fifth events,
the same original beta coefficients, complete a*(p::pre).prod and
repeated sixth-carrier occurrences. No asymptotic payment is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87CentrePrimeCapacity
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail actual_stopped_primitive_density_gap_bound)
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest primeMass densityTest primitiveError modulusPrimeTerm)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The centre AP prime is already a centre divisor, exactly. -/
theorem centre_ap_le_centre_divisor_count (N d : ℕ) :
    chenCentrePrimeAPCount N N d ≤ chenPrimeDivisorCount N N := by
  classical
  have hsub :
      (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N) ⊆
        (chenPrimePrefix N).filter (fun P => P ∣ N) := by
    intro P hP
    obtain ⟨hpre, hcong, hdiv⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨hpre, hdiv⟩
  unfold chenCentrePrimeAPCount chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hsub

/-- For composite/non-prime N, every centre divisor P in the AP has P<N.
The positive difference N-P has quotient 1..N/d. Distinct P yield
distinct quotients. At d=0 there are no such P (unlike prime N). -/
theorem centre_ap_le_floor_of_nonprime (N d : ℕ)
    (hcomp : ¬ Nat.Prime N) :
    chenCentrePrimeAPCount N N d ≤ ((N / d : ℕ) : ℝ) := by
  classical
  let S : Finset ℕ :=
    (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N)
  change (S.card : ℝ) ≤ ((N / d : ℕ) : ℝ)
  by_cases hd : d = 0
  · subst d
    have hempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro P hP
      obtain ⟨hpre, hcong, _⟩ := Finset.mem_filter.mp hP
      obtain ⟨hPN, hp⟩ := mem_chenPrimePrefix.mp hpre
      have hdiv : (0 : ℕ) ∣ N - P :=
        (dvd_sub_iff_modEq_of_le hPN).mpr hcong
      have hz : N - P = 0 := by simpa using hdiv
      have heq : P = N := by omega
      apply hcomp
      simpa [heq] using hp
    simp [hempty]
  · have hdata : ∀ P ∈ S,
        0 < (N - P) / d ∧ (N - P) / d ≤ N / d := by
      intro P hP
      obtain ⟨hpre, hcong, _⟩ := Finset.mem_filter.mp hP
      obtain ⟨hPN, hp⟩ := mem_chenPrimePrefix.mp hpre
      have hne : P ≠ N := by
        intro heq
        apply hcomp
        simpa [heq] using hp
      have hlt : P < N := lt_of_le_of_ne hPN hne
      have hdiv : d ∣ N - P :=
        (dvd_sub_iff_modEq_of_le hPN).mpr hcong
      have hmul : (N - P) / d * d = N - P :=
        Nat.div_mul_cancel hdiv
      have hqpos : 0 < (N - P) / d := by
        by_contra hnot
        have hz : (N - P) / d = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hz] at hmul
        simp at hmul
        omega
      exact ⟨hqpos, Nat.div_le_div_right (Nat.sub_le N P)⟩
    let f : ℕ → ℕ := fun P => (N - P) / d - 1
    have hinj : Set.InjOn f S := by
      intro P hP Q hQ heq
      have hPpos := (hdata P hP).1
      have hQpos := (hdata Q hQ).1
      have hquot : (N - P) / d = (N - Q) / d := by
        change (N - P) / d - 1 = (N - Q) / d - 1 at heq
        omega
      have hPdiv : d ∣ N - P := by
        obtain ⟨hpre, hcong, _⟩ := Finset.mem_filter.mp hP
        exact (dvd_sub_iff_modEq_of_le
          (mem_chenPrimePrefix.mp hpre).1).mpr hcong
      have hQdiv : d ∣ N - Q := by
        obtain ⟨hpre, hcong, _⟩ := Finset.mem_filter.mp hQ
        exact (dvd_sub_iff_modEq_of_le
          (mem_chenPrimePrefix.mp hpre).1).mpr hcong
      have hsub : N - P = N - Q := by
        calc
          N - P = (N - P) / d * d := (Nat.div_mul_cancel hPdiv).symm
          _ = (N - Q) / d * d := by rw [hquot]
          _ = N - Q := Nat.div_mul_cancel hQdiv
      have hPle : P ≤ N :=
        (mem_chenPrimePrefix.mp (Finset.mem_filter.mp hP).1).1
      have hQle : Q ≤ N :=
        (mem_chenPrimePrefix.mp (Finset.mem_filter.mp hQ).1).1
      omega
    have hsubset : S.image f ⊆ Finset.range (N / d) := by
      intro k hk
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hk
      have h := hdata P hP
      simp only [Finset.mem_range]
      omega
    have hcard : S.card ≤ N / d := by
      calc
        S.card = (S.image f).card :=
          (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (N / d)).card := Finset.card_le_card hsubset
        _ = N / d := by simp
    exact_mod_cast hcard

/-- A finite *minimum*, not an assumed analytic inequality. -/
def centreCapacity (N d : ℕ) : ℝ :=
  min (chenPrimeDivisorCount N N) (((N / d : ℕ) : ℝ))

theorem centreCapacity_nonneg (N d : ℕ) : 0 ≤ centreCapacity N d := by
  unfold centreCapacity chenPrimeDivisorCount
  positivity

theorem centre_abs_le_capacity (N d : ℕ)
    (hcomp : ¬ Nat.Prime N) :
    |chenCentrePrimeAPCount N N d| ≤ centreCapacity N d := by
  have hnonneg : 0 ≤ chenCentrePrimeAPCount N N d := by
    unfold chenCentrePrimeAPCount
    positivity
  rw [abs_of_nonneg hnonneg]
  exact le_min
    (centre_ap_le_centre_divisor_count N d)
    (centre_ap_le_floor_of_nonprime N d hcomp)

theorem highq_centre_abs_le_capacity (N X d : ℕ)
    (hcomp : ¬ Nat.Prime N) :
    |highQTest X (chenCentrePrimeAPCount N N) d| ≤
      centreCapacity N d := by
  by_cases h : X < d
  · simpa [highQTest, h] using centre_abs_le_capacity N d hcomp
  · simp [highQTest, h, centreCapacity_nonneg]

/-- The old original Rosser support, all full a*b moduli, no altered p list. -/
def centreAttachmentBudget (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ largeFifthRosserIndices N cap w X pre,
    |actualSmallRosserPlus N cap w L a| *
      centreCapacity N (a * (p :: pre).prod)

theorem large_plus_centre_abs_le_capacity
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (hcomp : ¬ Nat.Prime N) :
    |largeFifthPlusAttachment N cap w L X
      (chenCentrePrimeAPCount N N) pre p| ≤
      centreAttachmentBudget N cap w L X pre p := by
  unfold largeFifthPlusAttachment centreAttachmentBudget
  calc
    |∑ a ∈ largeFifthRosserIndices N cap w X pre,
      actualSmallRosserPlus N cap w L a *
        highQTest X (chenCentrePrimeAPCount N N)
          (a * (p :: pre).prod)|
      ≤ ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a *
          highQTest X (chenCentrePrimeAPCount N N)
            (a * (p :: pre).prod)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        |actualSmallRosserPlus N cap w L a| *
          centreCapacity N (a * (p :: pre).prod) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (highq_centre_abs_le_capacity
          N X (a * (p :: pre).prod) hcomp) (abs_nonneg _)

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

/-- The exact ordered post-fifth sixth carrier with signed mass. -/
def sixthCentreBudget (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) : ℝ :=
  (fifth.remainingAfter.map (fun p =>
    |signedTreeCoefficient true fifth.massAfter| *
      centreAttachmentBudget N cap w L X fifth.selectedAfter p)).sum

theorem common_sixth_centre_abs_le_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) (hcomp : ¬ Nat.Prime N) :
    |commonLargeSixthKernel N cap w L X
      (chenCentrePrimeAPCount N N) fifth| ≤
      sixthCentreBudget N cap w L X fifth := by
  unfold commonLargeSixthKernel sixthCentreBudget
  apply list_abs_sum_le_map
  intro p hp
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (large_plus_centre_abs_le_capacity
      N cap w L X fifth.selectedAfter p hcomp) (abs_nonneg _)

def eventCentreBudget (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      match fifth.kind with
      | .rawOnly => sixthCentreBudget N cap w L X fifth
      | .licensedOnly => sixthCentreBudget N cap w L X fifth
      | .both => 0
  | .sixthFromBoth _ _ => 0

theorem common_event_centre_abs_le_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) (hcomp : ¬ Nat.Prime N) :
    |commonSignedEventValue N cap w L X
      (chenCentrePrimeAPCount N N) ev| ≤
      eventCentreBudget N cap w L X ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, eventCentreBudget, hk] using
            (common_sixth_centre_abs_le_budget N cap w L X fifth hcomp)
      | licensedOnly =>
          simpa [commonSignedEventValue, eventCentreBudget, hk] using
            (common_sixth_centre_abs_le_budget N cap w L X fifth hcomp)
      | both =>
          simp [commonSignedEventValue, eventCentreBudget, hk]
  | sixthFromBoth pre inner =>
      simp [commonSignedEventValue, eventCentreBudget]

/-- Reuses the exact original receiverTest-generated events, not a second
prime-divisor producer. Counts every original occurrence separately. -/
def actualCentreCapacityBudget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state).map
        (eventCentreBudget N cap w L X)).sum)).sum

theorem actual_fixed_fifth_centre_abs_le_capacity
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (hcomp : ¬ Nat.Prime N) :
    |actualFixedSignedFifthTail delta n e q om N cap w z L X
      (chenCentrePrimeAPCount N N)| ≤
      actualCentreCapacityBudget delta n e q om N cap w z L X := by
  unfold actualFixedSignedFifthTail actualCentreCapacityBudget
  apply list_abs_sum_le_map
  intro state hstate
  apply list_abs_sum_le_map
  intro ev hev
  exact common_event_centre_abs_le_budget N cap w L X ev hcomp

/-- Only the previously present centre correction is charged once.
Neither primitive discrepancy nor modulus-prime error is hidden,
and the original outside/producer/licensed-outside bills are not repaid. -/
theorem actual_stopped_density_gap_centre_capacity
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hcomp : ¬ Nat.Prime N) :
    |(rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      primeMass N * actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X densityTest| ≤
    |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (primitiveError N)| +
    |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (modulusPrimeTerm N)| +
    actualCentreCapacityBudget
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X := by
  have hgap :=
    actual_stopped_primitive_density_gap_bound
      delta n e q om N cap w z he hN epsilon heps X hX
  have hcentre :=
    actual_fixed_fifth_centre_abs_le_capacity
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X hcomp
  exact hgap.trans (add_le_add_left hcentre _)

end
end ImbalancedChen.P4AOriginalFull87CentrePrimeCapacity
