import ImbalancedChen.P4AOriginalFull87ActualBetaWeightedRoom
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A genuine ORIGINAL upper prime fibre can be reindexed by its complete
six-factor integer quotient. The preceding packet used this injection
only for an absolute beta-weighted majorant. Here we retain the SIGN
of the same literal PLUS-Rosser coefficient and obtain an EXACT
difference: the full admitted Rosser room minus precisely the
unoccupied quotient occurrences. This is not a prime distribution
estimate; the missing sum is an arithmetic obligation, not zero.

The second identity carries the signed difference through the original
ordered sixth-suffix List of one fifth-stopped history. The third binds
that list to an actual sharedRankFour parent and real receiver-generated
fifth occurrence. Neither the historical owner nor the RAW/LICENSED
filter is reconstructed. No new axioms or analytic input are used.
-/

namespace ImbalancedChen.P4AOriginalFull87SignedBetaMissingRoom
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FullUpperQuotientRoom
  (originalFullUpperNonzeroPrimeCarrier)
open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom original_rough_upper_nonzero_in_primitive_room)
open P4AOriginalFull87StoppedGlobalPrimeLedger (upperPrimeFibreTerm)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)

/-- Image of the *existing* nonzero original prime carrier, with the
original integer quotient and the full six-factor modulus. This is an
accounting image, not a replacement producer or a hypothesis. -/
def occupiedOriginalUpperBetaQuotients
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (originalFullUpperNonzeroPrimeCarrier N cap w L X pre p).image
    (fun P => (N - P) / (p :: pre).prod)

/-- Complement relative to the genuine full-modulus PLUS-support room.
A zero beta there has zero signed and absolute cost automatically. -/
def unoccupiedOriginalUpperBetaQuotients
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (actualPrimitiveRosserRoom N cap w L X pre p) \
    (occupiedOriginalUpperBetaQuotients N cap w L X pre p)

theorem occupied_original_upper_subset_actual_room
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    occupiedOriginalUpperBetaQuotients N cap w L X pre p ⊆
      actualPrimitiveRosserRoom N cap w L X pre p := by
  intro a ha
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
  change P ∈ (chenPrimePrefix N).filter
    (fun P => upperPrimeFibreTerm N cap w L X P pre p ≠ 0) at hP
  exact original_rough_upper_nonzero_in_primitive_room
    N cap w z L X P pre p hrough (Finset.mem_filter.mp hP).2

private theorem nonzero_original_upper_gate
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    2 * P < N ∧ X < N - P ∧
      (N - P) / (p :: pre).prod ∈
        P4AOriginalFull87PlusBetaPowerFilter.largeFifthRosserIndices
          N cap w X pre ∧
      ((N - P) / (p :: pre).prod) * (p :: pre).prod = N - P := by
  unfold upperPrimeFibreTerm at hnon
  split_ifs at hnon with hg
  · exact hg
  · contradiction

/-- Unlike the previous absolute majorant, this signed formula has NO
triangle loss. The only discarded terms are literal zero fibres. -/
theorem original_upper_signed_sum_eq_occupied_beta
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (∑ P ∈ chenPrimePrefix N,
      upperPrimeFibreTerm N cap w L X P pre p) =
    ∑ a ∈ occupiedOriginalUpperBetaQuotients N cap w L X pre p,
      actualSmallRosserPlus N cap w L a := by
  classical
  let b : ℕ := (p :: pre).prod
  let W : Finset ℕ := originalFullUpperNonzeroPrimeCarrier
    N cap w L X pre p
  let f : ℕ → ℕ := fun P => (N - P) / b
  have hinj : Set.InjOn f W := by
    intro P hP Q hQ heq
    have hPn : upperPrimeFibreTerm N cap w L X P pre p ≠ 0 :=
      (Finset.mem_filter.mp hP).2
    have hQn : upperPrimeFibreTerm N cap w L X Q pre p ≠ 0 :=
      (Finset.mem_filter.mp hQ).2
    have hp := nonzero_original_upper_gate N cap w L X P pre p hPn
    have hq := nonzero_original_upper_gate N cap w L X Q pre p hQn
    have hsame : N - P = N - Q := by
      calc
        N - P = f P * b := hp.2.2.2.symm
        _ = f Q * b := congrArg (fun a : ℕ => a * b) heq
        _ = N - Q := hq.2.2.2
    omega
  have hsupport :
      (∑ P ∈ chenPrimePrefix N,
        upperPrimeFibreTerm N cap w L X P pre p) =
      ∑ P ∈ W, upperPrimeFibreTerm N cap w L X P pre p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hz : upperPrimeFibreTerm N cap w L X P pre p = 0
    · simp [hz]
    · simp [hz]
  have hval (P : ℕ) (hP : P ∈ W) :
      upperPrimeFibreTerm N cap w L X P pre p =
      actualSmallRosserPlus N cap w L (f P) := by
    have hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0 :=
      (Finset.mem_filter.mp hP).2
    have hg := nonzero_original_upper_gate N cap w L X P pre p hnon
    simp [upperPrimeFibreTerm, hg, f, b]
  have himage :
      (∑ a ∈ W.image f, actualSmallRosserPlus N cap w L a) =
      (∑ P ∈ W, actualSmallRosserPlus N cap w L (f P)) := by
    exact Finset.sum_image (fun P hP Q hQ heq => hinj hP hQ heq)
  rw [hsupport]
  calc
    (∑ P ∈ W, upperPrimeFibreTerm N cap w L X P pre p) =
      ∑ P ∈ W, actualSmallRosserPlus N cap w L (f P) := by
        apply Finset.sum_congr rfl
        intro P hP
        exact hval P hP
    _ = ∑ a ∈ W.image f, actualSmallRosserPlus N cap w L a :=
      himage.symm
    _ = _ := rfl

/-- EXACT signed room discrepancy. In particular a cardinal or
absolute beta bound cannot silently be treated as a signed mean. -/
theorem original_upper_signed_eq_full_beta_sub_unoccupied
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    (∑ P ∈ chenPrimePrefix N,
      upperPrimeFibreTerm N cap w L X P pre p) =
    (∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
      actualSmallRosserPlus N cap w L a) -
    (∑ a ∈ unoccupiedOriginalUpperBetaQuotients
        N cap w L X pre p,
      actualSmallRosserPlus N cap w L a) := by
  have hsubset := occupied_original_upper_subset_actual_room
    N cap w z L X pre p hrough
  rw [original_upper_signed_sum_eq_occupied_beta]
  unfold unoccupiedOriginalUpperBetaQuotients
  rw [Finset.sum_sdiff hsubset]
  ring

/-- A List identity proved occurrence by occurrence, without a
Finset conversion (which would erase repeated sixth primes). -/
private theorem ordered_signed_difference {α : Type*}
    (xs : List α) (c : ℝ) (f g h : α → ℝ)
    (hfg : ∀ x ∈ xs, f x = g x - h x) :
    (xs.map (fun x => c * f x)).sum =
      (xs.map (fun x => c * g x)).sum -
        (xs.map (fun x => c * h x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hfg x (by simp)
      have ht : ∀ y ∈ xs, f y = g y - h y := by
        intro y hy
        exact hfg y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ih ht]
      ring

/-- Actual fifth sign and ORIGINAL sixth suffix, with a same-history
signed quotient complement. This keeps the source occurrence List. -/
theorem original_fifth_signed_beta_room_partition
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ)
    (hrough : ∀ p ∈ fifth.remainingAfter,
      ∀ r ∈ p :: fifth.selectedAfter,
        r ∈ roughPrimeUniverse N cap w z) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ P ∈ chenPrimePrefix N,
          upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p))).sum =
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
          fifth.selectedAfter p,
          actualSmallRosserPlus N cap w L a))).sum -
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ unoccupiedOriginalUpperBetaQuotients
          N cap w L X fifth.selectedAfter p,
          actualSmallRosserPlus N cap w L a))).sum := by
  apply ordered_signed_difference
  intro p hp
  exact original_upper_signed_eq_full_beta_sub_unoccupied
    N cap w z L X fifth.selectedAfter p (hrough p hp)

/-- Bind the previous signed identity to a REAL producer occurrence:
sharedRankFour dynamic parent, original fifth selected history,
and all ordered remaining sixth primes. No unrelated mask on BOTH. -/
theorem actual_parent_fifth_signed_beta_room_partition
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hev : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        L X (receiverTest N) state) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ P ∈ chenPrimePrefix N,
          upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p))).sum =
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ actualPrimitiveRosserRoom N cap w L X
          fifth.selectedAfter p,
          actualSmallRosserPlus N cap w L a))).sum -
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        (∑ a ∈ unoccupiedOriginalUpperBetaQuotients
          N cap w L X fifth.selectedAfter p,
          actualSmallRosserPlus N cap w L a))).sum := by
  have hjoined : fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
      roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough delta n e q om
        N cap w z L X (receiverTest N) state hstate
        (.fifthExclusive fifth) hev)
  have hrough : ∀ p ∈ fifth.remainingAfter,
      ∀ r ∈ p :: fifth.selectedAfter,
        r ∈ roughPrimeUniverse N cap w z := by
    intro p hp r hr
    rcases List.mem_cons.mp hr with hpr | hpre
    · subst r
      exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
    · have hrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hpre
      exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  exact original_fifth_signed_beta_room_partition
    N cap w z L X fifth hrough

end
end ImbalancedChen.P4AOriginalFull87SignedBetaMissingRoom
