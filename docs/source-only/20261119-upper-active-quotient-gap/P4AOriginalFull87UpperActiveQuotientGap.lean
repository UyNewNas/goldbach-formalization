import ImbalancedChen.P4AOriginalFull87UpperPrimeActiveLevel
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The actual upper-half LONG term has the exact quotient
  a = (N-P)/b, b=(p::pre).prod,
and a nonzero term is supported in the genuine upper-Rosser active
lattice. Unlike a real-valued size inequality alone, its integral
quotient must lie in the HALF-OPEN INTEGER BAND

  floor(N/(2*b)) + 1 <= a < ceil(L).

The full-modulus lattice itself forces b>0 whenever nonempty, so
there is no extra positivity premise. Reindex the finite upper-bound
carrier injectively by a, derive an explicit integer-gap invoice, and
obtain a strictly integral local zero test. The ORIGINAL term is not
masked or replaced. The existing active-card invoice is still the
stronger literal count; the new formula is a computable envelope and
must never be paid in addition to it.

No smooth PP, asymptotic estimate, producer X/z bound, new physical
coefficient, or extra assertion about a prime distribution is used.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperActiveQuotientGap
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87UpperPrimeActiveLevel
  (longPrimeActiveRosserWindow
   long_fibre_nonzero_in_active_rosser_window
   original_long_prime_sum_abs_le_active_rosser_card
   original_fifth_ordered_long_prime_active_budget)
open P4AOriginalFull87UpperPrimeModulusLattice
  (longPrimeModulusWindow)
open P4AOriginalFull87UpperPrimeWindowWidth
  (longPrimeWindow)
open P4AOriginalFull87UpperPrimeShortBoundary
  (upperPrimeLongBoundaryTerm)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)

/-- Any element of the PREVIOUS unchanged active bounding carrier
already forces its literal complete modulus b to be positive.
Thus quotient reindexing introduces no independent b>0 hypothesis. -/
theorem active_window_forces_positive_full_modulus
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hP : P ∈ longPrimeActiveRosserWindow N cap w L X pre p) :
    0 < (p :: pre).prod := by
  have hmod :
      P ∈ longPrimeModulusWindow N X pre p :=
    (Finset.mem_filter.mp hP).1
  have hwin : P ∈ longPrimeWindow N X p :=
    (Finset.mem_filter.mp hmod).1
  have hupper : P < (N + 1) / 2 :=
    (Finset.mem_Ico.mp hwin).2
  have hdvd : (p :: pre).prod ∣ N - P :=
    (Finset.mem_filter.mp hmod).2
  by_contra hn
  have hb0 : (p :: pre).prod = 0 :=
    Nat.eq_zero_of_not_pos hn
  have hzero : N - P = 0 := by
    simpa [hb0] using hdvd
  omega

/-- Every bounding-carrier prime P has a unique exact INTEGRAL
quotient lying strictly above N/(2*b) and strictly below the real
Rosser level. The strict half-boundary is not rounded twice. -/
theorem active_window_quotient_in_integer_band
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hP : P ∈ longPrimeActiveRosserWindow N cap w L X pre p) :
    (N - P) / (p :: pre).prod ∈
      Finset.Ico (N / (2 * (p :: pre).prod) + 1) (Nat.ceil L) := by
  let b := (p :: pre).prod
  let a := (N - P) / b
  have hmod : P ∈ longPrimeModulusWindow N X pre p :=
    (Finset.mem_filter.mp hP).1
  have hwin : P ∈ longPrimeWindow N X p :=
    (Finset.mem_filter.mp hmod).1
  have hupper : P < (N + 1) / 2 :=
    (Finset.mem_Ico.mp hwin).2
  have hhalf : 2 * P < N := by omega
  have hPle : P ≤ N := by omega
  have hdvd : b ∣ N - P :=
    (Finset.mem_filter.mp hmod).2
  have hab : a * b = N - P :=
    Nat.div_mul_cancel hdvd
  have hN : N = P + a * b := by omega
  have hstrict : N < a * (2 * b) := by
    calc
      N < 2 * (a * b) := by omega
      _ = a * (2 * b) := by ring
  have hbpos : 0 < b :=
    active_window_forces_positive_full_modulus
      N cap w L X P pre p hP
  have hlower : N / (2 * b) < a :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * b)).2 hstrict
  have haL : (a : ℝ) < L :=
    (Finset.mem_filter.mp hP).2.2
  have hceil : a < Nat.ceil L :=
    Nat.lt_ceil.mpr haL
  change a ∈ Finset.Ico (N / (2 * b) + 1) (Nat.ceil L)
  exact Finset.mem_Ico.mpr ⟨by omega, hceil⟩

/-- Divisibility plus the original strict half-window makes the map
P -> (N-P)/b INJECTIVE ON THE PREVIOUS ACTIVE CARRIER.
This neither identifies repeated sixth occurrences nor changes their
List multiplicity; it applies within a fixed fifth/sixth occurrence. -/
theorem active_window_card_le_integer_quotient_gap
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (longPrimeActiveRosserWindow N cap w L X pre p).card ≤
      Nat.ceil L - (N / (2 * (p :: pre).prod) + 1) := by
  classical
  let b := (p :: pre).prod
  let W := longPrimeActiveRosserWindow N cap w L X pre p
  let B := Finset.Ico (N / (2 * b) + 1) (Nat.ceil L)
  let f : ℕ → ℕ := fun P => (N - P) / b
  have hInj : Set.InjOn f W := by
    intro P hP Q hQ heq
    have hPmod : P ∈ longPrimeModulusWindow N X pre p :=
      (Finset.mem_filter.mp hP).1
    have hQmod : Q ∈ longPrimeModulusWindow N X pre p :=
      (Finset.mem_filter.mp hQ).1
    have hPwin : P ∈ longPrimeWindow N X p :=
      (Finset.mem_filter.mp hPmod).1
    have hQwin : Q ∈ longPrimeWindow N X p :=
      (Finset.mem_filter.mp hQmod).1
    have hPle : P ≤ N := by
      have h := (Finset.mem_Ico.mp hPwin).2
      omega
    have hQle : Q ≤ N := by
      have h := (Finset.mem_Ico.mp hQwin).2
      omega
    have hdP : b ∣ N - P := (Finset.mem_filter.mp hPmod).2
    have hdQ : b ∣ N - Q := (Finset.mem_filter.mp hQmod).2
    have heP : (N - P) / b * b = N - P :=
      Nat.div_mul_cancel hdP
    have heQ : (N - Q) / b * b = N - Q :=
      Nat.div_mul_cancel hdQ
    have hsub : N - P = N - Q := by
      calc
        N - P = (N - P) / b * b := heP.symm
        _ = (N - Q) / b * b := congrArg (fun a : ℕ => a * b) heq
        _ = N - Q := heQ
    omega
  have hcard : (W.image f).card = W.card := by
    apply Finset.card_image_of_injOn
    exact hInj
  have hsub : W.image f ⊆ B := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    exact active_window_quotient_in_integer_band
      N cap w L X P pre p hP
  calc
    W.card = (W.image f).card := hcard.symm
    _ ≤ B.card := Finset.card_le_card hsub
    _ = Nat.ceil L - (N / (2 * b) + 1) := by
      simp [B]

/-- Explicit finite envelope for the UNCHANGED original signed prime
fibre. This is an upper envelope for its actual-active-card invoice,
NOT a second independent expense and NOT an H_N estimate. -/
theorem original_long_prime_sum_abs_le_integer_quotient_gap
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |∑ P ∈ chenPrimePrefix N,
        upperPrimeLongBoundaryTerm N cap w L X P pre p| ≤
      ((Nat.ceil L - (N / (2 * (p :: pre).prod) + 1) : ℕ) : ℝ) := by
  calc
    _ ≤ ((longPrimeActiveRosserWindow N cap w L X pre p).card : ℝ) :=
      original_long_prime_sum_abs_le_active_rosser_card
        N cap w L X pre p
    _ ≤ ((Nat.ceil L - (N / (2 * (p :: pre).prod) + 1) : ℕ) : ℝ) := by
      exact_mod_cast active_window_card_le_integer_quotient_gap
        N cap w L X pre p

/-- An INTEGRAL gap eliminates each ORIGINAL long boundary term,
even when the weaker real-size condition 2*L*b<=N is unavailable.
This is a checkable per-occurrence parameter condition, NOT asserted
for every genuine producer. -/
theorem long_fibre_zero_of_integer_quotient_gap
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hgap : Nat.ceil L ≤
      N / (2 * (p :: pre).prod) + 1) :
    upperPrimeLongBoundaryTerm N cap w L X P pre p = 0 := by
  have hcard :
      (longPrimeActiveRosserWindow N cap w L X pre p).card = 0 := by
    have hb := active_window_card_le_integer_quotient_gap
      N cap w L X pre p
    have hzero :
        Nat.ceil L - (N / (2 * (p :: pre).prod) + 1) = 0 :=
      Nat.sub_eq_zero_of_le hgap
    omega
  have hempty :
      longPrimeActiveRosserWindow N cap w L X pre p = ∅ :=
    Finset.card_eq_zero.mp hcard
  by_contra hnon
  have hmem := long_fibre_nonzero_in_active_rosser_window
    N cap w L X P pre p hnon
  simp [hempty] at hmem

/-- One-time exact deletion of the long invoice on the SAME ordered
sixth list, if every original occurrence passes its own integer-gap
test. No deduplication, no change of fifth signed mass, and no extra
prime mask on the source. -/
theorem original_fifth_ordered_long_zero_of_quotient_gaps
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (fifth : FifthStoppedEvent ℕ)
    (hgap : ∀ p ∈ fifth.remainingAfter,
      Nat.ceil L ≤
        N / (2 * (p :: fifth.selectedAfter).prod) + 1) :
    (fifth.remainingAfter.map (fun p =>
      signedTreeCoefficient true fifth.massAfter *
        upperPrimeLongBoundaryTerm N cap w L X P
          fifth.selectedAfter p)).sum = 0 := by
  have hmap :
      fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P
            fifth.selectedAfter p) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    simp [long_fibre_zero_of_integer_quotient_gap
      N cap w L X P fifth.selectedAfter p (hgap p hp)]
  rw [hmap]
  simp

private theorem list_map_sum_le {α : Type*}
    (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : f x ≤ g x := h x (by simp)
      have ht : ∀ y ∈ xs, f y ≤ g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add hx (ih ht)

/-- The SAME original fifth signed mass and ORDERED sixth list now
also have an explicit integer-gap envelope. The actual-active-card
invoice remains the tighter literal bound; do not sum both. -/
theorem original_fifth_ordered_long_integer_gap_budget
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    |∑ P ∈ chenPrimePrefix N,
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeLongBoundaryTerm N cap w L X P
            fifth.selectedAfter p)).sum| ≤
      (fifth.remainingAfter.map (fun p =>
        |signedTreeCoefficient true fifth.massAfter| *
          ((Nat.ceil L -
            (N / (2 * (p :: fifth.selectedAfter).prod) + 1) : ℕ) : ℝ))).sum := by
  calc
    _ ≤ (fifth.remainingAfter.map (fun p =>
          |signedTreeCoefficient true fifth.massAfter| *
            ((longPrimeActiveRosserWindow N cap w L X
              fifth.selectedAfter p).card : ℝ))).sum :=
      original_fifth_ordered_long_prime_active_budget
        N cap w L X fifth
    _ ≤ (fifth.remainingAfter.map (fun p =>
          |signedTreeCoefficient true fifth.massAfter| *
            ((Nat.ceil L -
              (N / (2 * (p :: fifth.selectedAfter).prod) + 1) : ℕ) : ℝ))).sum := by
      apply list_map_sum_le
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast active_window_card_le_integer_quotient_gap
          N cap w L X fifth.selectedAfter p)
        (abs_nonneg _)

end
end ImbalancedChen.P4AOriginalFull87UpperActiveQuotientGap
