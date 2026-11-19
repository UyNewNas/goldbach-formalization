import ImbalancedChen.P4AOriginalFull87FrozenSurvivorInvoice
import ImbalancedChen.P4AOriginalFull87FifthHistoryCeilingPrune
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A missing FULL-upper arithmetic invoice, not the already handled LONG
boundary. For the original quotient a=(N-P)/b, b=(p::pre).prod,
nonzero requires the SAME exact multiplication a*b=N-P and
  2*P<N, X<N-P, a<L.
Thus the integral quotient belongs to the genuinely TWO-SIDED interval

  max(floor(N/(2*b))+1, floor(X/b)+1) <= a
    < min(ceil L, floor(N/b)+1).

This supplies a strict FULL upper-fibre zero test and a finite counting
bound, including the missing X and q<=N restrictions. The prime carrier
is used only to prove the bound, not to modify any source or policy.
The fifth signed list remains ordered, with complete modulus and every
sixth occurrence intact. No H_N estimate or PP admission is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87FullUpperQuotientRoom
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87StoppedGlobalPrimeLedger
  (upperPrimeFibreTerm upperPrimeFibreEventValue)
open P4AOriginalFull87FifthHistoryCeilingPrune
  (original_upper_fibre_nonzero_power_and_level)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent)

/-- A numerical OUTER interval for the ORIGINAL full upper coefficient.
b=0 is harmless: then the original strict X<a*b gate is impossible. -/
def fullUpperQuotientRoom (N X : ℕ) (L : ℝ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  let b := (p :: pre).prod
  Finset.Ico ((N / (2 * b) + 1).max (X / b + 1))
    ((Nat.ceil L).min (N / b + 1))

private theorem original_full_upper_nonzero_gate
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    2 * P < N ∧ X < N - P ∧
      (N - P) / (p :: pre).prod ∈
        P4AOriginalFull87PlusBetaPowerFilter.largeFifthRosserIndices
          N cap w X pre ∧
      ((N - P) / (p :: pre).prod) *
        (p :: pre).prod = N - P := by
  unfold upperPrimeFibreTerm at hnon
  split_ifs at hnon with hgate
  · exact hgate
  · contradiction

/-- FULL upper, not LONG: the *original* prime support forces all
four strict/weak integer endpoints simultaneously. The extra X/b
floor and q<=N ceiling are not present in the old long-boundary gap. -/
theorem original_full_upper_nonzero_in_quotient_room
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hnon : upperPrimeFibreTerm N cap w L X P pre p ≠ 0) :
    (N - P) / (p :: pre).prod ∈
      fullUpperQuotientRoom N X L pre p := by
  let b : ℕ := (p :: pre).prod
  let a : ℕ := (N - P) / b
  have hg := original_full_upper_nonzero_gate
    N cap w L X P pre p hnon
  have hhalf : 2 * P < N := hg.1
  have hX : X < N - P := hg.2.1
  have hab : a * b = N - P := hg.2.2.2
  have hbpos : 0 < b := by
    by_contra hn
    have hbzero : b = 0 := Nat.eq_zero_of_not_pos hn
    have hqzero : 0 = N - P := by simpa [hbzero] using hab
    omega
  have hNlt : N < a * (2 * b) := by
    calc
      N < 2 * (a * b) := by omega
      _ = a * (2 * b) := by ring
  have hXlt : X < a * b := by omega
  have hqle : a * b ≤ N := by omega
  have hloN : N / (2 * b) + 1 ≤ a := by
    have hv : N / (2 * b) < a :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * b)).2 hNlt
    omega
  have hloX : X / b + 1 ≤ a := by
    have hv : X / b < a :=
      (Nat.div_lt_iff_lt_mul hbpos).2 hXlt
    omega
  have hhiN : a < N / b + 1 := by
    have hv : a ≤ N / b := (Nat.le_div_iff_mul_le hbpos).2 hqle
    omega
  have haL : (a : ℝ) < L := by
    simpa only [a, b] using
      (original_upper_fibre_nonzero_power_and_level
        N cap w L X P pre p hnon).2
  have hhiL : a < Nat.ceil L := Nat.lt_ceil.mpr haL
  change a ∈ Finset.Ico
    ((N / (2 * b) + 1).max (X / b + 1))
    ((Nat.ceil L).min (N / b + 1))
  exact Finset.mem_Ico.mpr
    ⟨max_le hloN hloX, lt_min hhiL hhiN⟩

/-- A genuinely two-sided empty quotient interval kills the ORIGINAL
full upper prime term. It is not an added filter or a payment. -/
theorem original_full_upper_zero_of_empty_room
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hempty : (Nat.ceil L).min
        (N / (p :: pre).prod + 1) ≤
      (N / (2 * (p :: pre).prod) + 1).max
        (X / (p :: pre).prod + 1)) :
    upperPrimeFibreTerm N cap w L X P pre p = 0 := by
  by_contra hn
  have hm := original_full_upper_nonzero_in_quotient_room
    N cap w L X P pre p hn
  exact (not_lt_of_ge hempty) (Finset.mem_Ico.mp hm).2

/-- The counting source is a SUBSET of the original prime prefix and
uses the original coefficient's actual nonzero predicate. No equality
of different sieve bounds or distribution theorem is assumed. -/
def originalFullUpperNonzeroPrimeCarrier
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) : Finset ℕ :=
  (chenPrimePrefix N).filter
    (fun P => upperPrimeFibreTerm N cap w L X P pre p ≠ 0)

/-- For fixed original fifth history and sixth occurrence, the map
P -> (N-P)/b is injective on the literal nonzero prime carrier.
The upper bound is now the TWO-SIDED quotient room, not the whole
integer prime interval and not the one-sided long boundary. -/
theorem original_full_upper_nonzero_prime_card_le_room
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (originalFullUpperNonzeroPrimeCarrier
        N cap w L X pre p).card ≤
      (fullUpperQuotientRoom N X L pre p).card := by
  classical
  let b : ℕ := (p :: pre).prod
  let W : Finset ℕ :=
    originalFullUpperNonzeroPrimeCarrier N cap w L X pre p
  let f : ℕ → ℕ := fun P => (N - P) / b
  have hinj : Set.InjOn f W := by
    intro P hP Q hQ heq
    have hp : upperPrimeFibreTerm N cap w L X P pre p ≠ 0 :=
      (Finset.mem_filter.mp hP).2
    have hq : upperPrimeFibreTerm N cap w L X Q pre p ≠ 0 :=
      (Finset.mem_filter.mp hQ).2
    have hpG := original_full_upper_nonzero_gate
      N cap w L X P pre p hp
    have hqG := original_full_upper_nonzero_gate
      N cap w L X Q pre p hq
    have hPmul : f P * b = N - P := hpG.2.2.2
    have hQmul : f Q * b = N - Q := hqG.2.2.2
    have hsame : N - P = N - Q := by
      calc
        N - P = f P * b := hPmul.symm
        _ = f Q * b := congrArg (fun x : ℕ => x * b) heq
        _ = N - Q := hQmul
    omega
  have hsubset : W.image f ⊆
      fullUpperQuotientRoom N X L pre p := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp ha
    exact original_full_upper_nonzero_in_quotient_room
      N cap w L X P pre p (Finset.mem_filter.mp hP).2
  have hcard : (W.image f).card = W.card := by
    apply Finset.card_image_of_injOn
    exact hinj
  calc
    W.card = (W.image f).card := hcard.symm
    _ ≤ (fullUpperQuotientRoom N X L pre p).card :=
      Finset.card_le_card hsubset

/-- This is a bound on the pinned PLUS Rosser weight, not on an
arbitrary surrogate beta or an independent prime sieve coefficient. -/
theorem original_full_upper_prime_fibre_abs_le_one
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ) :
    |upperPrimeFibreTerm N cap w L X P pre p| ≤ 1 := by
  unfold upperPrimeFibreTerm
  split_ifs with hg
  · exact actualSmallRosserPlus_abs_le_one
      N cap w L ((N - P) / (p :: pre).prod)
  · simp

/-- Exact finite prime absolute sum, controlled by the bounded quotient
carrier. This also controls SHORT terms (not only old LONG terms).
The original prime prefix, original Rosser quotient, centre correction,
strict X and strict half-boundary are all preserved. -/
theorem original_full_upper_prime_abs_sum_le_room
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    (∑ P ∈ chenPrimePrefix N,
      |upperPrimeFibreTerm N cap w L X P pre p|) ≤
      (((fullUpperQuotientRoom N X L pre p).card : ℕ) : ℝ) := by
  classical
  let W := originalFullUpperNonzeroPrimeCarrier
    N cap w L X pre p
  have hsupport :
      (∑ P ∈ chenPrimePrefix N,
        |upperPrimeFibreTerm N cap w L X P pre p|) =
      ∑ P ∈ W,
        |upperPrimeFibreTerm N cap w L X P pre p| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hpW : P ∈ W
    · simp [hpW]
    · have hz : upperPrimeFibreTerm N cap w L X P pre p = 0 := by
        by_contra hn
        exact hpW (Finset.mem_filter.mpr ⟨hP, hn⟩)
      simp [hpW, hz]
  rw [hsupport]
  calc
    _ ≤ ∑ P ∈ W, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact original_full_upper_prime_fibre_abs_le_one
        N cap w L X P pre p
    _ = (W.card : ℝ) := by simp
    _ ≤ ((fullUpperQuotientRoom N X L pre p).card : ℝ) := by
      exact_mod_cast original_full_upper_nonzero_prime_card_le_room
        N cap w L X pre p

/-- On the ORIGINAL fifth-stopped signed List, an empty quotient room
for every sixth occurrence annihilates its entire upper-prime value.
This is not a false claim about ALL actual producer occurrences. -/
theorem original_fifth_upper_event_zero_of_empty_rooms
    (N cap : ℕ) (w L : ℝ) (X P : ℕ)
    (fifth : FifthStoppedEvent ℕ)
    (hroom : ∀ p ∈ fifth.remainingAfter,
      (Nat.ceil L).min
          (N / (p :: fifth.selectedAfter).prod + 1) ≤
        (N / (2 * (p :: fifth.selectedAfter).prod) + 1).max
          (X / (p :: fifth.selectedAfter).prod + 1)) :
    upperPrimeFibreEventValue N cap w L X P
      (.fifthExclusive fifth) = 0 := by
  have hzero : ∀ p ∈ fifth.remainingAfter,
      upperPrimeFibreTerm N cap w L X P fifth.selectedAfter p = 0 := by
    intro p hp
    exact original_full_upper_zero_of_empty_room
      N cap w L X P fifth.selectedAfter p (hroom p hp)
  have hm :
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          upperPrimeFibreTerm N cap w L X P
            fifth.selectedAfter p)).sum = 0 := by
    have heq :
        fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            upperPrimeFibreTerm N cap w L X P
              fifth.selectedAfter p) =
        fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
      apply List.map_congr_left
      intro p hp
      simp [hzero p hp]
    rw [heq]
    simp
  cases hk : fifth.kind with
  | rawOnly => simpa [upperPrimeFibreEventValue, hk] using hm
  | both => simp [upperPrimeFibreEventValue, hk]
  | licensedOnly => simp [upperPrimeFibreEventValue, hk, hm]

end
end ImbalancedChen.P4AOriginalFull87FullUpperQuotientRoom
