import ImbalancedChen.P4AOriginalFull87OddCeilingEightWord
import ImbalancedChen.P4AOriginalFull87HistoricalCapMargin
import ImbalancedChen.P4AOriginalFull87AllOwnedRealizedHistory
import ImbalancedChen.PrimeHistoryLogCoordinates
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: transport the FOUR ORIGINAL odd historical exponent gates to the
physical processing-order prime tuple, without assuming a gate-product
identity or changing the actual eighth selectedPrefix.

For the source's history(j), with j = 0,1,2,3, the physical word is
(product of the first (2*j+1) ACTUAL processing primes) times the square
of the last of those primes. The extra copy is essential: these are the
inherited Rosser 3*t gates, not the weaker ordinary full-prefix 2*t gates.

The final theorem uses genuine full87 owned-state membership, the
original finiteCap and strictly positive mesh width, not an abstract
postulated result. Still missing is the exact identification of this
tuple-filtered product with the four literal LIST suffix products in
the previous eight-word J packet. No J < finiteCap assertion, saved
archive statement, asymptotics or reserve payment is made here.
-/

namespace ImbalancedChen.P4AOriginalFull87FourHistoryPhysicalTuple
noncomputable section

open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87AllOwnedRealizedHistory
  (owned_eighth_history_primes_and_deletion)
open P4AOriginalFull87HistoricalCapMargin
  (owned_four_original_history_power_below_actual_cap)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)

/-- The original named 3*t0, t0+t1+3*t2, ... history gates are
EXACTLY a processing-order prefix plus two copies of its final
coordinate. This is a finite 4-case algebraic calculation, not an
extra assumption about source membership or Rosser success. -/
private theorem original_four_history_as_prefix_sum
    (t : Fin 8 → ℝ) (j : Fin 4) :
    P4AOriginalRemainingEighthSources.history t j =
      (∑ i ∈ Finset.univ.filter
        (fun i : Fin 8 => i.val ≤ 2 * j.val), t i) +
      t ⟨2 * j.val, by omega⟩ + t ⟨2 * j.val, by omega⟩ := by
  fin_cases j <;>
    norm_num [P4AOriginalRemainingEighthSources.history,
      Finset.sum_filter, Fin.sum_univ_succ] <;>
    ring

/-- On ANY finite subset of actual history positions, the physical
prime product is the corresponding base-N exponential. The statement
uses the original inverse logarithmic coordinate theorem, applied
entrywise; no independent prime-coordinate dictionary is supplied. -/
private theorem rpow_actual_history_subset
    (N : ℝ) (hN : 1 < N) (H : List ℕ)
    (hlen : H.length = 8) (hpos : ∀ p ∈ H, 0 < p)
    (S : Finset (Fin 8)) :
    N ^ (∑ i ∈ S, primeHistoryLogCoordinates N 8 H i) =
      ∏ i ∈ S, (primeHistoryTuple 8 H i : ℝ) := by
  rw [Real.rpow_sum_of_pos (zero_lt_one.trans hN)]
  apply Finset.prod_congr rfl
  intro i hi
  exact rpow_primeHistoryLogCoordinates N hN hlen hpos i

/-- Physical transport for EACH of the four ORIGINAL inherited
odd-square tests, on the ACTUAL processing tuple of the SAME list H.
The prefix remains a finite index filter; it is not a setification
of the tree's selectedPrime occurrence sequence. -/
theorem rpow_original_four_history_actual_tuple
    (N : ℝ) (hN : 1 < N) (H : List ℕ)
    (hlen : H.length = 8) (hpos : ∀ p ∈ H, 0 < p)
    (j : Fin 4) :
    N ^ (P4AOriginalRemainingEighthSources.history
      (primeHistoryLogCoordinates N 8 H) j) =
    (∏ i ∈ Finset.univ.filter
      (fun i : Fin 8 => i.val ≤ 2 * j.val),
      (primeHistoryTuple 8 H i : ℝ)) *
    (primeHistoryTuple 8 H ⟨2 * j.val, by omega⟩ : ℝ) ^ 2 := by
  let t := primeHistoryLogCoordinates N 8 H
  let k : Fin 8 := ⟨2 * j.val, by omega⟩
  let S : Finset (Fin 8) :=
    Finset.univ.filter (fun i : Fin 8 => i.val ≤ 2 * j.val)
  have hhist :
      P4AOriginalRemainingEighthSources.history t j =
        (∑ i ∈ S, t i) + t k + t k := by
    simpa only [S, k] using original_four_history_as_prefix_sum t j
  have hsum : N ^ (∑ i ∈ S, t i) =
      ∏ i ∈ S, (primeHistoryTuple 8 H i : ℝ) := by
    simpa only [t] using rpow_actual_history_subset N hN H hlen hpos S
  have hentry : N ^ t k = (primeHistoryTuple 8 H k : ℝ) := by
    exact rpow_primeHistoryLogCoordinates N hN hlen hpos k
  calc
    N ^ (P4AOriginalRemainingEighthSources.history t j) =
        N ^ ((∑ i ∈ S, t i) + t k + t k) := by rw [hhist]
    _ = (N ^ (∑ i ∈ S, t i)) * (N ^ t k) * (N ^ t k) := by
      rw [Real.rpow_add (zero_lt_one.trans hN)]
      rw [Real.rpow_add (zero_lt_one.trans hN)]
    _ = (∏ i ∈ S, (primeHistoryTuple 8 H i : ℝ)) *
        (primeHistoryTuple 8 H k : ℝ) ^ 2 := by
      rw [hsum, hentry]
      ring

/-- ORIGINAL FULL87 physical four-gate conclusion. The history is the
actual state.selectedPrefix, known to have length eight and target-
deleted prime entries by its ORIGINAL owner/trim frontier producer.
In particular the caller does not supply a synthetic p-tuple, a gate
equality or a Rosser historical-square licence.

The original +width(r)/2 strict margin yields the gate inequality
at the unchanged finiteCap branch; no second rounding is charged. -/
theorem owned_four_physical_tuple_gates_below_actual_cap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hn : 4 * width n < width r)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    ∀ j : Fin 4,
      (∏ i ∈ Finset.univ.filter
        (fun i : Fin 8 => i.val ≤ 2 * j.val),
        (primeHistoryTuple 8 s.selectedPrefix i : ℝ)) *
      (primeHistoryTuple 8 s.selectedPrefix
        ⟨2 * j.val, by omega⟩ : ℝ) ^ 2 <
      actualFrozenPost8Level n e q om N c s false := by
  have hlen : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      (width r) n e q om N cap w z c s hs).1
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (owned_eighth_history_primes_and_deletion
      r n e q om N cap w z c s hs p hp).1.pos
  intro j
  let t := primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix
  have hpositive : 0 < width r := width_pos r
  have hmargin :
      P4AOriginalRemainingEighthSources.history t j <
      P4AOriginalRemainingEighthSources.history t j + width r / 2 := by
    linarith
  have hsmall := Real.rpow_lt_rpow_of_exponent_lt hN hmargin
  have hcap := owned_four_original_history_power_below_actual_cap
    r n e q om N cap hN w z c s hn hs j
  have hbound :
      (N : ℝ) ^ (P4AOriginalRemainingEighthSources.history t j) <
        actualFrozenPost8Level n e q om N c s false :=
    hsmall.trans hcap
  rw [rpow_original_four_history_actual_tuple
    (N : ℝ) hN s.selectedPrefix hlen hpos j] at hbound
  exact hbound

end
end ImbalancedChen.P4AOriginalFull87FourHistoryPhysicalTuple
