import ImbalancedChen.FirstExitCandidateGeometry
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Exact logarithmic coordinates of a selected prime history

The tree stores selected primes in reverse processing order. The total
tuple below reads the reversed list, using zero only outside the list.
When the recorded length is correct, no default is read: the tuple is
exactly the original processing order, with its actual product and mass.
Positive entries are recovered exactly from their logarithmic coordinates.

The actual frontier and next-selection corollaries derive primality and
order from the real prime carrier. Next selections are not required to
pass either an old or a new admission test. No box selector, asymptotic
estimate, or receiver-dependent coefficient is introduced here.
-/

namespace ImbalancedChen

open scoped BigOperators

theorem primeHistoryTuple_mem {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (i : Fin k) :
    primeHistoryTuple k history i ∈ history := by
  apply List.mem_reverse.mp
  rw [← primeHistoryTuple_ofFn hlen]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem primeHistoryTuple_prime {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (hprime : ∀ p ∈ history, Nat.Prime p) (i : Fin k) :
    Nat.Prime (primeHistoryTuple k history i) :=
  hprime _ (primeHistoryTuple_mem hlen i)

theorem primeHistoryTuple_pos {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (hpos : ∀ p ∈ history, 0 < p) (i : Fin k) :
    0 < primeHistoryTuple k history i :=
  hpos _ (primeHistoryTuple_mem hlen i)

/-- The general index identity states explicitly which reverse-history
entry is used. -/
theorem primeHistoryTuple_eq_getD {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (i : Fin k) :
    primeHistoryTuple k history i = history.getD (k - 1 - i.val) 0 := by
  unfold primeHistoryTuple
  rw [List.getD_reverse i.val (by simp [hlen]), hlen]

/-- The last processing coordinate is the last selected prime, namely the
head of the reverse-stored history. -/
theorem primeHistoryTuple_last {k : ℕ} {history : List ℕ}
    (hlen : history.length = k + 1) :
    primeHistoryTuple (k + 1) history (Fin.last k) = history.headD 0 := by
  rw [primeHistoryTuple_eq_getD hlen]
  cases history <;> simp

/-- Reversal and finite-function indexing preserve the entire product. -/
theorem primeHistoryTuple_prod {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) :
    (∏ i, primeHistoryTuple k history i) = history.prod := by
  rw [← List.prod_ofFn, primeHistoryTuple_ofFn hlen, List.prod_reverse]

/-- A positive selected integer is recovered exactly, not rounded, from
its coordinate at a base greater than one. -/
theorem rpow_primeHistoryLogCoordinates {k : ℕ} {history : List ℕ}
    (N : ℝ) (hN : 1 < N) (hlen : history.length = k)
    (hpos : ∀ p ∈ history, 0 < p) (i : Fin k) :
    N ^ primeHistoryLogCoordinates N k history i = (primeHistoryTuple k history i : ℝ) := by
  have hp : (0 : ℝ) < primeHistoryTuple k history i := by
    exact_mod_cast primeHistoryTuple_pos hlen hpos i
  unfold primeHistoryLogCoordinates
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hN),
    mul_div_cancel₀ _ (Real.log_pos hN).ne', Real.exp_log hp]

/-- Prime entries have strictly positive logarithmic coordinates. Mere
positivity of an integer would only imply nonnegative coordinates. -/
theorem primeHistoryLogCoordinates_pos {k : ℕ} {history : List ℕ}
    (N : ℝ) (hN : 1 < N) (hlen : history.length = k)
    (hprime : ∀ p ∈ history, Nat.Prime p) (i : Fin k) :
    0 < primeHistoryLogCoordinates N k history i := by
  have hp : (1 : ℝ) < primeHistoryTuple k history i := by
    exact_mod_cast (primeHistoryTuple_prime hlen hprime i).one_lt
  exact div_pos (Real.log_pos hp) (Real.log_pos hN)

/-- The sum of all coordinates is the exact exponent of the selected
product, including the empty history. -/
theorem rpow_sum_primeHistoryLogCoordinates {k : ℕ} {history : List ℕ}
    (N : ℝ) (hN : 1 < N) (hlen : history.length = k)
    (hpos : ∀ p ∈ history, 0 < p) :
    N ^ (∑ i, primeHistoryLogCoordinates N k history i) = (history.prod : ℝ) := by
  rw [Real.rpow_sum_of_pos (zero_lt_one.trans hN)]
  simp_rw [rpow_primeHistoryLogCoordinates N hN hlen hpos]
  rw [← Nat.cast_prod, primeHistoryTuple_prod hlen]

theorem sum_primeHistoryLogCoordinates {k : ℕ} {history : List ℕ}
    (N : ℝ) (hN : 1 < N) (hlen : history.length = k)
    (hpos : ∀ p ∈ history, 0 < p) :
    (∑ i, primeHistoryLogCoordinates N k history i) =
      Real.log (history.prod : ℝ) / Real.log N := by
  have heq := congrArg Real.log (rpow_sum_primeHistoryLogCoordinates N hN hlen hpos)
  rw [Real.log_rpow (zero_lt_one.trans hN)] at heq
  apply (eq_div_iff (Real.log_pos hN).ne').mpr
  simpa only [mul_comm] using heq

/-- Increasing reverse histories become strictly decreasing processing
tuples; no new ordering hypothesis is attached to the tuple itself. -/
theorem primeHistoryTuple_strictAnti {k : ℕ} {history : List ℕ}
    (hlen : history.length = k) (hsort : history.Pairwise (· < ·)) :
    StrictAnti (primeHistoryTuple k history) := by
  have hr : history.reverse.Pairwise (· > ·) := by
    simpa only [List.pairwise_reverse] using hsort
  rw [← primeHistoryTuple_ofFn hlen] at hr
  exact List.pairwise_ofFn.mp hr

theorem primeHistoryLogCoordinates_strictAnti {k : ℕ} {history : List ℕ}
    (N : ℝ) (hN : 1 < N) (hlen : history.length = k)
    (hpos : ∀ p ∈ history, 0 < p) (hsort : history.Pairwise (· < ·)) :
    StrictAnti (primeHistoryLogCoordinates N k history) := by
  intro i j hij
  apply (div_lt_div_iff_of_pos_right (Real.log_pos hN)).mpr
  apply Real.log_lt_log
  · exact_mod_cast primeHistoryTuple_pos hlen hpos j
  · exact_mod_cast primeHistoryTuple_strictAnti hlen hsort hij

/-- Actual root-frontier coordinates refer to the same capped carrier,
including its target-prime exclusions. Rank zero is allowed. -/
theorem primeHistoryTuple_frontier_mem
    (k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1
      (roughPrimeUniverse N cap w z)) (i : Fin k) :
    primeHistoryTuple k state.selectedPrefix i ∈ roughPrimeUniverse N cap w z := by
  have hlen := firstExitDepthFrontier_selected_length k parent h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k parent h
    (roughPrimeUniverse N cap w z) state hstate
  exact hsub.subset (List.mem_reverse.mpr (primeHistoryTuple_mem hlen i))

/-- No entry default or order is postulated for a real prime frontier. -/
theorem primeHistoryLogCoordinates_frontier
    (k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1
      (roughPrimeUniverse N cap w z)) :
    StrictAnti (primeHistoryLogCoordinates (N : ℝ) k state.selectedPrefix) ∧
      ∀ i : Fin k, 0 < primeHistoryLogCoordinates (N : ℝ) k state.selectedPrefix i ∧
        (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) k state.selectedPrefix i =
          (primeHistoryTuple k state.selectedPrefix i : ℝ) := by
  have hlen := firstExitDepthFrontier_selected_length k parent h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k parent h
    (roughPrimeUniverse N cap w z) state hstate
  have hprime : ∀ p ∈ state.selectedPrefix, Nat.Prime p := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hpos : ∀ p ∈ state.selectedPrefix, 0 < p := fun p hp => (hprime p hp).pos
  have hsort : state.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  exact ⟨primeHistoryLogCoordinates_strictAnti N hN hlen hpos hsort,
    fun i => ⟨primeHistoryLogCoordinates_pos N hN hlen hprime i,
      rpow_primeHistoryLogCoordinates N hN hlen hpos i⟩⟩

/-- The logarithmic geometry also holds for every next candidate,
including the branches rejected by the old own-cube test. -/
theorem primeHistoryLogCoordinates_candidate
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (hN : 1 < (N : ℝ))
    (z : ℝ) (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    StrictAnti (primeHistoryLogCoordinates (N : ℝ) (k + 1) candidate.selectedPrefix) ∧
      ∀ i : Fin (k + 1),
        0 < primeHistoryLogCoordinates (N : ℝ) (k + 1) candidate.selectedPrefix i ∧
        (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) (k + 1) candidate.selectedPrefix i =
          (primeHistoryTuple (k + 1) candidate.selectedPrefix i : ℝ) := by
  obtain ⟨hlen, hsort, _hP, _hcut, _hremaining, _hsign, _hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry k parent N cap z frontier hfrontier candidate hcandidate
  have hpos : ∀ p ∈ candidate.selectedPrefix, 0 < p := fun p hp => (hprime p hp).pos
  exact ⟨primeHistoryLogCoordinates_strictAnti N hN hlen hpos hsort,
    fun i => ⟨primeHistoryLogCoordinates_pos N hN hlen hprime i,
      rpow_primeHistoryLogCoordinates N hN hlen hpos i⟩⟩

end ImbalancedChen
