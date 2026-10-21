import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.ActualExtendedThirdCompactUpperRho

/-!
# The same compact policy's admitted third frontier

The depth-three frontier has tested the third prime itself. It is exactly
the original depth-two next-candidate tuple set filtered by that last
policy decision. On an adopted compact cell this last decision is the
strict original third own-cube inequality.

The finite weighted sum keeps the original rough carrier, cap, target
prime deletion and all three reciprocal-totient prime weights. No signed
density limit, numerical coefficient or progression estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Set
open scoped Classical BigOperators

/-- Testing the third candidate completes precisely the same selected
history; the first two policy decisions are retained on both sides. -/
theorem firstExitAdmittedTuples_three_eq_candidate_filter
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ) :
    firstExitAdmittedTuples 3 retained carrier =
      (firstExitFrontierTuples 2 retained carrier).filter
        (fun p => retained false [p 2, p 1, p 0] = true) := by
  ext p
  rw [mem_firstExitAdmittedTuples_iff, Finset.mem_filter,
    mem_firstExitFrontierTuples_iff]
  have hp : List.ofFn p = [p 0, p 1, p 2] := by
    simp [List.ofFn_succ]
  simp [FirstExitValidSelection, and_assoc]

/-- The same actual admitted frontier on an owned cell uses exactly the
strict physical third own cube. Neither inherited admission nor the
original rough enumeration and target-prime gates are discarded. -/
theorem actualExtendedThirdCompactAdmitted_cell_filter
    {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (w z : ℝ)
    {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    (firstExitAdmittedTuples 3 (actualExtendedThirdCompactUpperPolicy e h m N)
        (roughPrimeUniverse N cap w z)).filter
        (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j) =
      (firstExitFrontierTuples 2 (actualExtendedThirdCompactUpperPolicy e h m N)
        (roughPrimeUniverse N cap w z)).filter
        (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j ∧
          (p 0 : ℝ) * p 1 * p 2 ^ 3 <
            (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j) := by
  have hgate (p : Fin 3 → ℕ)
      (hp : p ∈ firstExitFrontierTuples 2
        (actualExtendedThirdCompactUpperPolicy e h m N)
        (roughPrimeUniverse N cap w z))
      (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j) :
      actualExtendedThirdCompactUpperPolicy e h m N false [p 2, p 1, p 0] = true ↔
        (p 0 : ℝ) * p 1 * p 2 ^ 3 <
          (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j := by
    obtain ⟨hanti, hprime, _hparent⟩ :=
      (mem_actualPrimeFrontierTuples_iff 2
        (actualExtendedThirdCompactUpperPolicy e h m N) N cap w z p).mp hp
    have hlog : primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0] =
        actualPrimeTupleLog N p := by
      funext i
      fin_cases i <;>
        simp [primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog]
    exact actualExtendedThirdCompactUpperPolicy_third_iff hN he0 he hmesh
      (p 0) (p 1) (p 2) (hprime 2).2.1.pos
      (hanti (by decide : (1 : Fin 3) < 2))
      (hanti (by decide : (0 : Fin 3) < 1)) hj (by rw [hlog]; exact ht)
  rw [firstExitAdmittedTuples_three_eq_candidate_filter]
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, hown⟩, ht⟩
    exact ⟨hp, ht, (hgate p hp ht).mp hown⟩
  · rintro ⟨hp, ht, hown⟩
    exact ⟨⟨hp, (hgate p hp ht).mpr hown⟩, ht⟩

/-- An arbitrary signed test on the genuine depth-three frontier is the
same strict-own-cube filtered prime tuple sum, with every original
reciprocal-totient prime weight counted once. -/
theorem actualExtendedThirdCompactAdmittedCell_weighted_sum
    {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (w z : ℝ)
    {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (G : (Fin 3 → ℕ) → ℝ) :
    ((firstExitDepthFrontier 3 (actualExtendedThirdCompactUpperPolicy e h m N)
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap w z)).map (fun state =>
        (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
          (if primeHistoryLogCoordinates (N : ℝ) 3 state.selectedPrefix ∈
              actualExtendedThirdOwnedCell m j then
            G (primeHistoryTuple 3 state.selectedPrefix) else 0))).sum =
      ∑ p ∈ (firstExitFrontierTuples 2 (actualExtendedThirdCompactUpperPolicy e h m N)
          (roughPrimeUniverse N cap w z)).filter
          (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j ∧
            (p 0 : ℝ) * p 1 * p 2 ^ 3 <
              (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j),
        (∏ i : Fin 3, 1 / ((p i : ℝ) - 1)) * G p := by
  change ((firstExitDepthFrontier 3 (actualExtendedThirdCompactUpperPolicy e h m N)
    (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap w z)).map (fun state =>
      (state.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        (if actualPrimeTupleLog N (primeHistoryTuple 3 state.selectedPrefix) ∈
            actualExtendedThirdOwnedCell m j then
          G (primeHistoryTuple 3 state.selectedPrefix) else 0))).sum = _
  rw [firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 3
    (actualExtendedThirdCompactUpperPolicy e h m N)
    (fun q : ℕ => 1 / ((q : ℝ) - 1)) _ (roughPrimeUniverse_nodup N cap w z)
      (fun p : Fin 3 → ℕ =>
        if actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j then G p else 0)]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter,
    actualExtendedThirdCompactAdmitted_cell_filter hN he0 he hmesh w z hj]

end

end ImbalancedChen
