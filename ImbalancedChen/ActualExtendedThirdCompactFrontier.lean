import ImbalancedChen.ActualExtendedThirdCompactUpperRho
import ImbalancedChen.ActualExtendedThirdDistinctProductHarmonic

/-!
# The literal compact policy's third-candidate prime carrier

The actual rank-two first-exit frontier supplies the third candidate
before its own cube is tested. On an adopted cell its initial first-prime
admission is proved from the same physical cap. The filtered frontier is
exactly the existing strictly ordered prime-cell carrier, retaining the
original rough enumeration cap and target-prime exclusions.

An arbitrary signed test on the actual original candidates therefore has
the same tuple sum, and then the same product-image sum with weight
1/phi(n). No Cartesian replacement, factorial, first-exit density identity
or arithmetic counting remainder is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Set
open scoped Classical BigOperators

theorem actualExtendedThirdCompactOwnedCell_primeRegion {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdOwnedCell m j) :
    t ∈ actualExtendedThirdCompactCellPrimeRegion m j := by
  have hz : 0 < t 2 := hh.trans_le ((Finset.mem_filter.mp hj).2.trans
    (ht.1 2 (mem_univ _)).1)
  have hxrho : t 0 ≤ thirdPrefixRho :=
    (ht.1 0 (mem_univ _)).2.le.trans (actualExtendedThirdDyadic_bounds m j 0).2.2
  exact ⟨ht, hz, (ht.2.2.1.trans ht.2.2.2).trans hxrho, ht.2.2.1, ht.2.2.2, hxrho⟩

/-- The retained cutoff gives an actual lower prime bound. The original
right cutoff is rho, even though the analytic bounding cube is larger. -/
theorem actualExtendedThirdCompactOwnedCell_log_bounds {e h : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdOwnedCell m j) (i : Fin 3) :
    h ≤ t i ∧ t i < thirdPrefixRho := by
  have hz : h ≤ t 2 := (Finset.mem_filter.mp hj).2.trans (ht.1 2 (mem_univ _)).1
  have hlo : h ≤ t i := by
    fin_cases i
    · exact (hz.trans ht.2.2.1).trans ht.2.2.2
    · exact hz.trans ht.2.2.1
    · exact hz
  exact ⟨hlo, (ht.1 i (mem_univ _)).2.trans_le
    (actualExtendedThirdDyadic_bounds m j i).2.2⟩

theorem actualExtendedThirdCompactHistoryLog (N : ℕ) (p : Fin 3 → ℕ) :
    primeHistoryLogCoordinates (N : ℝ) 3 [p 2, p 1, p 0] = actualPrimeTupleLog N p := by
  funext i
  fin_cases i <;> simp [primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog]

/-- The actual proper prefix has only the first admission. The third
candidate is deliberately not filtered by either old or new own cube. -/
theorem actualExtendedThirdCompactParent_valid_iff (e h : ℝ) (m N : ℕ)
    (p : Fin 3 → ℕ) :
    FirstExitValidSelection (actualExtendedThirdCompactUpperPolicy e h m N)
        [] true (List.ofFn p).dropLast ↔
      actualExtendedThirdCompactInitialPolicy e m N false [p 0] = true := by
  have hdrop : (List.ofFn p).dropLast = [p 0, p 1] := by simp [List.ofFn_succ]
  rw [hdrop]
  change (actualExtendedThirdCompactUpperPolicy e h m N false [p 0] = true ∧
    actualExtendedThirdCompactUpperPolicy e h m N true [p 1, p 0] = true ∧ True) ↔ _
  rw [actualExtendedThirdCompactUpperPolicy_through_two e h m N false [p 0] (by simp),
    actualExtendedThirdCompactUpperPolicy_even]
  simp

/-- The physical cap and its first-stop wall pay the real parent filter.
No caller-supplied prefix-admissibility premise remains on the cell. -/
theorem actualExtendedThirdCompactParent_valid_of_cell {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (p : Fin 3 → ℕ) (hp0 : 0 < p 0) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j) :
    FirstExitValidSelection (actualExtendedThirdCompactUpperPolicy e h m N)
      [] true (List.ofFn p).dropLast := by
  apply (actualExtendedThirdCompactParent_valid_iff e h m N p).mpr
  exact actualExtendedThirdCompactInitialPolicy_first_of_cell hN he0 he hmesh
    (p 0) (p 1) (p 2) hp0 hj (by rw [actualExtendedThirdCompactHistoryLog]; exact ht)

/-- Exact original-cap identification with the already defined strict
prime-cell carrier; the third candidate's own gate is absent on both sides. -/
theorem actualExtendedThirdCompactFrontier_cell_filter {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (w : ℝ)
    (hw : w ≤ (N : ℝ) ^ h) (hcap : (N : ℝ) ^ thirdPrefixRho ≤ (cap : ℝ))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    (firstExitFrontierTuples 2 (actualExtendedThirdCompactUpperPolicy e h m N)
        (roughPrimeUniverse N cap w ((N : ℝ) ^ thirdPrefixRho))).filter
        (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j) =
      actualExtendedThirdDistinctCellPrimeTuples N h m j := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  ext p
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hf, ht⟩
    obtain ⟨hs, hp, _hv⟩ := (mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap
      2 (actualExtendedThirdCompactUpperPolicy e h m N) N cap w _ hcap p).mp hf
    have hregion := actualExtendedThirdCompactOwnedCell_primeRegion hh hj ht
    have hbox : p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h / 2)
        (fun _ => thirdPrefixRho + 1) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hp i).1, (hp i).2.1⟩,
          actualExtendedThirdCompactCellPrimeRegion_subset_cube hh hj hregion⟩
    have hslog := (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hp i).1.pos)).mpr hs
    change p ∈ (actualPrimeBoxTuples N (fun _ : Fin 3 => h / 2)
      (fun _ => thirdPrefixRho + 1)).filter _
    apply Finset.mem_filter.mpr
    refine ⟨hbox, hregion, ?_⟩
    intro i
    fin_cases i
    · change actualPrimeTupleLog N p 1 - actualPrimeTupleLog N p 0 < 0
      linarith only [hslog (by decide : (0 : Fin 3) < 1)]
    · change actualPrimeTupleLog N p 2 - actualPrimeTupleLog N p 1 < 0
      linarith only [hslog (by decide : (1 : Fin 3) < 2)]
  · intro hp
    obtain ⟨hpbox, hpregion⟩ := Finset.mem_filter.mp hp
    have hpi := mem_actualPrimeBoxTuples_iff.mp hpbox
    have ht := hpregion.1.1
    obtain ⟨h10, h21⟩ := actualExtendedThirdDistinctCellPrimeRegion_prime_order hN hpbox hpregion
    have hs : StrictAnti p := by
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      fin_cases i
      · exact h10
      · exact h21
    refine ⟨(mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap
      2 (actualExtendedThirdCompactUpperPolicy e h m N) N cap w _ hcap p).mpr
        ⟨hs, ?_, actualExtendedThirdCompactParent_valid_of_cell hN he0 he hmesh p
          (hpi 0).1.pos hj ht⟩, ht⟩
    intro i
    refine ⟨(hpi i).1, (hpi i).2.1, ?_, ?_⟩
    · rw [← actualPrimeTupleLog_rpow hN p (fun k => (hpi k).1.pos) i]
      exact hw.trans (Real.rpow_le_rpow_of_exponent_le hNr.le
        (actualExtendedThirdCompactOwnedCell_log_bounds hj ht i).1)
    · rw [← actualPrimeTupleLog_rpow hN p (fun k => (hpi k).1.pos) i]
      exact (Real.rpow_lt_rpow_left_iff hNr).mpr
        (actualExtendedThirdCompactOwnedCell_log_bounds hj ht i).2

/-- The real candidate list, with its original signed test left arbitrary. -/
def actualExtendedThirdCompactFrontierCellSum (e h : ℝ) (m N cap : ℕ) (w : ℝ)
    (j : ActualExtendedThirdDyadicLabel m) (G : (Fin 3 → ℕ) → ℝ) : ℝ :=
  ((firstExitFrontierCandidates 2 (actualExtendedThirdCompactUpperPolicy e h m N)
    (fun q : ℕ => 1 / ((q : ℝ) - 1))
    (roughPrimeUniverse N cap w ((N : ℝ) ^ thirdPrefixRho))).map (fun candidate =>
      (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        (if primeHistoryLogCoordinates (N : ℝ) 3 candidate.selectedPrefix ∈
            actualExtendedThirdOwnedCell m j then
          G (primeHistoryTuple 3 candidate.selectedPrefix) else 0))).sum

theorem actualExtendedThirdCompactFrontierCellSum_eq_tuple_sum {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (w : ℝ)
    (hw : w ≤ (N : ℝ) ^ h) (hcap : (N : ℝ) ^ thirdPrefixRho ≤ (cap : ℝ))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (G : (Fin 3 → ℕ) → ℝ) :
    actualExtendedThirdCompactFrontierCellSum e h m N cap w j G =
      ∑ p ∈ actualExtendedThirdDistinctCellPrimeTuples N h m j,
        (∏ i : Fin 3, 1 / ((p i : ℝ) - 1)) * G p := by
  unfold actualExtendedThirdCompactFrontierCellSum
  change ((firstExitFrontierCandidates 2 (actualExtendedThirdCompactUpperPolicy e h m N)
    (fun q : ℕ => 1 / ((q : ℝ) - 1))
    (roughPrimeUniverse N cap w ((N : ℝ) ^ thirdPrefixRho))).map (fun candidate =>
      (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        (if actualPrimeTupleLog N (primeHistoryTuple 3 candidate.selectedPrefix) ∈
            actualExtendedThirdOwnedCell m j then
          G (primeHistoryTuple 3 candidate.selectedPrefix) else 0))).sum = _
  rw [firstExitFrontierCandidates_weighted_sum_eq_tuple_sum 2
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun q : ℕ => 1 / ((q : ℝ) - 1))
    _ (roughPrimeUniverse_nodup N cap w ((N : ℝ) ^ thirdPrefixRho))]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter,
    actualExtendedThirdCompactFrontier_cell_filter hN hh he0 he hmesh w hw hcap hj]

/-- The same original candidates, same signed test, and original product
image carry exactly one reciprocal totient weight. -/
theorem actualExtendedThirdCompactFrontierCellSum_eq_product_sum {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (w : ℝ)
    (hw : w ≤ (N : ℝ) ^ h) (hcap : (N : ℝ) ^ thirdPrefixRho ≤ (cap : ℝ))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (G : (Fin 3 → ℕ) → ℝ) :
    actualExtendedThirdCompactFrontierCellSum e h m N cap w j G =
      ∑ n ∈ actualExtendedThirdDistinctCellPrimeProducts N h m j,
        1 / (Nat.totient n : ℝ) * G (actualExtendedThirdDistinctCellProductTuple N h m j n) := by
  rw [actualExtendedThirdCompactFrontierCellSum_eq_tuple_sum hN hh he0 he hmesh w hw hcap hj]
  exact actualExtendedThirdDistinctCellPrimeTuples_totient_sum hN h m j G

end

end ImbalancedChen
